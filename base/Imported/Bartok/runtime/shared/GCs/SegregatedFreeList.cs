//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs {

    using Microsoft.Bartok.Options;
    using Microsoft.Bartok.Runtime;

    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

#if SINGULARITY
    using Microsoft.Singularity;
#endif

    /// <summary>
    /// This class supports Allocate/Free operations using memory obtained
    /// from the PageManager.
    ///
    /// Objects that are small enough that multiple instances of them can fit
    /// on a page are allocated from pages of identically sized memory cells.
    ///
    /// Large objects are allocated on separate pages.
    ///
    /// This class is designed to be thread safe on both allocation and free
    /// operations. At this stage it is required that RecycleGlobalPages is
    /// called periodically to reconsider previously full pages for inclusion
    /// in allocation lists.
    ///
    /// The free operation is currently more expensive than required due to
    /// space accounting.
    ///
    /// This class also keeps up to date memory accounting information. Note
    /// that modifications to this data is not synchronized so it is possible
    /// that the counts drift from actual figures over time.
    /// </summary>
    internal unsafe struct SegregatedFreeList /* : Allocator */
    {

        #region Mixins

        [MixinConditional("SegregatedFreeList")]
        [MixinConditional("AllThreadMixins")]
        [Mixin(typeof(Thread))]
        // Should be private, but mixin implementation will warn if visibility
        // does not match that of Thread.
        public sealed class SegregatedFreeListThread : Object {
            // Thread-specific segregated free-list allocator
            [RequiredByBartok]
            internal SegregatedFreeList segregatedFreeList;
        }

        [Inline]
        private static SegregatedFreeListThread MixinThread(Thread t)
        {
            return (SegregatedFreeListThread) (Object) t;
        }

        #endregion

        #region Global (Safe from the context of any thread)

        #region Constants

        /// <summary>
        /// Pages that are the process of being initialized, either as
        /// a page of small chunks or for a large object.
        /// </summary>
        internal const PageType INIT_PAGE = PageType.Owner1;

        /// <summary>
        /// PageType for pages containing small objects.
        /// </summary>
        internal const PageType SMALL_OBJ_PAGE = PageType.Owner2;

        /// <summary>
        /// For any large object, the first page is marked
        /// LARGE_OBJ_START, and subsequent pages marked
        /// LARGE_OBJ_TAIL.
        /// </summary>
        internal const PageType LARGE_OBJ_START = PageType.Owner3;
        internal const PageType LARGE_OBJ_TAIL = PageType.Owner4;

        /// <summary>
        /// BUGBUG: Duplicated constant.
        /// </summary>
        private const int LOG_PAGE_SIZE = 12;

        /// <summary>
        /// The size of each block (which contains a single object size)
        /// </summary>
        internal static int BLOCK_SIZE {
            get { return (1 << LOG_PAGE_SIZE) - PageHeader.Size; }
        }

        /// <summary>
        /// The threshold where objects become large objects.
        /// </summary>
        internal static UIntPtr LARGE_OBJECT_THRESHOLD {
            get { return (UIntPtr) unchecked((uint) (BLOCK_SIZE >> 1) + 1); }
        }

        /// <summary>
        /// The largest possible size class.
        /// </summary>
        internal static uint SIZE_CLASSES {
            get {
                return 33 + unchecked((uint)((LARGE_OBJECT_THRESHOLD-1) >> 7));
            }
        }
        
        internal static bool EagerMemClear {
            get {
                return true;
            }
        }
        
        internal static bool LazyMemClear {
            get {
                return false;
            }
        }
        
        [Inline]
        private static void DoLazyMemClear(UIntPtr regionPtr,
                                           uint sizeClass)
        {
            if (LazyMemClear) {
                Util.MemClear(regionPtr-PreHeader.Size,
                              (UIntPtr) GetCellSize(sizeClass));
            }
        }

        internal static bool fVerifyLists {
            get { 
                return false;
            }
        }

        #endregion

        #region Size Class Mappings
        /// <summary>
        /// Returns the size class index for an object of the specified size.
        ///
        /// BUGBUG: We hope that from an inlined allocation site this is
        /// resolved as a constant. That is why this was changed to remove
        /// indirection through an index lookup table.
        /// </summary>
        [Inline]
        private static uint GetSizeClass(UIntPtr bytes) {
            // Exact request rounds down to lower size class.
            bytes = bytes - 1;
            // Sizes 0 -> 64 are in classes 0 -> 15
            // Sizes 72 -> 128 are in classes 16 -> 23
            // Sizes 140 -> 256 are in classes 24 -> 31
            // Sizes 256 -> 512 are in classes 32 -> 35
            // We skip a power of 2 because large objects are rare.
            //Sizes 512 and up are in classes 36 -> 41
            if (bytes <  64) return  0 + ((uint)bytes >> 2);
            if (bytes < 128) return  8 + ((uint)bytes >> 3);
            if (bytes < 256) return 16 + ((uint)bytes >> 4);
            if (bytes < 512) return 28 + ((uint)bytes >> 6);
            if (bytes < LARGE_OBJECT_THRESHOLD) return 32 + ((uint)bytes >> 7);
            VTable.DebugPrint("GetSizeClass called on large object size");
            VTable.DebugBreak();
            return 0;
        }

        /// <summary>
        /// Returns the cell size for a given size class.
        /// </summary>
        private static uint GetCellSize(uint sizeClass) {
            // REVIEW: This should be made into a table lookup!
            VTable.Assert(sizeClass < SIZE_CLASSES,
                          "Attempt cellSize for invalid sizeClass");

            uint sc = sizeClass + 1;

            uint bytes;
            if      (sc <= 16) bytes = (sc -  0) << 2;
            else if (sc <= 24) bytes = (sc -  8) << 3;
            else if (sc <= 32) bytes = (sc - 16) << 4;
            else if (sc <= 36) bytes = (sc - 28) << 6;
            else               bytes = (sc - 32) << 7;

            return bytes;
        }
        #endregion

        #region Memory Accounting
        /// <summary>
        /// A count of the bytes allocated for small objects.
        /// </summary>
        internal static UIntPtr SmallBytes;

        /// <summary>
        /// A count of the bytes for objects the process of being freed.
        /// </summary>
        internal static UIntPtr SmallFreedBytes;

        /// <summary>
        /// A count of the small pages in the process of being freed.
        /// </summary>
        internal static UIntPtr SmallFreedPages;

        /// <summary>
        /// A count of the large pages in the process of being freed.
        /// </summary>
        internal static UIntPtr LargeFreedPages;

        /// <summary>
        /// A count of the bytes allocated for large objects.
        /// </summary>
        internal static UIntPtr LargeBytes {
            get {
                return PageTable.RegionSize(LargePages);
            }
        }

        /// <summary>
        /// The number of pages reserved for large objects.
        /// </summary>
        internal static UIntPtr LargePages;

        /// <summary>
        /// The number of pages reserved for small objects.
        /// </summary>
        internal static UIntPtr SmallPages;

        /// <summary>
        /// A partial free page visitor that does nothing.
        /// </summary>
        internal static NullPartialFreePageVisitor nullPartialFreePageVisitor;

        /// <summary>
        /// This is the total size of data (including object headers)
        /// </summary>
        internal static UIntPtr TotalBytes {
            get {
                return SmallBytes + LargeBytes;
            }
        }

        internal static UIntPtr TotalPages {
            get {
                return SmallPages + LargePages;
            }
        }

        internal static UIntPtr AllocatedPages {
            get {
                return (SmallPages-SmallFreedPages) +
                       (LargePages-LargeFreedPages);
            }
        }

        /// <summary>
        /// The number of pages managed by the alloc heap, including space
        /// occupied by empty cells.
        /// </summary>
        internal static UIntPtr ReservedBytes {
            get {
                return PageTable.RegionSize(SmallPages) + LargeBytes;
            }
        }

        /// <summary>
        /// Increment the counter of the number of small bytes allocated.
        /// </summary>
        [Inline]
        private static void AddSmallBytes(UIntPtr newBytes) {
            SmallBytes += newBytes;
            BaseCollector.IncrementNewBytesSinceGC(newBytes);
        }

        /// <summary>
        /// Increment the counter of the number of large bytes allocated.
        /// </summary>
        [Inline]
        private static void AddLargePages(UIntPtr pageCount) {
            LargePages += pageCount;
            UIntPtr regionSize = PageTable.RegionSize(pageCount);
            BaseCollector.IncrementNewBytesSinceGC(regionSize);
        }

        /// <summary>
        /// Decrement the counter of the number of small bytes allocated.
        /// </summary>
        [Inline]
        private static void SubSmallBytes(UIntPtr newBytes) {
            SmallFreedBytes += newBytes;
        }

        /// <summary>
        /// Decrement the counter of the number of large pages allocated.
        /// </summary>
        [Inline]
        private static void SubLargePages(UIntPtr pageCount) {
            LargeFreedPages += pageCount;
        }

        /// <summary>
        /// Increment the counter of the number of small pages allocated.
        /// </summary>
        [Inline]
        private static void AddSmallPage(PageHeader *page)
        {
            SmallPages += (UIntPtr) 1;
            UIntPtr payloadSize =
                (UIntPtr)page->cellSize * (UIntPtr) page->freeCount;
            AddSmallBytes(PageTable.PageSize - payloadSize);
        }

        /// <summary>
        /// Decrement the counter of the number of small pages allocated.
        /// </summary>
        [Inline]
        private static void SubSmallPage(PageHeader *page)
        {
            SmallFreedPages += (UIntPtr) 1;
            UIntPtr payloadSize =
                (UIntPtr)page->cellSize * (UIntPtr) page->freeCount;
            SubSmallBytes(PageTable.PageSize - payloadSize);
        }

        /// <summary>
        /// Subtract and zero the freed data counts.
        /// </summary>
        internal static void CommitFreedData() {
            SmallPages -= SmallFreedPages;
            SmallFreedPages = UIntPtr.Zero;
            LargePages -= LargeFreedPages;
            LargeFreedPages = UIntPtr.Zero;
            SmallBytes -= SmallFreedBytes;
            SmallFreedBytes = UIntPtr.Zero;
        }
        #endregion

        /// <summary>
        /// When notified of the creation of a new thread we initialize the
        /// alloc heap in that thread.
        /// </summary>
        internal unsafe static void NewThreadNotification(Thread newThread,
                                                          bool initial)
        {
            SegregatedFreeListThread mixinThread = MixinThread(newThread);
            if (initial) {
                // Initialise the initial thread.
                mixinThread.segregatedFreeList.localPages = (PageHeader*[])
                    BootstrapMemory.Allocate(typeof(PageHeader*[]),
                                             SIZE_CLASSES);
                mixinThread.segregatedFreeList.freeList = (UIntPtr[])
                    BootstrapMemory.Allocate(typeof(UIntPtr[]), SIZE_CLASSES);
            } else {
                // We have to create the thread-specific array of pages.
                mixinThread.segregatedFreeList.freeList =
                    new UIntPtr[SIZE_CLASSES];
                mixinThread.segregatedFreeList.localPages =
                    new PageHeader*[SIZE_CLASSES];
            }
        }

        /// <summary>
        /// A thread has finished, so we release any local pages.
        /// </summary>
        internal static void DeadThreadNotification(Thread deadThread)
        {
            SegregatedFreeListThread mixinThread = MixinThread(deadThread);
            for (uint i = 0; i < SIZE_CLASSES; i++) {
                if (mixinThread.segregatedFreeList.localPages[i] != null) {
                    mixinThread.segregatedFreeList.ReleaseLocalPage(i);
                }
            }
        }

        /// <summary>
        /// Allocate a large object. Large objects don't share pages with
        /// any other objects. Get memory for the object directly from the
        /// PageManager.
        /// </summary>
        [ManualRefCounts]
        private static unsafe UIntPtr AllocateLarge(uint alignment,
                                                    UIntPtr bytes,
                                                    Thread currentThread)
        {
            UIntPtr pageCount = PageTable.PageCount(PageTable.PagePad(bytes));
            bool fCleanPages = true;
            UIntPtr page = PageManager.EnsurePages(currentThread,
                                                   pageCount, INIT_PAGE,
                                                   ref fCleanPages);

            UIntPtr regionSize = PageTable.RegionSize(pageCount);
            AddLargePages(pageCount);

            int unusedBytes = (int) (regionSize - bytes);
            int unusedCacheLines = unusedBytes >> 5;
            int offset;
            if (unusedCacheLines != 0) {
                offset = (largeOffset % unusedCacheLines) << 5;
                largeOffset =
                    (largeOffset + 1) & ((int)PageTable.PageSize - 1);
            } else {
                offset = 0;
            }
            UIntPtr pageAddr = PageTable.PageAddr(page);
            UIntPtr startAddr = pageAddr + offset + PreHeader.Size;
            UIntPtr resultAddr =
                Allocator.AlignedObjectPtr(startAddr, alignment);
            uint shortOff = (uint) (resultAddr - pageAddr);
            VTable.Assert((short) shortOff > 0, "offset not positive");
            PageTable.SetExtra(page, shortOff);
            // Ready to be visited
            PageTable.SetType(page, LARGE_OBJ_START);
            if (pageCount > 1) {
                PageTable.SetType(page+1, pageCount-1, LARGE_OBJ_TAIL);
            }
            return resultAddr;
        }

        /// <summary>
        /// Free the specified object. For large objects the page becomes
        /// immediately available. For small objects it may require a call
        /// to RecycleGlobalPages.
        /// </summary>
        [ManualRefCounts]
        internal static void Free(Object obj) {
            UIntPtr objectStart = Magic.addressOf(obj) - PreHeader.Size;
            UIntPtr page = PageTable.Page(objectStart);
            PageType pageType = PageTable.Type(page);
            // Free the object
            if (pageType == SMALL_OBJ_PAGE) {
                uint alignment = obj.vtable.baseAlignment;
                FreeSmall(objectStart, alignment);
            } else {
                VTable.Assert(pageType == LARGE_OBJ_START,
                              "Found GC Page not small or large");
                FreeLarge(obj);
            }
        }

        /// <summary>
        /// Free a small object.
        /// </summary>
        [ManualRefCounts]
        internal static void FreeSmall(UIntPtr objectStart,
                                       uint alignment) {
            PageHeader *pageHeader;
            UIntPtr cellStart =
                freeCell(objectStart, alignment, out pageHeader);
            // Put the object memory cell on the freelist for the page
            UIntPtr oldFreeList;
            do {
                oldFreeList = pageHeader->freeList;
                *(UIntPtr *)cellStart = oldFreeList;
            } while (Interlocked.CompareExchange(ref pageHeader->freeList,
                                                 cellStart, oldFreeList) !=
                     oldFreeList);
            Interlocked.Increment(ref pageHeader->freeCount);
        }

        [ManualRefCounts]
        internal static void LocalFreeSmall(UIntPtr objectStart,
                                            uint alignment) {
            PageHeader *pageHeader;
            UIntPtr cell =
                freeCell(objectStart, alignment, out pageHeader);
            // Put the object memory cell on the freelist for the page
            *(UIntPtr *)cell = pageHeader->freeList;
            pageHeader->freeList = cell;
            pageHeader->freeCount++;
        }

        [Inline]
        [ManualRefCounts]
        private static UIntPtr freeCell(UIntPtr objectStart,
                                        uint alignment,
                                        out PageHeader* pageHeader) {
            UIntPtr pageAddr = PageTable.PageAlign(objectStart);
            pageHeader = (PageHeader*) pageAddr;
            UIntPtr cellStart;
            if (alignment > UIntPtr.Size) {
                cellStart = FindSmallCell(objectStart);
                // REVIEW: Cast to 'int' is needed in Singularity because
                // Singularity defines implicit conversions from uint and ulong
                // (?) causing an ambiguous call to UIntPtr.operator + from
                VTable.Assert(cellStart > (UIntPtr) pageHeader &&
                              cellStart <= objectStart &&
                              cellStart+(int)pageHeader->cellSize >=
                              objectStart+PreHeader.Size,
                              "find small cell found invalid start");
            } else {
                cellStart = objectStart;
            }
            if (EagerMemClear) {
                Util.MemClear(cellStart, (UIntPtr) pageHeader->cellSize);
            }
            SubSmallBytes((UIntPtr) pageHeader->cellSize);

            return cellStart + PreHeader.Size;
        }

        internal unsafe struct TempList {

            private UIntPtr next;

            internal void Add(UIntPtr memAddr) {
                *(UIntPtr *) memAddr = this.next;
                this.next = memAddr;
            }

            internal UIntPtr GetList() {
                UIntPtr result = this.next;
                this.next = UIntPtr.Zero;
                return result;
            }

        }

        [ManualRefCounts]
        internal static void FreeSmallList(ref TempList tempList)
        {
            UIntPtr cell = tempList.GetList();
            if (cell != UIntPtr.Zero) {
                PageHeader *pageHeader = (PageHeader *)
                    PageTable.PageAlign(cell);
                UIntPtr newChain = UIntPtr.Zero;
                UIntPtr newChainTail = cell + PreHeader.Size;
                UIntPtr cellSize = (UIntPtr) pageHeader->cellSize;
                int count = 0;
                do {
                    count++;
                    UIntPtr next = *(UIntPtr *) cell;
                    if (EagerMemClear) {
                        Util.MemClear(cell, cellSize);
                    }
                    UIntPtr cellPtrAddr = cell + PreHeader.Size;
                    *(UIntPtr *) cellPtrAddr = newChain;
                    newChain = cellPtrAddr;
                    cell = next;
                } while (cell != UIntPtr.Zero);
                SubSmallBytes((UIntPtr) count * cellSize);
                UIntPtr oldFreeList;
                do {
                    oldFreeList = pageHeader->freeList;
                    *(UIntPtr*)newChainTail = oldFreeList;
                } while (Interlocked.CompareExchange(ref pageHeader->freeList,
                                                     newChain, oldFreeList) !=
                         oldFreeList);
                AtomicAdd(ref pageHeader->freeCount, count);
            }
        }

        /// <summary>
        /// Free a large object.
        /// </summary>
        [ManualRefCounts]
        internal static void FreeLarge(Object obj) {
            UIntPtr objectStart = Magic.addressOf(obj) - PreHeader.Size;
            UIntPtr firstPage = PageTable.Page(objectStart);
            // Release the page(s) that the object resides on
            UIntPtr pageAddr = PageTable.PageAlign(objectStart);
            UIntPtr objectSize = ObjectLayout.Sizeof(obj);
            UIntPtr limitPage =
                PageTable.Page(PageTable.PagePad(objectStart + objectSize));
            UIntPtr pageCount = limitPage - firstPage;
            PageTable.SetType(firstPage, pageCount, INIT_PAGE);
            PageTable.SetExtra(PageTable.Page(pageAddr), 0);
            PageManager.ReleaseUnusedPages(firstPage, pageCount, false);
            SubLargePages(pageCount);
        }

        /// <summary>
        /// Determines whether a given address could be an interior pointer
        /// into an object.  If the function returns true, FindObjectAddr
        /// must be able to find the object containing the given address if
        /// such an object exists.  If the given address is outside the
        /// memory area for any object, it is possible for the function to
        /// return true, in which case FindObjectAddr is expected to
        /// be able to find a nearby object.
        /// Note: this method assumes that a pointer to the tail of one
        /// object and the head of another is really a pointer to the tail
        /// of the former.  In order to use method for pointers into the
        /// PreHeader, add PreHeader.Size to the argument.
        /// </summary>
        internal static unsafe bool IsGcPtr(UIntPtr addr)
        {
            // For an array, a pointer just past the last element in
            // the array is considered to be an interior pointer into
            // the array.  Given our chosen object layout, the address
            // of the first field in the PreHeader can be identical to
            // the address of the location just past the last element
            // of an adjacently allocated array.  In effect, the address
            // of the first field of an object's PreHeader cannot be
            // considered an interior pointer into the object.
            //    This function makes the assumption that it will not
            // be asked about addresses of elements in an object's
            // PreHeader.  Consequently, it can subtract the size of the
            // PreHeader from the given address and then determine if the
            // resulting address is in a memory area that could have been
            // allocated for an object.  The subtraction also conveniently
            // solves the problem of addresses past the last element of an
            // array falling outside the areas of memory that may have
            // been allocated for an object.
            //    For small pages (those containing a bunch of cells of
            // a given size), only the memory reserved for the PageHeader
            // is outside the memory that we assume could be allocated to
            // an object.  For large pages (those containing large objects),
            // the initial offset is excluded.
            if (addr==UIntPtr.Zero) {
                return false;
            }
            UIntPtr baseAddr = addr - PreHeader.Size;
            UIntPtr page = PageTable.Page(baseAddr);
            if (page>=PageTable.pageTableCount) {
                return false;
            }
            UIntPtr pageAddr = PageTable.PageAlign(baseAddr);
            PageType pageType = PageTable.Type(page);
            switch (pageType) {
              case SMALL_OBJ_PAGE: {
                  return baseAddr-pageAddr >= (UIntPtr)PageHeader.Size;
              }
              case LARGE_OBJ_START: {
                  uint brickData = PageTable.Extra(page);
                  return (baseAddr+PreHeader.Size-pageAddr >=
                          (UIntPtr) brickData);
              }
              case LARGE_OBJ_TAIL: {
                  // It is too expensive to find the end of the
                  // object, so we will simply assume that the pointer
                  // is inside the object area.
                  return true;
              }
              default: {
                  return false;
              }
            }
        }

        /// <summary>
        /// Given a possibly interior pointer to an object, return the
        /// real address of the object.  Note that this assumes that
        /// a pointer to the tail of one object and the head of another
        /// is really a pointer to the tail of the former.  In order
        /// to use this for identifying pointers to PreHeader fields,
        /// add PreHeader.Size to the argument.
        /// </summary>
        internal static unsafe UIntPtr Find(UIntPtr addr)
        {
            addr -= PreHeader.Size;
            UIntPtr page = PageTable.Page(addr);
            PageType pageType = PageTable.Type(page);
            VTable.Assert(PageTable.IsGcPage(pageType),
                          "Find called on non-GC page");
            if (pageType == SMALL_OBJ_PAGE) {
                return FindSmall(addr);
            } else {
                return FindLarge(addr);
            }
        }

        /// <summary>
        /// Find a small object (after determining it is on a small page)
        /// </summary>
        private static UIntPtr FindSmall(UIntPtr cellAddr) {
            UIntPtr objectAddr = FindSmallCell(cellAddr) + PreHeader.Size;
            objectAddr = Allocator.SkipAlignment(objectAddr);
            return objectAddr;
        }

        /// <summary>
        /// Find the cell for a given object address
        /// </summary>
        private static unsafe UIntPtr FindSmallCell(UIntPtr objectStart) {
            UIntPtr pageAddr = PageTable.PageAlign(objectStart);
            VTable.Assert(objectStart-pageAddr >= (UIntPtr)PageHeader.Size,
                          "FindSmallCell went back into the page header");
            PageHeader *pageHeader = (PageHeader *) pageAddr;
            UIntPtr firstAddr = pageAddr + PageHeader.Size;
            int cellSize = (int) pageHeader->cellSize;
            return (objectStart - ((int)(objectStart - firstAddr) % cellSize));
        }

        /// <summary>
        /// Find a large object (after determining it is on a large page)
        /// </summary>
        private static UIntPtr FindLarge(UIntPtr addr) {
            UIntPtr page = PageTable.Page(addr);
            while (PageTable.Type(page) == LARGE_OBJ_TAIL) {
                page--;
            }
            VTable.Assert(PageTable.Type(page) == LARGE_OBJ_START);
            uint brickData = PageTable.Extra(page);
            return (PageTable.PageAddr(page) + brickData);
        }

        internal abstract class ObjectVisitor : ObjectLayout.ObjectVisitor {

            internal virtual void VisitSmall(Object obj, UIntPtr memAddr) {
                this.Visit(obj);
            }

            internal virtual void VisitSmallPageEnd() { }

            internal virtual UIntPtr VisitLarge(Object obj) {
                return this.Visit(obj);
            }

            internal override UIntPtr Visit(Object obj) {
                VTable.NotReached("Someone forgot an override method in a "+
                                  "subclass of SegregatedFreeList.ObjectVisitor");
                return UIntPtr.Zero;
            }
            
            internal virtual bool Continue {
                get {
                    return true;
                }
            }

        }

        // Wraps a SegregatedFreeList.ObjectVisitor around a
        // ObjectLayout.ObjectVisitor.
        // Both large and small objects are visited by the same
        // ObjectLayout.ObjectVisitor.
        internal class ObjectVisitorWrapper : ObjectVisitor {

            private ObjectLayout.ObjectVisitor visitor;

            internal ObjectVisitorWrapper(ObjectLayout.ObjectVisitor visitor) {
                this.visitor = visitor;
            }

            internal override void VisitSmall(Object obj, UIntPtr memAddr) {
                this.visitor.Visit(obj);
            }

            internal override UIntPtr VisitLarge(Object obj) {
                return this.visitor.Visit(obj);
            }

        }

        /// <summary>
        /// Visit each object in the heap across all pages.
        /// </summary>
        [ManualRefCounts]
        [Inline]
        internal static void VisitAllObjects(ObjectVisitor visitor)
        {
            VisitObjects(UIntPtr.Zero, PageTable.pageTableCount, visitor);
        }

        /// <summary>
        /// Visit each object in the heap across a range of pages.
        ///
        /// This can be run concurrent to allocations, but not frees.
        /// </summary>
        [ManualRefCounts]
        [Inline]
        internal static void VisitObjects(UIntPtr lowPage,
                                          UIntPtr highPage,
                                          ObjectVisitor visitor)
        {
            for (UIntPtr i = lowPage;
                 i < highPage && visitor.Continue;
                 i++) {
                PageType pageType = PageTable.MyType(i);
                switch (pageType) {
                  case INIT_PAGE: {
                      // The page is either not yet ready for
                      // allocating objects or it contains an object
                      // that is not necessarily fully initialized, so
                      // we can't visit any objects on the page.
                      break;
                  }
                  case SMALL_OBJ_PAGE: {
                      VisitSmallObjects(i, visitor);
                      break;
                  }
                  case LARGE_OBJ_START: {
                      UIntPtr largeObjectPageCount =
                          VisitLargeObject(i, visitor);
                      i += largeObjectPageCount - 1;
                      break;
                  }
                  case LARGE_OBJ_TAIL: {
                      // To get here, another thread must have been
                      // concurrently updating the page table or
                      // initializing a large object.  The other
                      // thread could be in the process of converting
                      // from INIT_PAGE or reclaiming the pages.
                      // Alternatively, the large object at a
                      // preceding LARGE_OBJ_START page may not have
                      // been fully initialized (e.g. length of an
                      // array is missing), but in that case the size
                      // estimate will always err on the small size.
                      // In any case, there are no objects to visit on
                      // this page.
                      break;
                  }
                }
            }
        }

        [Inline]
        internal static void VisitObjects(UIntPtr lowPage,
                                          UIntPtr highPage,
                                          ObjectLayout.ObjectVisitor visitor)
        {
            ObjectVisitor myObjectVisitor = visitor as ObjectVisitor;
            VTable.Assert(myObjectVisitor != null,
                          "SegregatedFreeList requires specialized ObjectVisitor");
            VisitObjects(lowPage, highPage, myObjectVisitor);
        }

        /// <summary>
        /// Visit small objects in a single page.
        /// </summary>
        [ManualRefCounts]
        [Inline]
        private static unsafe void VisitSmallObjects(UIntPtr page,
                                                     ObjectVisitor visitor)
        {
            // The free cells on a small page are linked together in a
            // linked list. The links are at the vtable offset in each cell.
            // The possible values we can see (barring the presence of an
            // alignment marker at the very beginning of the cell) is:
            // (1) a link to another cell on the page, meaning that the cell
            // is free, (2) a null value, meaning either that the cell is the
            // last in the linked list of free cells or that it has just been
            // unlinked from that list and the vtable value has not yet been
            // written, or (3) a vtable pointer, meaning that the cell is
            // populated with an object.
            VTable.Assert(PageTable.Type(page) == SMALL_OBJ_PAGE,
                          "Visiting small objects on invalid page");
            UIntPtr pageAddr = PageTable.PageAddr(page);
            PageHeader *pageHeader = (PageHeader *) pageAddr;
            UIntPtr cellSize = (UIntPtr) pageHeader->cellSize;
            VTable.Assert(cellSize != UIntPtr.Zero,
                          "zero cellSize visiting small");
            UIntPtr lowAddr = pageAddr + PageHeader.Size;
            UIntPtr highAddr = PageTable.PagePad(lowAddr);
            while (lowAddr <= highAddr - cellSize) {
                UIntPtr objectAddr = lowAddr + PreHeader.Size;
                UIntPtr linkPtr = *(UIntPtr *) objectAddr;
                if (PageTable.IsAddrOnPage(linkPtr, page) &&
                    !Allocator.IsAlignment(objectAddr)) {
                    // We have found a link to another cell on this page.
                    // If we had found an alignment token at lowAddr, then
                    // the value seen is not a link pointer.  Instead, it
                    // must be a value from the PreHeader, most likely the
                    // MultiUseWord.  The IsAlignment test is guarding
                    // against the possibility that the MultiUseWord value
                    // happens to be an address on this page. 
                } else if (linkPtr == UIntPtr.Zero &&
                           !Allocator.IsAlignment(objectAddr)) {
                    // We have found the last unused cell in the list of
                    // unused cells on this page.
                } else {
                    objectAddr = Allocator.SkipAlignment(objectAddr);
                    Object maybeObject = Magic.fromAddress(objectAddr);
                    UIntPtr vtablePtr = *maybeObject.VTableFieldAddr;
                    // We need to check for alignment tokens again after reading
                    // the vtablePtr value due to race conditions.
                    // BUGBUG: We really should put a memory fence here!
                    if (!PageTable.IsForeignAddr(vtablePtr) &&
                        PageTable.IsNonGcPage(PageTable.Type(PageTable.Page(vtablePtr))) &&
                        !Allocator.IsAlignment(objectAddr)) {
                        // We have found a slot that contains an object.
                        visitor.VisitSmall(maybeObject, lowAddr);
                    } else {
                        // It looks like we have found a cell that is in the
                        // process of being allocated.  Either the linkPtr is
                        // zero/null, or someone is allocating an object that
                        // has non-standard alignment requirements.
                        if (!(linkPtr == UIntPtr.Zero ||
                              Allocator.IsAlignmentMarkerAddr(lowAddr))) {
                            Util.PrintPageContents(page);
                            VTable.DebugPrint("Bad object at 0x{0:x}\n",
                                              __arglist(linkPtr));
                            VTable.NotReached();
                        }
                    }
                }
                lowAddr += cellSize;
            }
            visitor.VisitSmallPageEnd();
        }

        /// <summary>
        /// Visit a large object on the specified page.
        /// </summary>
        [ManualRefCounts]
        private static UIntPtr VisitLargeObject(UIntPtr page,
                                                ObjectVisitor visitor)
        {
            VTable.Assert(PageTable.Type(page) == LARGE_OBJ_START,
                          "Visiting large object on invalid page");
            // Find the object
            UIntPtr pageAddr = PageTable.PageAddr(page);
            uint brickData = PageTable.Extra(page);
            if (brickData == 0) {
                // Possibly in the process of being allocated.
                return (UIntPtr) 1;
            }
            UIntPtr objectAddr = pageAddr + brickData;
            Object obj = Magic.fromAddress(objectAddr);
            if (obj.vtable == null) {
                // Memory has been allocated, but object is not initialized
                return (UIntPtr) 1;
            }
            // Visit the object
            UIntPtr objectSize = visitor.VisitLarge(obj);
            // Return the page count
            UIntPtr objectEnd = objectAddr + objectSize - PreHeader.Size;
            UIntPtr limitPage = PageTable.Page(PageTable.PagePad(objectEnd));
            return limitPage - page;
        }

        /// <summary>
        /// This is the the free list of pages to allocate from.
        /// </summary>
        private static UIntPtr[] globalFreePages;

        /// <summary>
        /// This is the list of pages released by threads. These pages must
        /// be periodically processes to release them back for allocation if
        /// necessary.
        /// </summary>
        private static UIntPtr[] globalPages;

        // Used by RecycleGlobalPages to avoid the ABA problem of
        // lock-free data structures.
        private static PageHeader*[] futureGlobalFreePages;

        /// <summary>
        /// Initialize the alloc heap by setting up the heads for all the
        /// linked lists.
        /// </summary>
        [PreInitRefCounts]
        internal static unsafe void Initialize() {
            // Global array of allocated pages
            globalPages = (UIntPtr[])
                BootstrapMemory.Allocate(typeof(UIntPtr[]), SIZE_CLASSES);
            // Global array of pages with free elements
            globalFreePages = (UIntPtr[])
                BootstrapMemory.Allocate(typeof(UIntPtr[]), SIZE_CLASSES);
            // Temporary list holders used by RecycleGlobalPages
            futureGlobalFreePages = (PageHeader*[])
                BootstrapMemory.Allocate(typeof(PageHeader*[]), SIZE_CLASSES);
            nullPartialFreePageVisitor = (NullPartialFreePageVisitor)
                BootstrapMemory.Allocate(typeof(NullPartialFreePageVisitor));
        }

        /// <summary>
        /// Take all global pages that have had elements freed and put them in
        /// the allocation queues.
        /// </summary>
        internal static void RecycleGlobalPages() {
            RecycleGlobalPagesPhase1();
            RecycleGlobalPagesPhase2();
        }

        internal static void RecycleGlobalPagesPhase1() 
        {
            RecycleGlobalPagesPhase1(nullPartialFreePageVisitor);
        }
        
        internal static void
        RecycleGlobalPagesPhase1(PartialFreePageVisitor pageVisitor)
        {
            for (uint i = 0; i < SIZE_CLASSES; i++) {
                // Steal full chain, split into chains of full and
                // non-full pages
                PageHeader* globalFull = AtomicPopChain(ref globalPages[i]);
                PageSeparation pageSeparation;
                int cellSize = (int) GetCellSize(i);
                if (SplitList(globalFull, cellSize, 0, pageVisitor,
                              out pageSeparation)) {
                    // Reinsert chain of full pages into full chain
                    if (!pageSeparation.fullList.IsEmpty) {
                        AtomicPushIncrementList(ref globalPages[i],
                                                pageSeparation.fullList);
                    }
                    // Store away information about the future free chain.
                    VTable.Assert(futureGlobalFreePages[i] == null,
                                  "Non-empty list of future free pages");
                    PageHeaderList freeList = new PageHeaderList();
                    freeList.Append(pageSeparation.partialList);
                    freeList.Append(pageSeparation.emptyList);
                    futureGlobalFreePages[i] = freeList.head;
                }
            }
        }

        internal enum PartialPageAction {
            CommitFree,
            CommitFull,
            Hold
        }

        internal abstract class PartialFreePageVisitor
        {
            internal abstract void Start();
            internal abstract PartialPageAction VisitPage(UIntPtr page,
                                                          PageHeader *ph,
                                                          int cells);
            internal abstract void ObserveEmptyPage();
            internal abstract void Finish();
        }

        internal class NullPartialFreePageVisitor : PartialFreePageVisitor
        {

            internal override void Start()
            {
            }
            
            internal override PartialPageAction VisitPage(UIntPtr page,
                                                          PageHeader *ph,
                                                          int cells)
            {
                return PartialPageAction.CommitFree;
            }

            internal override void ObserveEmptyPage()
            {
            }

            internal override void Finish()
            {
            }

        }

        internal static void RecycleGlobalPagesPhase2()
        {
            RecycleGlobalPagesPhase2(nullPartialFreePageVisitor);
        }

        internal static
        void RecycleGlobalPagesPhase2(PartialFreePageVisitor pageVisitor)
        {
            for (uint i = 0; i < SIZE_CLASSES; i++) {
                PageHeader* futureFreeHead = futureGlobalFreePages[i];
                if (futureFreeHead != null) {
                    futureGlobalFreePages[i] = null;
                    // Swap the existing free chain with the chain of recycled
                    // non-full pages.
                    PageHeader* futureTail = null;
                    if (fVerifyLists) {
                        futureTail = VerifySimpleList(futureFreeHead);
                    }
                    PageHeader* oldFreeHead = (PageHeader *)
                        AtomicSwitchChains(ref globalFreePages[i],
                                           futureFreeHead);
                    if (oldFreeHead == null) {
                        continue;
                    }
                    if (fVerifyLists) {
                        PageHeader* oldTail = VerifySimpleList(oldFreeHead);
                        VTable.Deny(futureTail == oldTail,
                                    "Old and future free lists share a tail");
                    }
                    PageSeparation pageSeparation;
                    int cellSize = (int) GetCellSize(i);
                    if (SplitList(oldFreeHead, cellSize, 2, pageVisitor,
                                  out pageSeparation)) {
                        if (pageSeparation.emptyList.head == oldFreeHead) {
                            // We cannot put the first element of the old
                            // chain back on the globalFreePages list
                            // since that would invite the possibility of
                            // ABA problems.  Put it on the globalPages
                            // list, since we know that doing so is safe.
                            PageHeader* removedHead =
                                pageSeparation.emptyList.RemoveHead();
                            VTable.Assert(removedHead == oldFreeHead);
                            AtomicPush(ref globalPages[i], removedHead);
                        } else if (pageSeparation.partialList.head ==
                                   oldFreeHead) {
                            PageHeader* removedHead =
                                pageSeparation.partialList.RemoveHead();
                            VTable.Assert(removedHead == oldFreeHead);
                            AtomicPush(ref globalPages[i], removedHead);
                        } else {
                            VTable.Assert(pageSeparation.fullList.head ==
                                          oldFreeHead);
                        }
                        PageHeaderList freeList = new PageHeaderList();
                        freeList.Append(pageSeparation.partialList);
                        freeList.Append(pageSeparation.emptyList);
                        if (!freeList.IsEmpty) {
                            PageHeader *skippedGlobalFreeHead =
                                AtomicPushDecrementList(ref globalFreePages[i],
                                                        freeList);
                            if (skippedGlobalFreeHead != null) {
                                // Put the node removed from globalFreePages
                                // as part of the list merge onto the
                                // globalPage list, as that is always safe.
                                AtomicPush(ref globalPages[i],
                                           skippedGlobalFreeHead);
                            }
                        }
                        // Reinsert chain of full pages into full chain
                        if (!pageSeparation.fullList.IsEmpty) {
                            AtomicPushIncrementList(ref globalPages[i],
                                                    pageSeparation.fullList);
                        }
                    }
                }
            }
        }

        internal static void LocalRecycleGlobalPages() {
            nullPartialFreePageVisitor.Start();
            for (uint i=0; i < SIZE_CLASSES; i++) {
                PageHeader* globalFull = (PageHeader*) globalPages[i];
                globalPages[i] = UIntPtr.Zero;

                PageSeparation pageSeparation;

                int cellSize = (int)GetCellSize(i);
                if (SplitList(globalFull, cellSize, 0,
                              nullPartialFreePageVisitor,
                              out pageSeparation)) {
                    // Reinsert values onto the free and full chains
                    if (!pageSeparation.fullList.IsEmpty) {
                        globalPages[i] = (UIntPtr)
                            pageSeparation.fullList.head;
                    }
                    PageHeaderList freeList = new PageHeaderList();
                    freeList.Append(pageSeparation.partialList);
                    freeList.Append(pageSeparation.emptyList);
                    if (!freeList.IsEmpty) {
                        PageHeader* globalFree =
                            (PageHeader *) globalFreePages[i];
                        globalFreePages[i] = (UIntPtr) freeList.head;

                        if (SplitList(globalFree, cellSize, 1,
                                      nullPartialFreePageVisitor,
                                      out pageSeparation)) {
                            VTable.Assert(pageSeparation.fullList.IsEmpty,
                                          "full free pages found");
                            freeList = new PageHeaderList();
                            freeList.Append(pageSeparation.partialList);
                            freeList.Append(pageSeparation.emptyList);
                            if (!freeList.IsEmpty) {
                                freeList.tail->nextPage =
                                    (PageHeader *) globalFreePages[i];
                                globalFreePages[i] = (UIntPtr) freeList.head;
                            }
                        }
                    }
                }
            }
            nullPartialFreePageVisitor.Finish();
        }

        // reclamationRate: the fraction of completely free pages that
        // should be returned to the PageManager.  A value of 0 means
        // that no pages are returned.  A value of 5 means that 1/5 of
        // the eligible pages are returned.
        private static bool SplitList(PageHeader* inputChain,
                                      int cellSize,
                                      int reclamationRate,
                                      PartialFreePageVisitor pageVisitor,
                                      out PageSeparation pageSeparation)
        {
            pageSeparation = new PageSeparation();
            if (fVerifyLists) {
                VerifySimpleList(inputChain);
            }
            // Start with free pages (they can not become full)
            PageHeader* current = inputChain;
            // Determine starting point
            if (current == null) {
                return false;
            }
            // Number of cells of this size class in a block
            int cells = BLOCK_SIZE / cellSize;
            VTable.Assert(cells > 0 && cells < (BLOCK_SIZE >> 1),
                          "invalid cell count");
            // Iterate through list
            int reclamationCount = 0;
            while (current != null) {
                PageHeader *page = current;
                current = page->nextPage;
                if (page->freeCount == cells &&
                    ++reclamationCount == reclamationRate) {
                    // Completely Free Page
                    reclamationCount = 0;
                    SubSmallPage(page);
                    UIntPtr pageNum = PageTable.Page((UIntPtr) page);
                    PageTable.SetType(pageNum, INIT_PAGE);
                    PageTable.SetExtra(pageNum, 0);
                    PageManager.ReleaseUnusedPages(pageNum,
                                                   (UIntPtr) 1,
                                                   false);
                    continue;
                }
                if (page->freeCount == cells) {
                    pageVisitor.ObserveEmptyPage();
                    pageSeparation.emptyList.Append(page);
                } else if (page->freeCount > 0) {
                    // Partially Free Page
                    PartialPageAction action =
                        pageVisitor.VisitPage(PageTable.Page((UIntPtr) page),
                                              page, cells);
                    if (action == PartialPageAction.CommitFree) {
                        pageSeparation.partialList.Append(page);
                    } else if (action == PartialPageAction.CommitFull) {
                        pageSeparation.fullList.Append(page);
                    } else {
                        VTable.NotReached("CMS PartialPageAction.Hold");
                    }
                } else {
                    // Completely Full Page
                    pageSeparation.fullList.Append(page);
                }
            }
            if (fVerifyLists) {
                pageSeparation.emptyList.VerifyTailedList();
                pageSeparation.partialList.VerifyTailedList();
                pageSeparation.fullList.VerifyTailedList();
            }
            return true;
        }

        /// <summary>
        /// Atomically add a value to a field.
        /// </summary>
        private static void AtomicAdd(ref int addr, int value) {
            int oldValue, newValue;
            do {
                oldValue = addr;
                newValue = oldValue + value;
            } while (Interlocked.CompareExchange(ref addr, newValue, oldValue)
                     != oldValue);
        }

        /// <summary>
        /// Atomically push a value onto a linked list.  The linked list
        /// may be concurrently added to, but may not be concurrently
        /// removed from.
        /// </summary>
        private static void AtomicPush(ref UIntPtr head, PageHeader *page) {
            VTable.Assert(page->nextPage == null,
                          "Expected single page, found page list");
            UIntPtr oldHead;
            do {
                oldHead = head;
                page->nextPage = (PageHeader*) oldHead;
            } while (Interlocked.CompareExchange(ref head, (UIntPtr) page,
                                                 oldHead) != oldHead);
        }

        /// <summary>
        /// Atomically remove a value from the linked list. Returns null
        /// if the list is empty.  The list may be concurrently removed
        /// from by means of AtomicPop and concurrently added to by means
        /// of AtomicPushDecrementList.
        /// </summary>
        private static PageHeader * AtomicPop(ref UIntPtr head) {
            PageHeader* oldHead;
            PageHeader* newHead;
            do {
                oldHead = (PageHeader*) head;
                if (oldHead == null) {
                    // Empty list.
                    return null;
                }
                newHead = oldHead->nextPage;
            } while(Interlocked.CompareExchange(ref head, (UIntPtr) newHead,
                                                (UIntPtr) oldHead)
                    != (UIntPtr) oldHead);
            oldHead->nextPage = null;
            return oldHead;
        }

        /// <summary>
        /// Steal an entire list.  Atomic PopChain can be done concurrently
        /// with any other atomic operation.  The removal of an entire chain
        /// does not by itself invite the ABA problem of lock-free algorithms.
        /// </summary>
        private static PageHeader* AtomicPopChain(ref UIntPtr head) {
            return (PageHeader *) Interlocked.Exchange(ref head, UIntPtr.Zero);
        }

        private static PageHeader* AtomicSwitchChains(ref UIntPtr head,
                                                      PageHeader *newHead) {
            return (PageHeader*) Interlocked.Exchange(ref head,
                                                      (UIntPtr) newHead);
        }

        /// <summary>
        /// Push a whole chain onto a list.
        /// The list may be concurrently added to by means to AtomicPush.
        /// </summary>
        private static void AtomicPushIncrementList(ref UIntPtr head,
                                                    PageHeaderList list)
        {
            if (fVerifyLists) {
                PageHeader* tail = VerifySimpleList((PageHeader*)head);
                list.VerifyTailedList();
                VTable.Deny(tail == list.tail, "Lists have shared tail");
            }
            UIntPtr oldHead;
            UIntPtr newHead = (UIntPtr) list.head;
            do {
                oldHead = head;
                list.tail->nextPage = (PageHeader*) oldHead;
            } while (Interlocked.CompareExchange(ref head, newHead, oldHead)
                     != oldHead);
        }

        /// <summary>
        /// Push a whole chain onto a list.
        /// The list may be concurrently removed from by AtomicPop.
        /// The removal is done along with removal of the first element of
        /// the list, and the removed node is returned.  The removal of
        /// the first element of the list ensures the absence of an ABA
        /// problem.  AtomicPop and AtomicPushDecrementList are both
        /// tolerant of the particular kind of ABA change that could occur
        /// without removal of the first element of the list, but the
        /// defensive mechanism is used anyway to ensure that potential
        /// future problems are avoided.
        /// </summary>
        private static PageHeader* AtomicPushDecrementList(ref UIntPtr head,
                                                           PageHeaderList list)
        {
            if (fVerifyLists) {
                list.VerifyTailedList();
            }
            PageHeader* oldHead;
            PageHeader* oldNext;
            UIntPtr newHead = (UIntPtr) list.head;
            do {
                oldHead = (PageHeader *) head;
                oldNext = (oldHead == null) ? null : oldHead->nextPage;
                list.tail->nextPage = oldNext;
                
            } while (Interlocked.CompareExchange(ref head, newHead,
                                                 (UIntPtr) oldHead)
                     != (UIntPtr) oldHead);
            if (oldHead != null) {
                oldHead->nextPage = null;
            }
            return oldHead;
        }

        internal static PageHeader* VerifySimpleList(PageHeader *head)
        {
            VTable.Assert(fVerifyLists);
            if (head == null) {
                return null;
            }
            PageHeader* probe = head->nextPage;
            PageHeader* slow = head;
            PageHeader* tail = head;
            // Use the old fast+slow trick to catch circular lists!
            while (true) {
                if (probe == null) {
                    return tail;
                }
                VTable.Assert(probe != slow, "Circular page list!");
                tail = probe;
                probe = tail->nextPage;
                if (probe == null) {
                    return tail;
                }
                VTable.Assert(probe != slow, "Circular page list!");
                tail = probe;
                probe = tail->nextPage;
                slow = slow->nextPage;
            }
        }

        private struct PageSeparation {
            internal PageHeaderList emptyList;
            internal PageHeaderList partialList;
            internal PageHeaderList fullList;
        }

        private struct PageHeaderList {

            internal PageHeader *head;
            internal PageHeader *tail;

            internal PageHeaderList(PageHeader *page)
            {
                this.head = page;
                this.tail = page;
                if (fVerifyLists) {
                    VTable.Assert(page->nextPage == null,
                                  "Expected single page, got a list of them");
                    this.VerifyTailedList();
                }
            }

            internal bool IsEmpty
            {
                get { return this.head == null; }
            }

            /// <summary>
            /// Add a page onto a local linked list (possibly the first page)
            /// </summary>
            internal void Append(PageHeader *page)
            {
                page->nextPage = null;
                if (this.head == null) {
                    this.head = page;
                    this.tail = page;
                    return;
                } else {
                    VTable.Assert(this.tail->nextPage == null,
                                  "Add expected a single page, got a list");
                }
                this.tail->nextPage = page;
                this.tail = page;
            }

            internal void Append(PageHeaderList appendList) {
                if (appendList.IsEmpty) {
                    // Do nothing
                } else if (this.IsEmpty) {
                    this.head = appendList.head;
                    this.tail = appendList.tail;
                } else {
                    this.tail->nextPage = appendList.head;
                    this.tail = appendList.tail;
                }
            }

            internal PageHeader* RemoveHead() {
                PageHeader *oldHead = this.head;
                this.head = this.head->nextPage;
                oldHead->nextPage = null;
                return oldHead;
            }

            internal bool Contains(PageHeader *page)
            {
                PageHeader *cursor = this.head;
                while (cursor != null) {
                    if (cursor == page) {
                        return true;
                    }
                    cursor = cursor->nextPage;
                }
                return false;
            }

            internal void VerifyTailedList()
            {
                VTable.Assert(fVerifyLists);
                if (this.head == null) {
                    VTable.Assert(this.tail == null,
                                  "Null head and non-null tail");
                    return;
                } else {
                    VTable.Assert(this.tail != null,
                                  "Non-null head and null tail");
                    VTable.Assert(this.tail->nextPage == null,
                                  "Tail->nextPage is non-null");
                }
                PageHeader* foundTail = VerifySimpleList(this.head);
                VTable.Assert(this.tail == foundTail,
                              "Lists are not disjoint");
            }

        }

        /// <summary>
        /// This struct represents the header data stored in each
        /// small object page.
        ///
        /// BUGBUG: Not space efficient.
        /// </summary>
        [StructLayout(LayoutKind.Sequential)]
        internal struct PageHeader {

            internal static int Size {
                get { return sizeof(PageHeader); }
            }

            /// <summary>
            /// The next page in the linked list.
            /// </summary>
            internal PageHeader* nextPage;

            /// <summary>
            /// The head of the free list for this page. This is not
            /// used when a page is assigned to a thread.
            /// </summary>
            internal UIntPtr freeList;

            /// <summary>
            /// The cell size for objects in this page.
            /// </summary>
            internal ushort cellSize;

            /// <summary>
            /// User value.
            /// </summary>
            // Note that this should be more than a user value.  In
            // particular, when CoCo marks a page for evacuation then
            // the page should not be used for any subsequent allocation.
            internal ushort userValue;

            /// <summary>
            /// The number of cells that have been freed. This is used
            /// for accounting purposes.
            /// </summary>
            internal int freeCount;
        }

        #endregion

        #region Local  (Safe from the context of owner thread)
        /// <summary>
        /// This is a thread's local free list for each size class.
        /// </summary>
        [RequiredByBartok]
        private UIntPtr[] freeList;

        /// <summary>
        /// This is a thread's local set of pages for each size class.
        /// </summary>
        private PageHeader*[] localPages;

        [ManualRefCounts]
        internal static UIntPtr Allocate(Thread thread,
                                         UIntPtr bytes, uint alignment)
        {
            SegregatedFreeListThread mixinThread = MixinThread(thread);
            return mixinThread.segregatedFreeList.Allocate(bytes, alignment,
                                                           thread);
        }

        [ManualRefCounts]
        internal UIntPtr Allocate(UIntPtr bytes, uint alignment, Thread thread)
        {
            UIntPtr resultAddr = this.AllocateFast(bytes, alignment);
            if (resultAddr == UIntPtr.Zero) {
                resultAddr = this.AllocateSlow(bytes, alignment, thread);
            }
            return resultAddr;
        }

        [Inline]
        [ManualRefCounts]
        internal static UIntPtr AllocateFast(Thread thread,
                                             UIntPtr bytes,
                                             uint alignment)
        {
            SegregatedFreeListThread mixinThread = MixinThread(thread);
            return mixinThread.segregatedFreeList.AllocateFast(bytes,
                                                               alignment);
        }

        [RequiredByBartok]
        [Inline]
        [DisableBoundsChecks]
        public static unsafe Object CompilerAllocateMarkSweep
        (VTable vtable, Thread currentThread, UIntPtr bytes, uint alignment)
        {
            VTable.Assert((alignment == 4)
                          || ((alignment == 8) && (UIntPtr.Size == 8))
                          || ((alignment == 8) && (PreHeader.Size == 4)),
                          "Unsupported object layout");
            VTable.Assert(UIntPtr.Size == PreHeader.Size,
                          "Unsupported preheader size");
            VTable.Assert(Util.IsAligned((uint) PreHeader.Size +
                                         (uint)PostHeader.Size, alignment),
                          "Unsupported header sizes");
            VTable.Assert(bytes < LARGE_OBJECT_THRESHOLD,
                          "CompilerAllocate called for large object");

            UIntPtr origBytes=  bytes;
            
            // Room to ensure alignment
            bool alignRequired = (alignment > UIntPtr.Size);
            if (alignRequired) {
                bytes = bytes + alignment - UIntPtr.Size;
            }
            uint sizeClass = GetSizeClass(bytes);
            SegregatedFreeListThread mixinThread = MixinThread(currentThread);
            UIntPtr region = mixinThread.segregatedFreeList.freeList[sizeClass];
            if (region != UIntPtr.Zero) {
                mixinThread.segregatedFreeList.freeList[sizeClass] =
                    *(UIntPtr *)region;

                // Zero out the free list data structure.  However, if the
                // vtable is at offset zero, then we're going to overwrite it
                // anyway.  (and the optimizer does not see this through the
                // unmanaged/managed conversion)
                if (Magic.OffsetOfVTable != UIntPtr.Zero) {
                    *(UIntPtr *)region = UIntPtr.Zero;
                }

                DoLazyMemClear(region, sizeClass);

                UIntPtr objAddr = region;

                if((alignment == 8) && (UIntPtr.Size == 4)) {
                    // Since 'objAddr' will be the actual object reference, we
                    // want to misalign it here so that the object payload will
                    // be aligned.  (We know that PostHeader.Size & 8 == 4
                    // because the PreHeader is 4 and the sum of the PreHeader
                    // and PostHeader sizes is a multiple of alignment (8))

                    // Store alignment token at objAddr.  This will be where an
                    // alignment token should go if it is required...
                    Allocator.WriteAlignment(objAddr);
                    // ... (align if necessary) ...
                    objAddr = Util.Align(objAddr, (UIntPtr) alignment);
                    // ... or where the object header will be if alignment was
                    // not necessary.  This code zeroes the object header
                    // regardless and avoids a branch in this fast path.
                    *(UIntPtr *)objAddr = UIntPtr.Zero;
                    // Finally misalign 'objAddr'
                    objAddr += PreHeader.Size;
                }
                
                Object obj = Magic.fromAddress(objAddr);
                obj.vtable = vtable;
                return obj;
            }

            return GC.AllocateObjectNoInline(vtable, currentThread);
        }

        [Inline]
        [ManualRefCounts]
        private UIntPtr AllocateFast(UIntPtr bytes, uint alignment)
        {
            UIntPtr origBytes = bytes;
            // Room to ensure alignment
            bool alignRequired = (alignment > UIntPtr.Size);
            if (alignRequired) {
                bytes = bytes + alignment - UIntPtr.Size;
            }
            // Is this a large object?
            if (!(bytes < LARGE_OBJECT_THRESHOLD)) {
                return UIntPtr.Zero;
            }
            uint sizeClass = GetSizeClass(bytes);
            UIntPtr region = AllocateSmallFast(sizeClass);
            if (region == UIntPtr.Zero) {
                return UIntPtr.Zero;
            } else {
                DoLazyMemClear(region, sizeClass);
                UIntPtr resultAddr =
                    Allocator.AlignedObjectPtr(region, alignment);
                return resultAddr;
            }
        }

        [Inline]
        [ManualRefCounts]
        internal static UIntPtr AllocateSlow(Thread thread,
                                             UIntPtr bytes, uint alignment)
        {
            SegregatedFreeListThread mixinThread = MixinThread(thread);
            return mixinThread.segregatedFreeList.AllocateSlow(bytes,
                                                               alignment,
                                                               thread);
        }

        [NoInline]
        [ManualRefCounts]
        private UIntPtr AllocateSlow(UIntPtr bytes, uint alignment,
                                      Thread currentThread)
        {
            UIntPtr origBytes = bytes;
            
            // Room to ensure alignment
            bool alignRequired = (alignment > UIntPtr.Size);

            if (alignRequired) {
                bytes = bytes + alignment - UIntPtr.Size;
            }

            // Is this a large object?
            if (!(bytes < LARGE_OBJECT_THRESHOLD)) {
                return AllocateLarge(alignment, bytes, currentThread);
            }

            uint sizeClass = GetSizeClass(bytes);
            UIntPtr region = AllocateSmall(sizeClass, currentThread);
            DoLazyMemClear(region, sizeClass);
            UIntPtr resultAddr =
                Allocator.AlignedObjectPtr(region, alignment);
            return resultAddr;
        }

        /// <summary>
        /// Used to attempt to spread large objects across pages to avoid
        /// higher cache conflicts on low page addresses.
        /// </summary>
        private static int largeOffset;

        /// <summary>
        /// Allocate an object of a specified size class from the
        /// thread's local block.
        /// </summary>
        [Inline]
        [ManualRefCounts]
        private UIntPtr AllocateSmall(uint sizeClass, Thread currentThread) {
            UIntPtr region = freeList[sizeClass];
            if (region != UIntPtr.Zero) {
                freeList[sizeClass] = *(UIntPtr*)region;
                *(UIntPtr*)region = UIntPtr.Zero;
                return region;
            } else {
                return AllocateSmallSlow(sizeClass, currentThread);
            }
        }

        [Inline]
        private UIntPtr AllocateSmallFast(uint sizeClass) {
            UIntPtr region = freeList[sizeClass];
            if (region != UIntPtr.Zero) {
                freeList[sizeClass] = *(UIntPtr*)region;
                *(UIntPtr*)region = UIntPtr.Zero;
                return region;
            } else {
                return UIntPtr.Zero;
            }
        }

        /// <summary>
        /// Get a new thread-local page and allocate from it.
        /// </summary>
        [ManualRefCounts]
        private UIntPtr AllocateSmallSlow(uint sizeClass, Thread currentThread)
        {
            // Get a new page.
            PageHeader* newPage = GetLocalPage(sizeClass, currentThread);
            VTable.Assert(newPage != null, "GetLocalPage returned null");
            // Return old page.
            // After GetLocalPage, in case of allocation during that call.
            if (this.localPages[sizeClass] != null) {
                ReleaseLocalPage(sizeClass);
            }
            // Install new page.
            VTable.Assert(this.localPages[sizeClass] == null,
                          "Already had a local page");
            this.localPages[sizeClass] = newPage;
            // Read (and then zero) the free list.
            VTable.Assert(freeList[sizeClass] == UIntPtr.Zero,
                          "Got page with empty free list");
            freeList[sizeClass] =
                Interlocked.Exchange(ref this.localPages[sizeClass]->freeList,
                                     UIntPtr.Zero);

            int gotFreeCount = CountListElements(freeList[sizeClass]);
            AddSmallBytes((UIntPtr) this.localPages[sizeClass]->cellSize *
                          (UIntPtr) gotFreeCount); 
            AtomicAdd(ref this.localPages[sizeClass]->freeCount,
                      -gotFreeCount);
            VTable.Assert(freeList[sizeClass] != UIntPtr.Zero,
                          "GetLocalPage returned empty page");

            // Allocate off the free list
            return AllocateSmallFast(sizeClass);
        }

        private static int CountListElements(UIntPtr head)
        {
            // Count the reclaimed cells.
            UIntPtr listPage = PageTable.Page(head);
            int freeCount = 0;
            UIntPtr next = head;
            while (next != UIntPtr.Zero) {
                VTable.Assert(PageTable.Page(next) == listPage);
                next = *(UIntPtr*)next;
                freeCount++;
            }
            return freeCount;
        }

        private static bool FreeListContains(UIntPtr list, UIntPtr element)
        {
            while (list != UIntPtr.Zero) {
                if (list == element) {
                    return true;
                }
                list = *(UIntPtr*)list;
            }
            return false;
        }

        /// <summary>
        /// Release a local allocation page into the pool of consumed pages.
        /// </summary>
        [ManualRefCounts]
        private void ReleaseLocalPage(uint sizeClass) {
            PageHeader *page = this.localPages[sizeClass];
            this.localPages[sizeClass] = null;
            VTable.Assert(page->nextPage == null, "Local page on page list");
            // Prepare the page to be released
            UIntPtr pageFreeList = freeList[sizeClass];
            if (pageFreeList != UIntPtr.Zero) {
                // We are releasing the page 'early'.
                freeList[sizeClass] = UIntPtr.Zero;
                // Save our local free list as the page's free list.
                // We use Interlocked.CompareExchange because a concurrent
                // collector's sweep phase may asynchronously add to the
                // free list.  Attempts to acquire the list are disallowed.
                UIntPtr oldFreeList =
                    Interlocked.CompareExchange(ref page->freeList,
                                                pageFreeList, UIntPtr.Zero);
                if (oldFreeList != UIntPtr.Zero) {
                    // Page already had a free list.
                    // page->freeList was not changed by CompareExchange.
                    // Follow the found free list to the end.
                    UIntPtr cursor = oldFreeList;
                    while (*(UIntPtr*)cursor != UIntPtr.Zero) {
                        cursor = *(UIntPtr*)cursor;
                    }
                    // Stitch our local free list onto the end of oldFreeList.
                    *(UIntPtr*)cursor = pageFreeList;
                } else {
                    // Page did not have a free list.
                    // page->freeList was changed by CompareExchange.
                    // Nothing more to do.
                }
                // Count the number of elements not allocated and update
                // the global statistics counters.
                int freeCount = CountListElements(pageFreeList);
                SubSmallBytes((UIntPtr) ((uint)freeCount *
                                          (uint)page->cellSize));
                // Add the free'd blocks to the freeCount.
                AtomicAdd(ref page->freeCount, freeCount);
                // The free list should not have changed, as the page is
                // not on any publicly visible list.
                VTable.Assert(oldFreeList != UIntPtr.Zero ||
                              FreeListContains(page->freeList, pageFreeList),
                              "Someone stole from our private free list - 1");
                VTable.Assert(oldFreeList == UIntPtr.Zero ||
                              FreeListContains(page->freeList, oldFreeList),
                              "Someone stole from our private free list - 2");
            }
            // Atomically insert the page in the globalPages queue.
            AtomicPush(ref globalPages[sizeClass], page);
            // Nobody should create another local list while we are
            // deleting another one.
            VTable.Assert(this.localPages[sizeClass] == null,
                          "Local page created during ReleaseLocalPage");
        }

        /// <summary>
        /// Either reuse an existing page or acquire a completely new page
        /// to allocate from.
        /// </summary>
        [ManualRefCounts]
        private PageHeader * GetLocalPage(uint sizeClass, Thread currentThread)
        {
            GC.CheckForNeededGCWork(currentThread);
            PageHeader *pageHeader = AtomicPop(ref globalFreePages[sizeClass]);
            if (pageHeader == null) {
                // We didn't get an existing page.  Create a new local page.
                pageHeader = NewLocalPage(sizeClass, currentThread);
            }
            VTable.Assert(pageHeader->freeList != UIntPtr.Zero,
                          "empty FreeList");
            return pageHeader;
        }

        /// <summary>
        /// Create a new page to allocate from.
        /// </summary>
        [ManualRefCounts]
        private PageHeader * NewLocalPage(uint sizeClass, Thread currentThread)
        {
            VTable.Assert(sizeClass > 0, "non-positive sizeClass");
            bool fCleanPages = true;
            UIntPtr page = PageManager.EnsurePages(currentThread,
                                                   (UIntPtr) 1, INIT_PAGE,
                                                   ref fCleanPages);
            UIntPtr pageAddr = PageTable.PageAddr(page);
            PageTable.SetExtra(page, sizeClass);
            PageHeader *pageHeader = (PageHeader *) pageAddr;

            // Set up the free list of free slots
            uint stride = GetCellSize(sizeClass);
            VTable.Assert(stride != 0, "Zero Stride");
            pageHeader->cellSize = (ushort) stride;
            UIntPtr cursor =
                pageAddr + PageHeader.Size + PreHeader.Size;
            pageHeader->freeList = cursor;
            UIntPtr limit =
                PageTable.PageAddr(page+1) - stride + PreHeader.Size;
            int cellCount = 1;
            UIntPtr nextAddr = cursor + stride;
            while (nextAddr <= limit) {
                cellCount++;
                *(UIntPtr*)cursor = nextAddr;
                cursor = nextAddr;
                nextAddr = cursor + stride;
            }
            pageHeader->freeCount = cellCount;
            AddSmallPage(pageHeader);
            PageTable.SetType(page, SMALL_OBJ_PAGE);
            return pageHeader;
        }

        #endregion

    }

}
