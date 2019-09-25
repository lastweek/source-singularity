//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

#if !SINGULARITY || (SINGULARITY_KERNEL && SINGULARITY_MP)
#define USE_SPINLOCK
#elif SINGULARITY_PROCESS
#define USE_MUTEX
#endif

namespace System.GCs {

    using System.Runtime.CompilerServices;
    using System.Threading;

#if SINGULARITY
    using Microsoft.Singularity;
#endif
    
    internal unsafe class PageManager
    {

        // WARNING: don't initialize any static fields in this class
        // without manually running the class constructor at startup!

        // Makes old-generation collections take 5+ seconds:
        private static bool SlowDebug {
            get { return false; }
        }

        // Known to slow down selfhost if true:
        private static bool AggressiveMemReset {
            get { return false; }
        }

        internal static UIntPtr os_commit_size;
        private static UIntPtr heap_commit_size;
        private static UnusedBlockHeader [] unusedMemoryBlocks;
        private static bool avoidDirtyPages;
        private static OutOfMemoryException outOfMemoryException;

#if USE_MUTEX
        private static Mutex mutex;
#elif USE_SPINLOCK
        private static SpinLock Lock;
#endif

        // Unused pages (clean and dirty combined) in the system are combined
        // into multi-page regions.  Parts of the this struct are stored in the
        // first and last pages of each region.  Since a region may be a single
        // page, it is necessary for the various first-page and last-page fields
        // to be stored at different offsets, which is why they are all declared
        // in this struct.  The headers form a list of regions of approximately
        // the same size (see SlotFromCount).  The head of each list is a dummy
        // node in the 'unusedMemoryBlocks' array.  The last page of region
        // simply points back to the beginning of the region.

        internal struct UnusedBlockHeader {

            private const int magicNumber = 0x1234567;

            // Simply a sanity check against random overwrites of the region.
            private UIntPtr magic;

            // Built-in threading for the list of similarly sized regions.
            internal UnusedBlockHeader * next;
            private UnusedBlockHeader * prev;

            // Number of pages in this unused page region.
            internal UIntPtr count;

            // The 'curr' field is in the last block of the unused region.
            // However, the first and last blocks may be the same, so we
            // put the field in the same struct so that the layout can be
            // done automatically for us.  The last block does not have the
            // normal header fields.
            internal UnusedBlockHeader * curr;

            internal static unsafe void Initialize(UnusedBlockHeader *header,
                                                   UIntPtr count)
            {
                header->magic = (UIntPtr) magicNumber;
                header->next = null;
                header->prev = null;
                header->count = count;
                UnusedBlockHeader *tailBlock = (UnusedBlockHeader *)
                    (((UIntPtr) header) + PageTable.RegionSize(count - 1));
                tailBlock->curr = header;
            }

            [System.Diagnostics.Conditional("DEBUG")]
            internal static unsafe void Verify(UnusedBlockHeader *header)
            {
                VTable.Assert(header->magic == (UIntPtr) magicNumber,
                              "Bad magic number in UnusedBlockHeader");
                VTable.Assert(header->count > 0,
                              "Count <= 0 in UnusedBlockHeader");
                VTable.Assert(header->prev->next == header,
                              "UnusedBlockHeader not linked properly (1)");
                if (header->next != null) {
                    VTable.Assert(header->next->prev == header,
                                  "UnusedBlockHeader not linked properly (2)");
                }
                UIntPtr count = header->count;
                UnusedBlockHeader *tailBlock = (UnusedBlockHeader *)
                    (((UIntPtr) header) + PageTable.RegionSize(count - 1));
                VTable.Assert(tailBlock->curr == header,
                              "UnusedBlockHeader tail->curr is incorrect");
                if (PageManager.SlowDebug) {
                    UIntPtr page = PageTable.Page((UIntPtr)header);
                    for (UIntPtr i = UIntPtr.Zero; i < count; i++) {
                        VTable.Assert(PageTable.IsUnusedPage(page+i) &&
                                      PageTable.IsMyPage(page+i),
                                      "Incorrect page in unused region");
                    }
                }
            }

            internal static unsafe void InsertNext(UnusedBlockHeader *header,
                                                   UnusedBlockHeader *newNext)
            {
                //Trace.Log(Trace.Area.Page,
                //          "UnusedBlockHeader.InsertNext {0} count={1}",
                //          __arglist(newNext, newNext->count));
                UnusedBlockHeader *oldNext = header->next;
                header->next = newNext;
                newNext->next = oldNext;
                newNext->prev = header;
                if (oldNext != null) {
                    oldNext->prev = newNext;
                }
                UnusedBlockHeader.Verify(newNext);
            }

            internal static unsafe UIntPtr Remove(UnusedBlockHeader *header)
            {
                //Trace.Log(Trace.Area.Page,
                //          "UnusedBlockHeader.Remove {0} count={1}",
                //          __arglist(this.prev->next, this.count));
                UnusedBlockHeader.Verify(header);
                header->prev->next = header->next;
                if (header->next != null) {
                    header->next->prev = header->prev;
                }
                UIntPtr result = header->count;
                header->magic = UIntPtr.Zero;
                header->prev = null;
                header->next = null;
                header->count = UIntPtr.Zero;
                UnusedBlockHeader *tailBlock = (UnusedBlockHeader *)
                    (((UIntPtr) header)  + PageTable.RegionSize(result - 1));
                tailBlock->curr = null;
                return result;
            }

        }

        [NoBarriers]
        [PreInitRefCounts]
        internal static void Initialize(UIntPtr os_commit_size,
                                        UIntPtr heap_commit_size)
        {
            PageManager.os_commit_size = os_commit_size;
            PageManager.heap_commit_size = heap_commit_size;
            // unusedMemoryBlocks = new UnusedBlockHeader [32]
            unusedMemoryBlocks = (UnusedBlockHeader[])
                BootstrapMemory.Allocate(typeof(UnusedBlockHeader[]), 32);
            // outOfMemoryException = new OutOfMemoryException();
            outOfMemoryException = (OutOfMemoryException)
                BootstrapMemory.Allocate(typeof(OutOfMemoryException));
#if SINGULARITY_KERNEL
#if USE_SPINLOCK
            Lock = new SpinLock(SpinLock.Types.PageManager);
#endif
            avoidDirtyPages = true;
#else
            avoidDirtyPages = false;
#endif
        }

        internal static void FinishInitializeThread()
        {
#if USE_MUTEX
            mutex = new Mutex();
            GC.SuppressFinalize(mutex);
#endif
        }

        private static bool EnterMutex(Thread currentThread) {
            bool iflag = false;
            if (currentThread != null
#if !SINGULARITY || SEMISPACE_COLLECTOR || SLIDING_COLLECTOR || ADAPTIVE_COPYING_COLLECTOR || MARK_SWEEP_COLLECTOR
                &&
                StopTheWorldGCData.CurrentPhase !=
                StopTheWorldPhase.SingleThreaded
#endif
                ) {
#if SINGULARITY_KERNEL
                iflag = Processor.DisableInterrupts();
#endif // SINGULARITY_KERNEL
#if USE_MUTEX
                if (mutex != null) {
                    mutex.AcquireMutex();
                }
#elif USE_SPINLOCK
                PageManager.Lock.Acquire(currentThread);
#endif
            }
            return iflag;
        }

        private static void LeaveMutex(Thread currentThread, bool iflag) {
            if (currentThread != null
#if !SINGULARITY || SEMISPACE_COLLECTOR || SLIDING_COLLECTOR || ADAPTIVE_COPYING_COLLECTOR || MARK_SWEEP_COLLECTOR
                &&
                StopTheWorldGCData.CurrentPhase !=
                StopTheWorldPhase.SingleThreaded
#endif
                ) {
#if USE_MUTEX
                if (mutex != null) {
                    mutex.ReleaseMutex();
                }
#elif USE_SPINLOCK
                PageManager.Lock.Release(currentThread);
#endif

#if SINGULARITY_KERNEL
                // Must happen after spinlock is released
                Processor.RestoreInterrupts(iflag);
#endif // SINGULARITY_KERNEL
            }
        }

        [ManualRefCounts]
        private static void Clear(UIntPtr startAddr,
                                  UIntPtr regionSize)
        {
            VTable.Assert(PageTable.PageAligned(startAddr));
            VTable.Assert(PageTable.PageAligned(regionSize));
            MemoryManager.IgnoreMemoryContents(startAddr, regionSize);
            MarkUnusedPages(Thread.CurrentThread,
                            PageTable.Page(startAddr),
                            PageTable.PageCount(regionSize),
                            false);
        }

        private static int SlotFromCount(UIntPtr count) {
            int slot = -1;
            do {
                slot++;
                count >>= 1;
            } while (count > UIntPtr.Zero);
            return slot;
        }

        internal static UIntPtr AllocateNonheapMemory(Thread currentThread,
                                                      UIntPtr size)
        {
            bool iflag = EnterMutex(currentThread);
            try {
                UIntPtr result = MemoryManager.AllocateMemory(size);
                if (result != UIntPtr.Zero) {
                    SetNonheapPages(result, size);
                }
                return result;
            } finally {
                LeaveMutex(currentThread, iflag);
            }
        }

        internal static void FreeNonheapMemory(UIntPtr startAddress,
                                               UIntPtr size)
        {
            SetUnallocatedPages(startAddress, size);
            MemoryManager.FreeMemory(startAddress, size);
        }

        private static void SetPageTypeClean(UIntPtr startPage,
                                             UIntPtr pageCount,
                                             PageType newType)
        {
            UIntPtr* tableAddr = (UIntPtr *) PageTable.PageAddr(startPage);
            UIntPtr* tableCursor = tableAddr + 1;
            UIntPtr dirtyCount = UIntPtr.Zero;
            UIntPtr endPage = startPage + pageCount;
            for (UIntPtr i = startPage; i < endPage; i++) {
                PageType pageType = PageTable.Type(i);
                if (pageType == PageType.UnusedDirty) {
                    PageTable.SetType(i, newType);
                    UIntPtr j = i+1;
                    while (j < endPage &&
                           PageTable.Type(j)==PageType.UnusedDirty) {
                        PageTable.SetType(j, newType);
                        j++;
                    }
                    UIntPtr dirtyStartAddr = PageTable.PageAddr(i);
                    UIntPtr dirtyEndAddr = PageTable.PageAddr(j);
                    *tableCursor++ = dirtyStartAddr;
                    *tableCursor++ = dirtyEndAddr - dirtyStartAddr;
                    dirtyCount++;
                    i = j-1;
                } else {
                    PageTable.SetType(i, newType);
                }
            }
            *tableAddr = dirtyCount;
            PageTable.SetProcess(startPage, pageCount);
        }

        [ManualRefCounts]
        internal static UIntPtr EnsurePages(Thread currentThread,
                                            UIntPtr pageCount,
                                            PageType newType,
                                            ref bool fCleanPages)
        {
            if (currentThread != null) {
                GC.CheckForNeededGCWork(currentThread);
            }
            VTable.Deny(PageTable.IsUnusedPageType(newType));
            // Try to find already allocated but unused pages
            UIntPtr foundPages =
                FindUnusedPages(currentThread, pageCount, newType);
            if (foundPages != UIntPtr.Zero) {
                if (fCleanPages) {
                    CleanFoundPages(foundPages);
                } else {
                    fCleanPages = FoundOnlyCleanPages(foundPages);
                }
                return foundPages;
            }
            // We need to allocate new pages
            bool iflag = EnterMutex(currentThread);
            try {
                UIntPtr bytesNeeded = PageTable.RegionSize(pageCount);
                UIntPtr allocSize = Util.Pad(bytesNeeded, heap_commit_size);
                UIntPtr startAddr = MemoryManager.AllocateMemory(allocSize);
                if (startAddr == UIntPtr.Zero) {
                    if (heap_commit_size > os_commit_size) {
                        allocSize = Util.Pad(bytesNeeded, os_commit_size);
                        startAddr = MemoryManager.AllocateMemory(allocSize);
                    }
                }
                if (startAddr == UIntPtr.Zero) {
                    // BUGBUG: if in CMS, should wait on one complete GC cycle and
                    // the retry.  for STW, we may get here even if the collector
                    // hasn't triggered just prior.
                    PageTable.Dump("Out of memory");
                    throw outOfMemoryException;
                }
                UIntPtr startPage = PageTable.Page(startAddr);
                PageTable.SetType(startPage, pageCount, newType);
                PageTable.SetProcess(startPage, pageCount);
                UIntPtr extraPages =
                    PageTable.PageCount(allocSize) - pageCount;
                if (extraPages > 0) {
                    // Mark the new memory pages as allocated-but-unused
                    MarkUnusedPages(/* avoid recursive locking */ null,
                                    startPage+pageCount, extraPages,
                                    true);
                }
                return startPage;
            } finally {
                LeaveMutex(currentThread, iflag);
            }
        }

        internal static void ReleaseUnusedPages(UIntPtr startPage,
                                                UIntPtr pageCount,
                                                bool fCleanPages)
        {
            if(VTable.enableDebugPrint) {
                VTable.DebugPrint("ClearPages({0}, {1})\n",
                                  __arglist(startPage, pageCount));
            }
            UIntPtr startAddr = PageTable.PageAddr(startPage);
            UIntPtr endPage = startPage + pageCount;
            UIntPtr endAddr = PageTable.PageAddr(endPage);
            UIntPtr rangeSize = PageTable.RegionSize(pageCount);

            MarkUnusedPages(Thread.CurrentThread,
                            PageTable.Page(startAddr),
                            PageTable.PageCount(rangeSize),
                            fCleanPages);

            if (PageManager.AggressiveMemReset) {
                // We cannot simply reset the memory range, as MEM_RESET can
                // only be used within a region returned from a single
                // VirtualAlloc call.
                UIntPtr regionAddr, regionSize;
                bool fUsed = MemoryManager.QueryMemory(startAddr,
                                                       out regionAddr,
                                                       out regionSize);
                if(VTable.enableDebugPrint) {
                    VTable.DebugPrint(" 1 Query({0}, {1}, {2}) -> {3}\n",
                                      __arglist(startAddr, regionAddr,
                                                regionSize, fUsed));
                }
                VTable.Assert(fUsed, "Memory to be cleared isn't used");
                // We don't care if regionAddr < startAddr.  We can MEM_RESET
                // part of the region.

                UIntPtr endRegion = regionAddr + regionSize;
                while (endRegion < endAddr) {
                    if (VTable.enableDebugPrint) {
                        VTable.DebugPrint("Clearing region [{0}, {1}]\n",
                                          __arglist(regionAddr,
                                                    regionAddr+regionSize));
                    }
                    MemoryManager.IgnoreMemoryContents(startAddr,
                                                       endRegion - startAddr);
                    startAddr = endRegion;
                    fUsed = MemoryManager.QueryMemory(endRegion,
                                                      out regionAddr,
                                                      out regionSize);
                    if(VTable.enableDebugPrint) {
                        VTable.DebugPrint(" 2 Query({0}, {1}, {2}) -> {3}\n",
                                          __arglist(endRegion, regionAddr,
                                                    regionSize, fUsed));
                    }
                    VTable.Assert(fUsed, "Region to be freed isn't used");
                    endRegion = regionAddr + regionSize;
                }
                if (VTable.enableDebugPrint) {
                    VTable.DebugPrint("Clearing final region [{0}, {1}]\n",
                                      __arglist(startAddr, endAddr));
                }
                MemoryManager.IgnoreMemoryContents(startAddr,
                                                   endAddr - startAddr);
            }
            if(VTable.enableDebugPrint) {
                VTable.DebugPrint("  --> ClearPages({0},{1})\n",
                                  __arglist(startPage, pageCount));
            }
        }

        // Use this method to free heap pages.
        // There must be no contention regarding ownership of the pages.
        internal static void FreePageRange(UIntPtr startPage,
                                           UIntPtr endPage)
        {
            if(VTable.enableDebugPrint) {
                VTable.DebugPrint("FreePageRange({0}, {1})\n",
                                  __arglist(startPage, endPage));
            }
            UIntPtr startAddr = PageTable.PageAddr(startPage);
            UIntPtr endAddr = PageTable.PageAddr(endPage);
            UIntPtr rangeSize = endAddr - startAddr;
#if SINGULARITY
            // Singularity doesn't care if you free pages in different
            // chunks than you acquired them in
            MemoryManager.FreeMemory(startAddr, rangeSize);
#else
            // We cannot simply release the memory range, as MEM_RELEASE
            // requires the pointer to be the same as the original call
            // to VirtualAlloc, and the length to be zero.
            UIntPtr regionAddr, regionSize;
            bool fUsed = MemoryManager.QueryMemory(startAddr,
                                                   out regionAddr,
                                                   out regionSize);
            if(VTable.enableDebugPrint) {
                VTable.DebugPrint(" 1 Query({0}, {1}, {2}) -> {3}\n",
                                  __arglist(startAddr, regionAddr,
                                            regionSize, fUsed));
            }
            VTable.Assert(fUsed, "Memory to be freed isn't used");
            UIntPtr endRegion = regionAddr + regionSize;
            if (regionAddr < startAddr) {
                // startAddr is in the middle of an allocation region -> skip
                if (endRegion >= endAddr) {
                    // [startAddr, endAddr] is fully contained in a region
                    PageManager.Clear(startAddr, endAddr - startAddr);
                    return;
                }
                // Part of the address range falls into the next region
                PageManager.Clear(startAddr, endRegion - startAddr);
                fUsed = MemoryManager.QueryMemory(endRegion,
                                                  out regionAddr,
                                                  out regionSize);
                if(VTable.enableDebugPrint) {
                    VTable.DebugPrint(" 2 Query({0}, {1}, {2}) -> {3}\n",
                                      __arglist(endRegion, regionAddr,
                                                regionSize, fUsed));
                }
                VTable.Assert(fUsed, "Area to be freed isn't used");
                endRegion = regionAddr + regionSize;
            }
            // [regionAddr, endRegion] is contained in [startAddr, endAddr]
            while (endRegion < endAddr) {
                if (VTable.enableDebugPrint) {
                    VTable.DebugPrint("Freeing region [{0}, {1}]\n",
                                      __arglist(regionAddr,
                                                regionAddr+regionSize));
                }
                SetUnallocatedPages(regionAddr, regionSize);
                MemoryManager.FreeMemory(regionAddr, regionSize);
                fUsed = MemoryManager.QueryMemory(endRegion,
                                                  out regionAddr,
                                                  out regionSize);
                if(VTable.enableDebugPrint) {
                    VTable.DebugPrint(" 3 Query({0}, {1}, {2}) -> {3}\n",
                                      __arglist(endRegion, regionAddr,
                                                regionSize, fUsed));
                }
                VTable.Assert(fUsed, "Region to be freed isn't used");
                endRegion = regionAddr + regionSize;
            }
            if (endRegion == endAddr) {
                if (VTable.enableDebugPrint) {
                    VTable.DebugPrint("Freeing final region [{0}, {1}]\n",
                                      __arglist(regionAddr,
                                                regionAddr + regionSize));
                }
                SetUnallocatedPages(regionAddr, regionSize);
                MemoryManager.FreeMemory(regionAddr, regionSize);
            } else {
                PageManager.Clear(regionAddr, endAddr - regionAddr);
            }
            if(VTable.enableDebugPrint) {
                VTable.DebugPrint("  --> FreePageRange({0},{1})\n",
                                  __arglist(startPage, endPage));
            }
#endif // SINGULARITY
        }

        //===============================
        // Routines to mark special pages

        private static unsafe void SetNonheapPages(UIntPtr startAddr,
                                                    UIntPtr size)
        {
            UIntPtr startPage = PageTable.Page(startAddr);
            UIntPtr endAddr = startAddr + size;
            UIntPtr endPage = PageTable.Page(endAddr);
            if (!PageTable.PageAligned(endAddr)) {
                endPage++;
            }
            UIntPtr pageCount = endPage - startPage;
            if (pageCount == 1) {
                PageTable.SetType(startPage, PageType.System);
            } else {
                PageTable.SetType(startPage, pageCount, PageType.System);
            }
        }

        // Tell the GC that a certain data area is no longer allowed to
        // contain off-limits, non-moveable data.
        private static unsafe void SetUnallocatedPages(UIntPtr startAddr,
                                                       UIntPtr size)
        {
            UIntPtr startPage = PageTable.Page(startAddr);
            UIntPtr endAddr = startAddr + size;
            UIntPtr endPage = PageTable.Page(endAddr);
            UIntPtr pageCount = endPage - startPage;
            if (pageCount == 1) {
                PageTable.SetExtra(startPage, 0);
                PageTable.SetType(startPage, PageType.Unallocated);
                PageTable.SetProcess(startPage, 0);
            } else {
                PageTable.SetExtra(startPage, pageCount, 0);
                PageTable.SetType(startPage, pageCount, PageType.Unallocated);
                PageTable.SetProcess(startPage, pageCount, 0);
            }
        }

#if !SINGULARITY                // Needed before Bartok runtime is initialized
        [NoStackLinkCheck]
#endif
        internal static unsafe void SetStaticDataPages(UIntPtr startAddr,
                                                       UIntPtr size)
        {
            
#if SINGULARITY
            // It's perfectly fine to be given memory outside the page table region, so
            // long as we intend to treat that memory as NonGC anyway.
            if (startAddr < PageTable.baseAddr)
            {
                if (startAddr + size < PageTable.baseAddr)
                {
                    // nothing to do.  All pages are below the base covered by the page table
                    return;
                }
                // The range overlaps with the region covered by the page table
                size -= (PageTable.baseAddr - startAddr);
                startAddr = PageTable.baseAddr;
            }
            UIntPtr endAddr = startAddr + size;
            if (endAddr > PageTable.limitAddr)
            {
                if (startAddr > PageTable.limitAddr)
                {
                    // nothing to do.  All pages are above the limit covered by the page table
                    return;
                }
                // The range overlaps with the region covered by the page table
                size -= (PageTable.limitAddr - endAddr);
            }
#endif
            
            UIntPtr startIndex = PageTable.Page(startAddr);
            UIntPtr pageCount = PageTable.PageCount(size);

            PageTable.SetType(startIndex, pageCount, PageType.NonGC);
        }

#if !SINGULARITY
        // Bartok uses the extra field in the PageTable to easily
        // map from a stack address to the thread that owns that stack.
        // This is used to implement GetCurrentThread.
        // Singularity uses a different mechanism that does not involve
        // the extra data at all.

        private static unsafe void SetStackPages(UIntPtr startAddr,
                                                 UIntPtr endAddr,
                                                 Thread thread)
        {
            UIntPtr startPage = PageTable.Page(startAddr);
            UIntPtr endPage = PageTable.Page(endAddr);
            UIntPtr pageCount = endPage - startPage;
            PageTable.VerifyType(startPage, pageCount, PageType.Unallocated);
            PageTable.VerifyExtra(startPage, pageCount, 0);
            PageTable.SetType(startPage, pageCount, PageType.Stack);
            PageTable.SetExtra(startPage, pageCount,
                               (uint) thread.threadIndex);
        }

        internal static unsafe void MarkThreadStack(Thread thread) {
            int stackVariable;
            UIntPtr stackBase = PageTable.PagePad(new UIntPtr(&stackVariable));
            CallStack.SetStackBase(thread, stackBase);
            UIntPtr topPageAddr =
                PageTable.PageAlign(CallStack.StackBase(thread) - 1);
            SetStackPages(topPageAddr, CallStack.StackBase(thread), thread);
            UIntPtr regionAddr, regionSize;
            bool fUsed = MemoryManager.QueryMemory(topPageAddr,
                                                   out regionAddr,
                                                   out regionSize);
            VTable.Assert(fUsed);
            SetStackPages(regionAddr, topPageAddr, thread);
        }

        internal static unsafe void ClearThreadStack(Thread thread) {
            short threadIndex = (short) thread.threadIndex;
            UIntPtr endPage = PageTable.Page(CallStack.StackBase(thread));
            UIntPtr startPage = endPage - 1;
            VTable.Assert(PageTable.IsStackPage(PageTable.Type(startPage)));
            VTable.Assert(PageTable.Extra(startPage) == threadIndex);
            while (startPage > 0 &&
                   PageTable.IsStackPage(PageTable.Type(startPage-1)) &&
                   PageTable.Extra(startPage-1) == threadIndex) {
                startPage--;
            }
            UIntPtr startAddr = PageTable.PageAddr(startPage);
            UIntPtr size = PageTable.RegionSize(endPage - startPage);
            SetUnallocatedPages(startAddr, size);
        }
#endif

        //====================================
        // Routines to manipulate unused pages

        [ManualRefCounts]
        private static void LinkUnusedPages(UIntPtr startPage,
                                            UIntPtr pageCount,
                                            bool asVictim)
        {
            if (PageManager.SlowDebug) {
                for (UIntPtr i = startPage; i < startPage + pageCount; i++) {
                    VTable.Assert(PageTable.IsUnusedPage(i) &&
                                  PageTable.IsMyPage(i),
                                  "Incorrect page to link into unused region");
                }
            }
            Trace.Log(Trace.Area.Page,
                      "LinkUnusedPages start={0:x} count={1:x}",
                      __arglist(startPage, pageCount));
            VTable.Deny(startPage > UIntPtr.Zero &&
                        PageTable.IsUnusedPage(startPage-1) &&
                        PageTable.IsMyPage(startPage-1));
            VTable.Deny(startPage + pageCount > PageTable.pageTableCount);
            VTable.Deny(startPage + pageCount < PageTable.pageTableCount &&
                        PageTable.IsUnusedPage(startPage + pageCount) &&
                        PageTable.IsMyPage(startPage + pageCount));
            UnusedBlockHeader *header = (UnusedBlockHeader *)
                PageTable.PageAddr(startPage);
            UnusedBlockHeader.Initialize(header, pageCount);
            int slot = SlotFromCount(pageCount);

            // Unused blocks are linked into the free list either as the result of a collection
            // or as a result of carving a big block into a smaller allocation and a remainder.
            // When such a remainder is linked back into the free list, it is identified as a
            // victim.  We favor subsequent allocations from these victims, in an attempt to
            // reduce fragmentation.  This is achieved by keeping victims at the head of the
            // free list.
            //
            // TODO: the long term solution is to perform best fit on the free list.
            if (asVictim || unusedMemoryBlocks[slot].next == null) {
                fixed (UnusedBlockHeader *listHeader = &unusedMemoryBlocks[slot]) {
                    UnusedBlockHeader.InsertNext(listHeader, header);
                }
            }
            else {
                UnusedBlockHeader *listHeader = unusedMemoryBlocks[slot].next;
                UnusedBlockHeader.InsertNext(listHeader, header);
            }
        }

        private static UIntPtr UnlinkUnusedPages(UIntPtr startPage)
        {
            VTable.Assert(PageTable.IsUnusedPage(startPage) &&
                          PageTable.IsMyPage(startPage));
            VTable.Deny(startPage > UIntPtr.Zero &&
                        PageTable.IsUnusedPage(startPage-1) &&
                        PageTable.IsMyPage(startPage-1));
            UnusedBlockHeader *header = (UnusedBlockHeader *)
                PageTable.PageAddr(startPage);
            UIntPtr pageCount = UnusedBlockHeader.Remove(header);
            Trace.Log(Trace.Area.Page,
                      "UnlinkUnusedPages start={0:x} count={1:x}",
                      __arglist(startPage, pageCount));
            return pageCount;
        }

        // The indicated pages will be marked with 'pageStatus' in the
        // page table.  The region of unused memory will also be linked
        // into the table of blocks of unused memory
        [ManualRefCounts]
        private static void MarkUnusedPages(Thread currentThread,
                                            UIntPtr startPage,
                                            UIntPtr pageCount,
                                            bool fCleanPages)
        {
            Trace.Log(Trace.Area.Page,
                      "MarkUnusedPages start={0:x} count={1:x}",
                      __arglist(startPage, pageCount));
            UIntPtr endPage = startPage + pageCount;
            if (avoidDirtyPages && !fCleanPages) {
                UIntPtr dirtyStartAddr = PageTable.PageAddr(startPage);
                UIntPtr dirtySize = PageTable.RegionSize(pageCount);
                Util.MemClear(dirtyStartAddr, dirtySize);
                fCleanPages = true;
            }
            bool iflag = EnterMutex(currentThread);
            try {
                if (endPage < PageTable.pageTableCount) {
                    if (PageTable.IsUnusedPage(endPage) &&
                        PageTable.IsMyPage(endPage)) {
                        UIntPtr regionSize = UnlinkUnusedPages(endPage);
                        endPage += regionSize;
                    }
                }

                UIntPtr queryStartPage = startPage - 1;
                UIntPtr newStartPage = startPage;
                if (PageTable.IsUnusedPage(queryStartPage) &&
                    PageTable.IsMyPage(queryStartPage)) {
                    UnusedBlockHeader * tailUnused = (UnusedBlockHeader *)
                        PageTable.PageAddr(queryStartPage);
                    UIntPtr newStartAddr = (UIntPtr) tailUnused->curr;
                    newStartPage = PageTable.Page(newStartAddr);
                    UIntPtr regionSize = UnlinkUnusedPages(newStartPage);
                    VTable.Assert(newStartPage + regionSize == startPage);
                }

                PageType pageType =
                    fCleanPages ? PageType.UnusedClean : PageType.UnusedDirty;
                PageTable.SetType(startPage, pageCount, pageType);
                LinkUnusedPages(newStartPage, endPage - newStartPage, false);
            } finally {
                LeaveMutex(currentThread, iflag);
            }
        }

        internal static bool TryReserveUnusedPages(Thread currentThread,
                                                   UIntPtr startPage,
                                                   UIntPtr pageCount,
                                                   PageType newType,
                                                   ref bool fCleanPages)
        {
            Trace.Log(Trace.Area.Page,
                      "TryReserveUnusedPages start={0:x} count={1:x}",
                      __arglist(startPage, pageCount));
            VTable.Deny(PageTable.IsUnusedPageType(newType));
            VTable.Assert(pageCount > UIntPtr.Zero);
            VTable.Deny(startPage != UIntPtr.Zero &&
                        PageTable.IsUnusedPage(startPage-1) &&
                        PageTable.IsMyPage(startPage-1));
            UIntPtr endPage = startPage + pageCount;
            if (endPage > PageTable.pageTableCount) {
                return false;
            }
            if (currentThread != null) {
                GC.CheckForNeededGCWork(currentThread);
            }
            bool iflag = EnterMutex(currentThread);
            try {
                // GC can occur and page can be collected.
                if (startPage != UIntPtr.Zero &&
                    PageTable.IsUnusedPage(startPage-1)) {
                    return false;
                }

                if (!PageTable.IsUnusedPage(startPage)
                    || !PageTable.IsMyPage(startPage)) {
                    return false;
                }

                UnusedBlockHeader * header = (UnusedBlockHeader *)
                    PageTable.PageAddr(startPage);

                if (header->count < pageCount) {
                    return false;
                }

                UIntPtr regionPages = UnlinkUnusedPages(startPage);
                Trace.Log(Trace.Area.Page,
                          "TryReserveUnusedPages found={0:x}",
                          __arglist(regionPages));

                SetPageTypeClean(startPage, pageCount, newType);
                if (regionPages > pageCount) {
                    UIntPtr suffixPages = regionPages - pageCount;
                    LinkUnusedPages(endPage, suffixPages, true);
                }
            } finally {
                LeaveMutex(currentThread, iflag);
            }
            // Now that we are outside the Mutex, we should perform the
            // real cleaning of the gotten pages
            if (fCleanPages) {
                CleanFoundPages(startPage);
            } else {
                fCleanPages = FoundOnlyCleanPages(startPage);
            }
            return true;
        }

        internal static bool TryReservePages(Thread currentThread,
                                             UIntPtr startPage,
                                             UIntPtr pageCount,
                                             PageType newType,
                                             ref bool fCleanPages)
        {
            Trace.Log(Trace.Area.Page,
                      "TryReservePages start={0:x} count={1:x}",
                      __arglist(startPage, pageCount));
            VTable.Deny(PageTable.IsUnusedPageType(newType));
            VTable.Assert(pageCount > UIntPtr.Zero);
            VTable.Deny(startPage != UIntPtr.Zero &&
                        PageTable.IsUnusedPage(startPage-1) &&
                        PageTable.IsMyPage(startPage-1));
            UIntPtr endPage = startPage + pageCount;
            UIntPtr index = startPage;
            while (index < endPage &&
                   PageTable.IsUnusedPage(index) &&
                   PageTable.IsMyPage(index)) {
                index++;
            }
            if (PageTable.IsUnallocatedPage(PageTable.Type(index))) {
                // We should try to extend the region of allocated pages
                UIntPtr pagesNeeded = pageCount - (index - startPage);
                UIntPtr bytesNeeded = PageTable.RegionSize(pagesNeeded);
                UIntPtr allocSize = Util.Pad(bytesNeeded, heap_commit_size);
                UIntPtr startAddr = PageTable.PageAddr(index);
                bool gotMemory = false;
                bool iflag = EnterMutex(currentThread);
                try {
                    gotMemory =
                        MemoryManager.AllocateMemory(startAddr, allocSize);
                    if (gotMemory) {
                        UIntPtr allocPages = PageTable.PageCount(allocSize);
                        MarkUnusedPages(/* avoid recursive locking */ null,
                                        index, allocPages, true);
                    }
                } finally {
                    LeaveMutex(currentThread, iflag);
                }
                if (gotMemory) {
                    bool success =
                        TryReserveUnusedPages(currentThread, startPage,
                                              pageCount, newType,
                                              ref fCleanPages);
                    Trace.Log(Trace.Area.Page,
                              "TryReservePages success={0}",
                              __arglist(success));
                    return success;
                }
            }
            return false;
        }

        // Try to find a region of unused memory of a given size.  If the
        // request can be satisfied, the return value is the first page
        // in the found region.  If the request cannot be satisfied, the
        // return value is UIntPtr.Zero.
        [ManualRefCounts]
        private static UIntPtr FindUnusedPages(Thread currentThread,
                                               UIntPtr pageCount,
                                               PageType newType)
        {
            VTable.Deny(PageTable.IsUnusedPageType(newType));
            int slot = SlotFromCount(pageCount);
            Trace.Log(Trace.Area.Page,
                      "FindUnusedPages count={0:x} slot={1}",
                      __arglist(pageCount, slot));
            bool iflag = EnterMutex(currentThread);
            try {
                while (slot < 32) {
                    UnusedBlockHeader *header = unusedMemoryBlocks[slot].next;
                    while (header != null) {
                        if (header->count >= pageCount) {
                            UIntPtr startPage =
                                PageTable.Page((UIntPtr) header);
                            UIntPtr regionSize = UnlinkUnusedPages(startPage);
                            SetPageTypeClean(startPage, pageCount, newType);
                            if (regionSize > pageCount) {
                                UIntPtr restCount = regionSize - pageCount;
                                UIntPtr endPage = startPage + pageCount;
                                LinkUnusedPages(endPage, restCount, true);
                            }
                            Trace.Log(Trace.Area.Page,
                                      "FindUnusedPages success {0:x}",
                                      __arglist(startPage));
                            return startPage;
                        }
                        header = header->next;
                    }
                    slot++;
                }
                return UIntPtr.Zero;
            } finally {
                LeaveMutex(currentThread, iflag);
            }
        }

        [ManualRefCounts]
        private static void CleanFoundPages(UIntPtr startPage)
        {
            UIntPtr *tableAddr = (UIntPtr *) PageTable.PageAddr(startPage);
            uint count = (uint) *tableAddr;
            UIntPtr* cursor = tableAddr + (count + count);
            while (count != 0) {
                UIntPtr dirtySize = *cursor;
                *cursor-- = UIntPtr.Zero;
                UIntPtr dirtyStartAddr = *cursor;
                *cursor-- = UIntPtr.Zero;
                Util.MemClear(dirtyStartAddr, dirtySize);
                count--;
            }
            *tableAddr = UIntPtr.Zero;
        }

        [ManualRefCounts]
        private static bool FoundOnlyCleanPages(UIntPtr startPage)
        {
            UIntPtr *tableAddr = (UIntPtr *) PageTable.PageAddr(startPage);
            uint count = (uint) *tableAddr;
            UIntPtr* cursor = tableAddr + (count + count);
            bool result = true;
            while (count != 0) {
                result = false;
                *cursor-- = UIntPtr.Zero;
                *cursor-- = UIntPtr.Zero;
                count--;
            }
            *tableAddr = UIntPtr.Zero;
            return result;
        }

        [ManualRefCounts]
        internal static UIntPtr TotalUnusedPages() {
            Thread currentThread = Thread.CurrentThread;
            UIntPtr pageCount = (UIntPtr) 0;
            bool iflag = EnterMutex(currentThread);
            try {
                for (int slot = 0; slot < 32; slot++) {
                    UnusedBlockHeader *header = unusedMemoryBlocks[slot].next;
                    while (header != null) {
                        pageCount += header->count;
                        header = header->next;
                    }
                }
                return pageCount;
            } finally {
                LeaveMutex(currentThread, iflag);
            }
        }

        [System.Diagnostics.Conditional("DEBUG")]
        internal static void VerifyUnusedPage(UIntPtr page, bool containsHeader)
        {
            if (PageTable.Type(page) == PageType.UnusedDirty) {
                return;
            }

            // Verify that the page is indeed clean

            UIntPtr *startAddr = (UIntPtr *) PageTable.PageAddr(page);
            UIntPtr *endAddr = (UIntPtr *) PageTable.PageAddr(page + 1);

            // If the page contains a header then we can't expect the header
            // to be clean.
            if (containsHeader)
            {
                startAddr += (uint)
                    (Util.UIntPtrPad((UIntPtr)sizeof(UnusedBlockHeader))
                     / (uint)sizeof(UIntPtr));
            }

            while (startAddr < endAddr) {
                VTable.Assert(*startAddr == UIntPtr.Zero,
                              "UnusedClean page contains nonzero data");
                startAddr++;
            }
        }

        [System.Diagnostics.Conditional("DEBUG")]
        internal static void VerifyUnusedRegion(UIntPtr startPage,
                                                UIntPtr endPage)
        {
            // Verify that all of the pages are of the same Clean/Dirty type.
            PageType startType = PageTable.Type(startPage);
            for(UIntPtr page = startPage; page < endPage; ++page) {
                VTable.Assert(startType == PageTable.Type(page),
                              "Unused page types don't match in region");
            }

            if (startPage > UIntPtr.Zero &&
                PageTable.IsUnusedPage(startPage-1) &&
                PageTable.IsMyPage(startPage-1)) {
                // We have already checked the region
                return;
            }

            UIntPtr regionAddr = PageTable.PageAddr(startPage);
            UnusedBlockHeader * regionHeader = (UnusedBlockHeader *) regionAddr;
            UIntPtr pageCount = regionHeader->count;
            VTable.Assert
                (pageCount >= (endPage - startPage),
                 "Region-to-verify is larger than its header specifies");

            endPage = startPage + pageCount;

            for(UIntPtr page = startPage; page < endPage; ++page) {
                VTable.Assert(PageTable.IsUnusedPage(page) &&
                              PageTable.IsMyPage(page),
                              "Non my-unused page in unused region");

                PageManager.VerifyUnusedPage
                    (page, (page == startPage) || (page == (endPage - 1)));
            }

            VTable.Assert(!(endPage < PageTable.pageTableCount &&
                            PageTable.IsUnusedPage(endPage) &&
                            PageTable.IsMyPage(endPage)),
                          "My-unused page immediately after unused region");

            // Verify that the region is correctly linked into the
            // list of unused memory blocks
            int slot = SlotFromCount(pageCount);
            UnusedBlockHeader *header = unusedMemoryBlocks[slot].next;
            UnusedBlockHeader.Verify(header);
            while (regionAddr != (UIntPtr) header) {
                header = header->next;
                VTable.Assert(header != null,
                              "Unused region not list for its slot number");
                UnusedBlockHeader.Verify(header);
            }
        }

    }

}
