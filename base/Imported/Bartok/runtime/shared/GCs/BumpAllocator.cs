//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


// Conceptually, even if nothing is recorded in the offset table
// during object allocation, the offset table itself should be
// able to identify objects correctly in the execution. So as
// a stress mode to test the correctness of the offset table,
// here we can turn on the following macro to disable recording
// object allocation in the offset table.

//#define DONT_RECORD_OBJALLOC_IN_OFFSETTABLE

#define ENSURE_ALLOCATION_ALLOWED

namespace System.GCs {

    using System.Runtime.CompilerServices;
    using System.Threading;

    using Microsoft.Bartok.Options;
    using Microsoft.Bartok.Runtime;
#if SINGULARITY
    using Microsoft.Singularity;
#endif

    // Common struct for allocation pool.
    [NoCCtor]
    internal struct BumpAllocator /* : Allocator */
    {

        [RequiredByBartok]
        private UIntPtr           allocPtr; // Next allocation.
        [RequiredByBartok]
        private UIntPtr           zeroedLimit; // Limit of zeroed pool.
        private UIntPtr           reserveLimit; // Limit of reserved pool.
        private UIntPtr           allocNew; // Most recent page allocation.
        private readonly PageType pageType;

        [MixinOverride]
        private static bool CLEAR_POOL_PAGES() {
            VTable.DebugBreak();
            return false;
        }

        [MixinConditional("BumpAllocator")]
        [MixinConditional("AllThreadMixins")]
        [Mixin(typeof(Thread))]
        // Should be private, but mixin implementation will warn if visibility
        // does not match that of Thread.
        public sealed class BumpAllocatorThread : Object {
            // Thread-specific bump allocator
            [RequiredByBartok]
            internal BumpAllocator bumpAllocator;
        }

        [Inline]
        private static BumpAllocatorThread MixinThread(Thread t)
        {
            return (BumpAllocatorThread) (Object) t;
        }

        internal BumpAllocator(PageType pageType) {
            this.zeroedLimit = UIntPtr.Zero;
            this.reserveLimit = UIntPtr.Zero;
            this.allocPtr = UIntPtr.Zero;
            this.allocNew = UIntPtr.Zero;
            this.pageType = pageType;
        }

        internal void SetReservedRange(UIntPtr startAddr, UIntPtr length) {
            this.allocPtr = startAddr;
            this.reserveLimit = startAddr + length;
        }

        internal void SetZeroedRange(UIntPtr startAddr, UIntPtr length) {
            this.allocPtr = startAddr;
            this.zeroedLimit = startAddr + length;
            this.reserveLimit = startAddr + length;
        }

        internal void SetZeroedLimit(UIntPtr zeroedLimit) {
            this.zeroedLimit = zeroedLimit;
        }

        internal UIntPtr AllocPtr {
            get { return this.allocPtr; }
        }

        internal UIntPtr ZeroedLimit {
            get { return this.zeroedLimit; }
        }

        internal UIntPtr ReserveLimit {
            get { return this.reserveLimit; }
        }

        internal UIntPtr AllocNew {
            get { return this.allocNew; }
        }

        internal void Dump()
        {
#if SINGULARITY
            Tracing.Log(Tracing.Debug, "[gen={0} {1:x8}..{2:x8}..{3:x8}]",
                        (UIntPtr)unchecked((uint)this.pageType),
                        this.allocPtr, this.zeroedLimit, this.reserveLimit);
#else
            VTable.DebugPrint(" [gen={0} {1:x8}..{2:x8}..{3:x8}]\n",
                              __arglist(this.pageType, this.allocPtr,
                                        this.zeroedLimit, this.reserveLimit));
#endif
        }

        internal static void NewThreadNotification(Thread newThread,
                                                   PageType pageType)
        {
            MixinThread(newThread).bumpAllocator = new BumpAllocator(pageType);
        }

        [ManualRefCounts]
        public static UIntPtr Allocate(Thread thread,
                                       UIntPtr bytes, uint alignment)
        {
            BumpAllocatorThread mixinThread = MixinThread(thread);
            return mixinThread.bumpAllocator.Allocate(bytes, alignment,
                                                      thread);
        }

        [RequiredByBartok]
        [Inline]
        public static unsafe Object CompilerAllocateGenerational
        (VTable vtable, Thread currentThread, UIntPtr bytes, uint alignment)
        {
            VTable.Assert((alignment == 4)
                          || ((alignment == 8) && (UIntPtr.Size == 8))
                          || ((alignment == 8) && (PreHeader.Size == 4)),
                          "Unsupported object layout");
            VTable.Assert(UIntPtr.Size == PreHeader.Size,
                          "Unsupported preheader size");
            VTable.Assert
                (Util.IsAligned((uint) PreHeader.Size + (uint)PostHeader.Size,
                                alignment),
                 "Unsupported header sizes");

            UIntPtr preHeaderAddr =
                MixinThread(currentThread).bumpAllocator.allocPtr;

            // allocPtr is only needed when alignment needs to be checked.  It
            // stores the beginning of the region to be allocation including
            // a possible alignment token.
            UIntPtr allocPtr = UIntPtr.Zero;
            if((alignment == 8) && (UIntPtr.Size == 4)) {
                allocPtr = preHeaderAddr;
                preHeaderAddr = Util.Pad(preHeaderAddr, (UIntPtr) alignment);
            }

            UIntPtr bound = preHeaderAddr + bytes;
            UIntPtr limitPtr =
                MixinThread(currentThread).bumpAllocator.zeroedLimit;
            if (bound <= limitPtr) {
                if((alignment == 8) && (UIntPtr.Size == 4)) {
                    // Store alignment token at allocPtr.  This will be where an
                    // alignment token should go if 'preHeaderAddr' was
                    // bumped...
                    Allocator.WriteAlignment(allocPtr);
                    // ... or the alignment token is where the object header
                    // should be.  This code zeroes the object header regardless
                    // and avoids a branch in this fast path.
                    *(UIntPtr *)preHeaderAddr = UIntPtr.Zero;
                }
                MixinThread(currentThread).bumpAllocator.allocPtr = bound;

                UIntPtr objAddr = preHeaderAddr + PreHeader.Size;
                Object obj = Magic.fromAddress(objAddr);
                obj.vtable = vtable;
                return obj;
            }

            return GC.AllocateObjectNoInline(vtable, currentThread);
        }

        [Inline]
        internal static UIntPtr AllocateFast(Thread thread,
                                             UIntPtr bytes, uint alignment)
        {
            BumpAllocatorThread mixinThread = MixinThread(thread);
            return mixinThread.bumpAllocator.AllocateFast(bytes, alignment);
        }

        [ManualRefCounts]
        public static UIntPtr AllocateSlow(Thread currentThread,
                                           UIntPtr bytes, uint alignment)
        {
            BumpAllocatorThread mixinThread = MixinThread(currentThread);
            return mixinThread.bumpAllocator.AllocateSlow(bytes, alignment,
                                                          currentThread);
        }

        [ManualRefCounts]
        public UIntPtr Allocate(UIntPtr bytes, uint alignment) {
            UIntPtr resultAddr = this.AllocateFast(bytes, alignment);
            if (resultAddr == UIntPtr.Zero) {
                Thread currentThread = Thread.CurrentThread;
                resultAddr = this.AllocateSlow(bytes, alignment,
                                               currentThread);
                VTable.Assert(resultAddr != UIntPtr.Zero);
            }
            return resultAddr;
        }

        [ManualRefCounts]
        public UIntPtr Allocate(UIntPtr bytes, uint alignment, Thread thread)
        {
            UIntPtr resultAddr = this.AllocateFast(bytes, alignment);
            if (resultAddr == UIntPtr.Zero) {
                resultAddr = this.AllocateSlow(bytes, alignment, thread);
                VTable.Assert(resultAddr != UIntPtr.Zero);
            }
            return resultAddr;
        }

        [ManualRefCounts]
        internal UIntPtr AllocateFast(UIntPtr bytes, uint alignment)
        {
#if SINGULARITY_KERNEL
#if ENSURE_ALLOCATION_ALLOWED
            // BumpAllocator.EnsureAllocationAllowed();
#endif
#endif
            UIntPtr allocPtr =
                Allocator.AlignedAllocationPtr(this.allocPtr, this.zeroedLimit,
                                               alignment);
            if (allocPtr + bytes > this.zeroedLimit) {
                this.allocPtr = allocPtr;
                return UIntPtr.Zero;
            }
            this.allocPtr = allocPtr + bytes;
            return allocPtr + PreHeader.Size;
        }

        internal UIntPtr AllocateSlow(UIntPtr bytes, uint alignment,
                                      Thread currentThread)
        {
            UIntPtr newObjectAddr = this.ExtendZero(bytes, alignment);
            if (newObjectAddr == UIntPtr.Zero) {
                newObjectAddr =
                    this.ExtendAlloc(bytes, alignment, currentThread);
                if (newObjectAddr == UIntPtr.Zero) {
                    newObjectAddr =
                        this.FreshAlloc(bytes, alignment, currentThread);
                }
            }
            return newObjectAddr;
        }

        [Inline]
        private UIntPtr ExtendZero(UIntPtr bytes, uint alignment)
        {
            return UIntPtr.Zero;
        }

        private UIntPtr ExtendAlloc(UIntPtr bytes, uint alignment,
                                    Thread currentThread)
        {
            if (this.reserveLimit == UIntPtr.Zero) {
                return UIntPtr.Zero;
            }
#if SINGULARITY_KERNEL
            Kernel.Waypoint(700);
#endif
            UIntPtr neededBytes =
                bytes +  // Bytes required for object +
                alignment - UIntPtr.Size - // worst case alignment overhead +
                (this.reserveLimit - this.allocPtr); // bytes already available
            UIntPtr paddedNeed = PageTable.PagePad(neededBytes);
            UIntPtr pageCount = PageTable.PageCount(paddedNeed);
            UIntPtr startPage = PageTable.Page(this.reserveLimit);
            bool fCleanPages = CLEAR_POOL_PAGES();
            bool gotPages =
                PageManager.TryReserveUnusedPages(currentThread, startPage,
                                                  pageCount, this.pageType,
                                                  ref fCleanPages);
            if (!gotPages) {
                // We can't indiscriminately ask for more memory if we have
                // unused pages already available.
                return UIntPtr.Zero;
            }
            if (this.reserveLimit == UIntPtr.Zero) {
                // A collection occurred, so there is no region to extend
                PageManager.ReleaseUnusedPages(startPage, pageCount,
                                               fCleanPages);
                return UIntPtr.Zero;
            }
            BaseCollector.IncrementNewBytesSinceGC(paddedNeed);
            this.allocNew = this.reserveLimit;
            // Pad alignment space if necessary.  NB: a prior call to
            // AllocateFast may have started generating alignment tokens,
            // but we may need to finish the job here if the residual space
            // was insufficient for a multi-word alignment.
            UIntPtr oldReserveLimit = this.reserveLimit;
            this.reserveLimit += paddedNeed;
            this.allocPtr =
                Allocator.AlignedAllocationPtr(this.allocPtr,
                                               this.reserveLimit,
                                               alignment);
            if (this.zeroedLimit < this.allocPtr) {
                this.zeroedLimit = this.allocPtr;
            }
            UIntPtr objectAddr = this.allocPtr + PreHeader.Size;
            this.allocPtr += bytes;
            if (fCleanPages) {
                if (this.zeroedLimit < oldReserveLimit) {
                    Util.MemClear(this.zeroedLimit,
                                  oldReserveLimit - this.zeroedLimit);
                }
                this.zeroedLimit = this.reserveLimit;
            } else {
                Util.MemClear(this.zeroedLimit,
                              this.allocPtr - this.zeroedLimit);
                this.zeroedLimit = this.allocPtr;
            }
            VTable.Assert(this.allocPtr <= this.zeroedLimit);
            VTable.Assert(PageTable.PageAligned(this.reserveLimit));
            if (objectAddr >= oldReserveLimit) {
                // Object is first on new page
                InteriorPtrTable.SetFirst(objectAddr);
            } else if (objectAddr + bytes < this.reserveLimit) {
                // The object does not end on new limit

                // N.B. The next object may not be allocated at exactly
                // (objectAddr + bytes) due to alignment considerations.  It
                // also might not ever be allocated.  These cases are handled
                // by InteriorPtrTable.First skipping over alignment tokens
                // and callers of First watching out for unused space tokens.

                InteriorPtrTable.SetFirst(objectAddr + bytes);
            }
            // We know an object is located as the last one in a page
            // when it extends through the page to the next.
            // Otherwise, it is totally before or below the page, and
            // we are not sure whether it is the last object or not.
            // So record only such an object for the last card in that
            // page. Many objects may have been omitted due to
            // this coarse-grain recording. But we should be able
            // to incrementally update the offset table and find them.
            // I believe this is a better choice than simply recording
            // any object to the offset table, because most objects
            // may just die and need not to record.

#if !SINGULARITY || SEMISPACE_COLLECTOR || ADAPTIVE_COPYING_COLLECTOR || SLIDING_COLLECTOR
            if (GC.remsetType == RemSetType.Cards) {
                if (objectAddr < oldReserveLimit &&
                    allocPtr + bytes > oldReserveLimit) {
#if DONT_RECORD_OBJALLOC_IN_OFFSETTABLE
#else
                    OffsetTable.SetLast(objectAddr);
#endif
                }
            }
#endif

#if SINGULARITY_KERNEL
            Kernel.Waypoint(701);
#endif
            return objectAddr;
        }

        private UIntPtr FreshAlloc(UIntPtr bytes, uint alignment,
                                   Thread currentThread)
        {
#if SINGULARITY_KERNEL
            Kernel.Waypoint(702);
#endif
            this.Truncate();
            UIntPtr paddedBytes =
                PageTable.PagePad(bytes + alignment - UIntPtr.Size);
            BaseCollector.IncrementNewBytesSinceGC(paddedBytes);
            UIntPtr pages = PageTable.PageCount(paddedBytes);
            bool fCleanPages = CLEAR_POOL_PAGES();
            // We may eventually want to ask for specific pages
            // between asking if any pages are reusable and asking the
            // OS for any possible page.
            UIntPtr startPage =
                PageManager.EnsurePages(currentThread, pages, this.pageType,
                                        ref fCleanPages);
            UIntPtr startAddr = PageTable.PageAddr(startPage);
            UIntPtr limitAddr = PageTable.PageAddr(startPage + pages);
            startAddr = Allocator.AlignedAllocationPtr(startAddr, limitAddr,
                                                       alignment);
            this.allocNew = startAddr;
            this.allocPtr = startAddr + bytes;
            if (fCleanPages) {
                this.zeroedLimit = limitAddr;
            } else {
                Util.MemClear(startAddr, bytes);
                this.zeroedLimit = this.allocPtr;
            }
            this.reserveLimit = limitAddr;
            UIntPtr resultAddr = startAddr + PreHeader.Size;
            InteriorPtrTable.SetFirst(resultAddr);

#if !SINGULARITY || SEMISPACE_COLLECTOR || ADAPTIVE_COPYING_COLLECTOR || SLIDING_COLLECTOR
            if (GC.remsetType == RemSetType.Cards) {
                UIntPtr nextPageAddr = startAddr + PageTable.PageSize;
                VTable.Assert(resultAddr < nextPageAddr);
                if (this.allocPtr > nextPageAddr) {
#if DONT_RECORD_OBJALLOC_IN_OFFSETTABLE
#else
                    OffsetTable.SetLast(resultAddr);
#endif
                }
            }
#endif

#if SINGULARITY_KERNEL
            Kernel.Waypoint(703);
#endif
            return resultAddr;
        }

        internal static void Preempt(Thread t)
        {
            MixinThread(t).bumpAllocator.Preempt();
        }

        private void Preempt()
        {
            this.zeroedLimit = UIntPtr.Zero;
        }

        internal static void Truncate(Thread t)
        {
            MixinThread(t).bumpAllocator.Truncate();
        }

        internal void Truncate()
        {
            UIntPtr allocPtr = this.allocPtr;
            if (!PageTable.PageAligned(allocPtr)) {
                WriteUnusedMarker(allocPtr);
            }
            // NB: allocPtr must never be zero unless zeroedLimit is also zero.
            // NB: zeroedLimit can be zero if GC is necessary.
            this.zeroedLimit = UIntPtr.Zero;
            this.reserveLimit = UIntPtr.Zero;
            this.allocPtr = UIntPtr.Zero;
            this.allocNew = UIntPtr.Zero;
        }

        private static UIntPtr UNUSED_SPACE_TOKEN {
            [Inline]
            [NoHeapAllocation]
            get { return ~((UIntPtr)7u); }
        }

        [Inline]
        [NoHeapAllocation]
        internal static unsafe void WriteUnusedMarker(UIntPtr addr)
        {
            *(UIntPtr*)addr = BumpAllocator.UNUSED_SPACE_TOKEN;
        }

        [Inline]
        [NoHeapAllocation]
        internal static unsafe bool IsUnusedMarkerAddr(UIntPtr addr)
        {
            return (*(UIntPtr*)addr == UNUSED_SPACE_TOKEN);
        }

        [Inline]
        [NoHeapAllocation]
        internal static unsafe bool IsUnusedSpace(UIntPtr obj)
        {
            return *(UIntPtr*)(obj - PreHeader.Size) == UNUSED_SPACE_TOKEN;
        }

        internal static unsafe UIntPtr SkipNonObjectData(UIntPtr objectAddr,
                                                         UIntPtr limit)
        {
            // Skip any UNUSED_SPACE_TOKEN and ALIGNMENT_TOKEN areas
            while (true) {
                if (objectAddr >= limit) {
                    break;
                }
                if (Allocator.IsAlignment(objectAddr)) {
                    objectAddr += UIntPtr.Size;
                } else if (IsUnusedSpace(objectAddr)) {
                    UIntPtr wordAfterUnused =
                        objectAddr - PreHeader.Size + UIntPtr.Size;
                    UIntPtr pageLimit = PageTable.PagePad(wordAfterUnused);
                    CheckMemoryClear(wordAfterUnused, pageLimit);
                    objectAddr = pageLimit + PreHeader.Size;
                } else if (Allocator.IsZeroVTable(objectAddr)) {
                    // The rest of the page must not be used
                    UIntPtr pageLimit = PageTable.PagePad(objectAddr);
                    CheckMemoryClear(objectAddr, pageLimit);
                    objectAddr = pageLimit + PreHeader.Size;
                } else {
                    break;
                }
            }
            return objectAddr;
        }

        [Inline]
        internal static unsafe bool IsRestOfPageZero(UIntPtr lowAddr) {
            UIntPtr* initial = (UIntPtr*)lowAddr;
            UIntPtr* pageLimit = (UIntPtr*)PageTable.PagePad(lowAddr);
            for (UIntPtr* addr = initial; addr < pageLimit; addr++) {
                 if (*addr != UIntPtr.Zero) {
                     return false;
                 }
            }
            return true;
        }

        [System.Diagnostics.Conditional("DEBUG")]
        private static void CheckMemoryClear(UIntPtr begin,
                                             UIntPtr limit) {
            VTable.DebugBreak();
        }

#if SINGULARITY_KERNEL
#if ENSURE_ALLOCATION_ALLOWED
        internal static void EnsureAllocationAllowed()
        {
            // Verify that we're not in an interrupt or non-preemptible region where allocations are prohibited
            Microsoft.Singularity.Processor currentProcessor = Microsoft.Singularity.Processor.CurrentProcessor;
            if (currentProcessor != null) // The Processor object itself may still need to be allocated
            {
                if (currentProcessor.InInterruptContext)
                {
                    Tracing.Log(Tracing.Fatal, "Attempt to allocate memory from interrupt context!");
                    VTable.DebugPrint("Attempt to allocate memory from interrupt context!\n");
                    VTable.DebugBreak();
                }
#if false // Currently too many allocations with preemption disabled to debug right now
                if (currentProcessor.PreemptionDisabled)
                {
                    VTable.DebugPrint("Attempt to allocate memory with preemption disabled!\n");
                    VTable.DebugBreak();
                }
#endif
            }
            VTable.Deny(Thread.CurrentThread != null &&
                        Transitions.fInitializedRuntime &&
                        Transitions.UnderGCControl(Thread.GetCurrentThreadIndex()));
        }
#endif
#endif

    }

    [MixinConditional("BumpAllocatorPageClear")]
    [Mixin(typeof(BumpAllocator))]
    internal struct BumpAllocatorPageClear /* : BumpAllocator */
    {

        [MixinOverride]
        private static bool CLEAR_POOL_PAGES() {
            return true;
        }

        [System.Diagnostics.Conditional("DEBUG")]
        [MixinOverride]
        private static unsafe void CheckMemoryClear(UIntPtr begin,
                                                    UIntPtr limit)
        {
            UIntPtr *beg = (UIntPtr *)begin;
            UIntPtr *lim = (UIntPtr *)limit;

            for (; beg < lim; beg++) {
                VTable.Assert(*beg == UIntPtr.Zero, "Memory isn't zero.");
            }
        }

    }

    [MixinConditional("BumpAllocatorObjectClear")]
    [Mixin(typeof(BumpAllocator))]
    internal struct BumpAllocatorObjectClear /* : BumpAllocator */
    {

        private UIntPtr           allocPtr; // Next allocation.
        private UIntPtr           zeroedLimit; // Limit of zeroed pool.
        private UIntPtr           reserveLimit; // Limit of reserved pool.

        [MixinOverride]
        private static bool CLEAR_POOL_PAGES() {
            return false;
        }

        [MixinOverride]
        [ManualRefCounts]
        [Inline]
        internal UIntPtr AllocateFast(UIntPtr bytes, uint alignment)
        {
#if SINGULARITY_KERNEL
#if ENSURE_ALLOCATION_ALLOWED
            BumpAllocator.EnsureAllocationAllowed();
#endif
#endif
            UIntPtr allocPtr =
                Allocator.AlignedAllocationPtr(this.allocPtr,
                                               this.reserveLimit,
                                               alignment);
            UIntPtr objectLimitPtr = allocPtr + bytes;
            if (objectLimitPtr > this.reserveLimit) {
                this.allocPtr = allocPtr;
                return UIntPtr.Zero;
            }
            if (objectLimitPtr > this.zeroedLimit) {
                Util.MemClear(allocPtr, bytes);
                this.zeroedLimit = objectLimitPtr;
            }
            this.allocPtr = objectLimitPtr;
            return allocPtr + PreHeader.Size;
        }

        [System.Diagnostics.Conditional("DEBUG")]
        [MixinOverride]
        private static unsafe void CheckMemoryClear(UIntPtr begin,
                                                    UIntPtr limit)
        {
            // Since we are only clearing memory on demand, the memory area
            // is allowed to contain random garbage values.
        }

    }

    [MixinConditional("BumpAllocatorCacheClear")]
    [Mixin(typeof(BumpAllocator))]
    internal struct BumpAllocatorCacheClear /* : BumpAllocator */
    {

        private UIntPtr           allocPtr; // Next allocation.
        private UIntPtr           zeroedLimit; // Limit of zeroed pool.
        private UIntPtr           reserveLimit; // Limit of reserved pool.

        [MixinOverride]
        private static bool CLEAR_POOL_PAGES() {
            return false;
        }

        private static UIntPtr CACHE_SIZE {
            get { return (UIntPtr) 128; }
        }

        [MixinOverride]
        internal UIntPtr ExtendZero(UIntPtr bytes, uint alignment)
        {
            while (this.allocPtr + bytes <= this.reserveLimit) {
                UIntPtr newZeroedLimit =
                    Util.Pad(this.allocPtr + bytes, CACHE_SIZE);
                Util.MemClear(this.zeroedLimit,
                              newZeroedLimit - this.zeroedLimit);
                this.zeroedLimit = newZeroedLimit;
                UIntPtr allocPtr =
                    Allocator.AlignedAllocationPtr(this.allocPtr,
                                                   newZeroedLimit,
                                                   alignment);
                if (allocPtr + bytes <= newZeroedLimit) {
                    this.allocPtr = allocPtr + bytes;
                    return allocPtr + PreHeader.Size;
                } else {
                    this.allocPtr = allocPtr;
                }
            }
            return UIntPtr.Zero;
        }

        [System.Diagnostics.Conditional("DEBUG")]
        [MixinOverride]
        private static unsafe void CheckMemoryClear(UIntPtr begin,
                                                    UIntPtr limit)
        {
            // Since we are only clearing memory on demand, the memory area
            // is allowed to contain random garbage values.
        }

    }

}
