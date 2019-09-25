//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Heap for memory passed between processes.
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using System.GCs;
using System.Collections;
using System.Diagnostics;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity.Memory
{
    // <summary>
    // Non-garbage collected heap for memory transferred between processes.
    //
    // This heap supports explicit Allocate/Free operations of arbitrary sizes.
    //
    // An allocated region may be split into two separate regions at a later
    // time.  The split may occur at an arbitrary position inside the original
    // region.  These split regions may be further split.  In order to support
    // this feature, the heap meta-data for tracking allocated regions is kept
    // on the side, instead of directly adjacent to the allocation.
    //
    // Each allocated region is owned by a process.  All regions owned by a
    // process may be quickly found and deleted upon process death.
    //
    // An allocated region's ownership may be transferred between owners.
    // A region may also have multiple owners.
    // </summary>
    public partial class SharedHeap {

        //
        // The system always has at least one shared heap
        //
        private static SharedHeap kernelSharedHeap;

        public static SharedHeap KernelSharedHeap {
            get {
                DebugStub.Assert(kernelSharedHeap != null);
                return kernelSharedHeap;
            }
        }

        public static SharedHeap CurrentProcessSharedHeap {
            get {
                return Thread.CurrentProcess.ProcessSharedHeap;
            }
        }

        internal static unsafe void Initialize()
        {
            kernelSharedHeap = new SharedHeap(ProtectionDomain.DefaultDomain,
                MemoryManager.UseAddressTranslation
                    ? MemoryManager.GetKernelRange()
                    : null);
        }

        // Debug-only sanity check that we are in the right protection domain.
        protected void CheckDomain()
        {
            //
            // If this assertion fails, we are not operating within
            // correct address space. This is likely a serious problem; check
            // to make sure the caller is properly checking that this
            // shared heap is, in fact, mapped before trying to use it!
            //
            if (!parentDomain.KernelMode) {
                DebugStub.Assert(
                    Processor.GetCurrentAddressSpace() ==
                    parentDomain.AddressSpace);
            }
        }

        // <summary>
        // If we can fit multiple regions of a certain size on a single page,
        // then we consider them to be "small" regions.  Large regions get
        // sole usage of their page(s).
        // </summary>
        private const uint MaxSmallRegion = MemoryManager.PageSize / 2;

        // <summary>
        // Small regions fall into various raw bucket sizes:
        //
        // Bucket          Raw Size                      4K page example
        //   0    0 to round(MaxSmallRegion / 128)             16
        //   1    prior to round(MaxSmallRegion / 64)          32
        //   2    prior to round(MaxSmallRegion / 32)          64
        //   3    prior to round(MaxSmallRegion / 16)         128
        //   4    prior to round(MaxSmallRegion / 8)          256
        //   5    prior to round(MaxSmallRegion / 4)          512
        //   6    prior to round(MaxSmallRegion / 2)         1024
        //   7    prior to MaxSmallRegion                    2048
        //
        // Where round() rounds down to UIntPtr-size boundaries.
        // Actual space available to user is the raw size minus the
        // size of the small region header.
        // </summary>
        private const byte TotalBuckets = 8;
        private unsafe UIntPtr *freeSmallRegions;

        private VirtualMemoryRange memoryRange; // where we get our pages
        private ProtectionDomain parentDomain;

        // <summary>
        // Given a bucket number, return the size of the regions
        // stored in that bucket.
        // </summary>
        [Inline]
        private static UIntPtr BucketSize(byte bucket)
        {
            DebugStub.Assert(bucket < TotalBuckets);

            return (UIntPtr)(((MaxSmallRegion >> (TotalBuckets - 1)) &
                              ~(UIntPtr.Size - 1)) << bucket);
        }

        // <summary>
        // Given a desired size, return the number of the smallest bucket
        // which can hold something of the desired size.
        // </summary>
        private static byte BucketForSize(UIntPtr size)
        {
            DebugStub.Assert(size <= MaxSmallRegion);

            for (byte Loop = 0; Loop < TotalBuckets - 1; Loop++) {
                if (size <= BucketSize(Loop)) {
                    return Loop;
                }
            }

            return TotalBuckets - 1;
        }


        // <summary>
        // Header for small regions.
        // A small region is not returned to its bucket's free list until all
        // of its shared and split-off pieces have been freed.  The reference
        // count tracks outstanding views into a region.
        // </summary>
        private struct SmallRegion {
            internal uint referenceCount;
        }

        // <summary>
        // Increment the reference count on a small region.
        //
        // BUGBUG: Only works where sizeof(UIntPtr) = sizeof(uint)
        // Need another version of Interlocked.CompareExchange for uints.
        //
        // BUGBUG: Should handle ref count overflow more gracefully.
        // </summary>
        private static unsafe void AtomicReferenceSmallRegion(UIntPtr region)
        {
            uint *refCountLocation;
            uint oldRefCount, newRefCount;

            refCountLocation = &(((SmallRegion *)region)->referenceCount);

            do {

                oldRefCount = *refCountLocation;
                DebugStub.Assert(oldRefCount != uint.MaxValue);
                newRefCount = oldRefCount + 1;

            } while (oldRefCount != Interlocked.CompareExchange(ref *refCountLocation, newRefCount, oldRefCount));
        }

        // <summary>
        // Decrement the reference count on a small region.
        //
        // BUGBUG: Only works where sizeof(UIntPtr) = sizeof(uint)
        // Need another version of Interlocked.CompareExchange for uints.
        // </summary>
        private static unsafe uint AtomicDereferenceSmallRegion(
            UIntPtr region)
        {
            uint *refCountLocation;
            uint oldRefCount, newRefCount;

            refCountLocation = &(((SmallRegion *)region)->referenceCount);

            do {

                oldRefCount = *refCountLocation;
                DebugStub.Assert(oldRefCount != 0);
                newRefCount = oldRefCount - 1;

            } while (oldRefCount != Interlocked.CompareExchange(ref *refCountLocation, newRefCount, oldRefCount));

            return newRefCount;
        }


        // <summary>
        // Masks to retrieve various interpretations of the "extra" 12 bits
        // contained in a page descriptor.  One bit differentiates pages
        // broken into small regions from those comprising large regions.
        // The remainder are used to indicate the bucket (for small regions)
        // or the reference count on the page (for large regions).
        // </summary>
        private const uint SmallRegionBit = 0x00008000u;
        private const uint SmallRegionBucketMask = 0x00000ff0u;
        private const byte SmallRegionBucketShift = 4;
        private const uint LargeRegionReferenceMask = 0x00007ff0u;
        private const byte LargeRegionReferenceShift = 4;

        [Inline]
        private static uint BucketToExtra(byte bucket)
        {
            return (uint)(SmallRegionBit |
                          ((uint)bucket << SmallRegionBucketShift));
        }

        [Inline]
        private static uint LargeRefToExtra(uint refCount)
        {
            return (uint)(refCount << LargeRegionReferenceShift);
        }

        // <summary>
        // Increment the reference count on a large region page.
        // Note: This method relies upon page descriptor format.
        //
        // BUGBUG: Only works where sizeof(UIntPtr) = sizeof(uint)
        // Need another version of Interlocked.CompareExchange for uints.
        //
        // BUGBUG: Should handle ref count overflow more gracefully.
        // </summary>
        private unsafe void AtomicReferencePage(UIntPtr page)
        {
            uint *descriptorLocation;
            uint oldDescriptor, refCount, newDescriptor;

            descriptorLocation = SharedHeapPageTable + page;

            do {

                oldDescriptor = *descriptorLocation;
                refCount = (oldDescriptor & LargeRegionReferenceMask)
                    >> LargeRegionReferenceShift;
                DebugStub.Assert(refCount != (LargeRegionReferenceMask >>
                                              LargeRegionReferenceShift));
                refCount++;
                newDescriptor = (oldDescriptor & ~LargeRegionReferenceMask) |
                    (refCount << LargeRegionReferenceShift);

            } while (oldDescriptor != Interlocked.CompareExchange(ref *descriptorLocation, newDescriptor, oldDescriptor));
        }

        // <summary>
        // Decrement the reference count on a large region page.
        // Note: This method relies upon page descriptor format.
        //
        // BUGBUG: Only works where sizeof(UIntPtr) = sizeof(uint)
        // Need another version of Interlocked.CompareExchange for uints.
        // </summary>
        private unsafe uint AtomicDereferencePage(UIntPtr page)
        {
            uint *descriptorLocation;
            uint oldDescriptor, refCount, newDescriptor;

            descriptorLocation = SharedHeapPageTable + page;

            do {

                oldDescriptor = *descriptorLocation;
                refCount = (oldDescriptor & LargeRegionReferenceMask)
                    >> LargeRegionReferenceShift;
                DebugStub.Assert(refCount != 0);
                refCount--;
                newDescriptor = (oldDescriptor & ~LargeRegionReferenceMask) |
                    (refCount << LargeRegionReferenceShift);

            } while (oldDescriptor != Interlocked.CompareExchange(ref *descriptorLocation, newDescriptor, oldDescriptor));

            return refCount;
        }

        // <summary>
        // Increment the reference count(s) on the page(s) or small region.
        // </summary>
        private unsafe void ReferenceRegion(
            UIntPtr start, UIntPtr size)
        {
            UIntPtr page;
            uint pageDescriptor;

            if (size == 0) {
                //
                // Zero-sized allocations aren't backed by actual memory
                // and thus have no reference count to maintain.
                //
                return;
            }

            page = PageFromAddr(start);
            pageDescriptor = *(SharedHeapPageTable + page);

            if ((pageDescriptor & SmallRegionBit) == SmallRegionBit) {
                byte bucket;
                UIntPtr region;
                UIntPtr regionSize;

                //
                // This is a small region.  Figure out which bucket it's from.
                // Using the bucket size, we can find the start of the region
                // and access the region header.
                //
                bucket = (byte)((pageDescriptor & SmallRegionBucketMask) >>
                                SmallRegionBucketShift);
                regionSize = BucketSize(bucket);
                region = start & ~(regionSize - 1);

                AtomicReferenceSmallRegion(region);

            }
            else {
                //
                // This is a large region.  We need to walk all the pages
                // it covers, and increment the reference count on each.
                //
                UIntPtr lastPage;
                UIntPtr lastByteAddress;

                lastByteAddress = start + size - 1;
                lastPage = PageFromAddr(lastByteAddress);

                while (page <= lastPage) {
                    AtomicReferencePage(page);
                    page++;
                }
            }
        }

        /// <summary>
        /// Decrement the reference count(s) on the page(s) or small region.
        /// </summary>
        /// <returns>true if last reference to this region was freed.</returns>
        private unsafe bool DereferenceRegion(UIntPtr start, UIntPtr size)
        {
            // Dereference and release underlying memory
            return DereferenceRegion(start, size, false);
        }

        // The dontFreePages argument indicates whether to actually release
        // memory pages back to the operating system. If the caller
        // specifies true, it acquires ownership of the memory pages if
        // the return address is true (indicating that no more allocation
        // records refer to the memory)
        private unsafe bool DereferenceRegion(UIntPtr start, UIntPtr size,
                                              bool dontFreePages)
        {
            UIntPtr page;
            uint pageDescriptor;
            bool lastReference = true;

            if (size == 0) {
                //
                // Zero-sized allocations aren't backed by actual memory
                // and thus have no reference count to maintain.
                //
                return lastReference;
            }

            page = PageFromAddr(start);
            pageDescriptor = *(SharedHeapPageTable + page);

            if ((pageDescriptor & SmallRegionBit) == SmallRegionBit) {
                byte bucket;
                UIntPtr region;
                UIntPtr regionSize;
                uint refCount;

                //
                // This is a small region.  Figure out which bucket it's from.
                // Using the bucket size, we can find the start of the region
                // and access the region header.
                //
                bucket = (byte)((pageDescriptor & SmallRegionBucketMask) >>
                                SmallRegionBucketShift);
                regionSize = BucketSize(bucket);
                region = start & ~(regionSize - 1);

                refCount = AtomicDereferenceSmallRegion(region);
                if (refCount == 0) {
                    //
                    // Return region to the bucket's free list.
                    //
                    AtomicPushFreeList(ref freeSmallRegions[bucket], region);
                }
                else {
                    lastReference = false;
                }

            }
            else {
                //
                // This is a large region.  We need to walk all the pages
                // it covers, and decrement the reference count on each.
                // Pages no longer referenced are returned to the page manager.
                //
                UIntPtr lastPage;
                UIntPtr lastByteAddress;

                lastByteAddress = start + size - 1;
                lastPage = PageFromAddr(lastByteAddress);

                while (page <= lastPage) {

                    if (AtomicDereferencePage(page) == 0) {
                        UIntPtr startAddr = AddrFromPage(page);
                        UIntPtr regionPages = 1;
                        page++;

                        while (page <= lastPage &&
                               AtomicDereferencePage(page) == 0) {
                            regionPages++;
                            page++;
                        }

                        if (!dontFreePages) {
                            FreePages(startAddr, regionPages);
                        }
                    }
                    else {
                        lastReference = false;
                    }

                    page++;
                }
            }
            return lastReference;
        }

        // <summary>
        // Whether to use spinlocks (true) or disabling of interrupts (false)
        // to protect the ownership lists.
        // </summary>
        private static bool useAllocationOwnerLocks;

        // <summary>
        // The free allocation owner descriptor list.
        // Free descriptors are kept as unstructured memory, with the first
        // UIntPtr bytes of each serving as the pointer to the next one.
        // </summary>
        private UIntPtr freeOwnerList;

        //
        // NOTE: The shared heap has a concept of AllocationOwnerIds,
        // but in our current system there is a single one of these for
        // all data block and endpoint allocs in a given heap.
        //
        private AllocationOwnerId allocOwnerId;
        private AllocationOwnerId endpointOwnerId;
        private AllocationOwnerId endpointPeerOwnerId;

        public AllocationOwnerId DataOwnerId {
            get {
                return allocOwnerId;
            }
        }

        public AllocationOwnerId EndpointOwnerId {
            get {
                return endpointOwnerId;
            }
        }

        public AllocationOwnerId EndpointPeerOwnerId {
            get {
                return endpointPeerOwnerId;
            }
        }

        /// <summary>
        /// Call back for iterating over all elements of an allocation list.
        /// </summary>
        unsafe public delegate void AllocationVisitor(Allocation* alloc);

        /// <summary>
        /// Call back for filtering elements of an allocation list.
        /// </summary>
        unsafe public delegate bool AllocationMatches(Allocation* alloc);

        // <summary>
        // Per-process object structure used to track allocations 'owned'
        // by a process.  List integrity is protected by the spinlock.
        // </summary>
        internal struct AllocationOwner {
            internal unsafe Allocation *sentinel;
            private SpinLock listLock;
            internal long outstandingBlocks;

            internal static unsafe bool Lock(AllocationOwner *owner)
            {
                bool wasEnabled = Processor.DisableInterrupts();
                if (useAllocationOwnerLocks) {
                    owner->listLock.Acquire(Thread.CurrentThread);
                }
                return wasEnabled;
            }

            internal static unsafe void Unlock(AllocationOwner* owner,
                                               bool doRestore)
            {
                if (useAllocationOwnerLocks) {
                    owner->listLock.Release(Thread.CurrentThread);
                }
                Processor.RestoreInterrupts(doRestore);
            }

            internal static unsafe void ReuseOrCreateOwner(
                SharedHeap sharedHeap,
                out AllocationOwnerId ownerId)
            {
                UIntPtr descriptorAddress;
                uint descriptorSize = (uint)sizeof(AllocationOwner);

                //
                // Attempt to get a descriptor from our free list.
                //
                descriptorAddress = AtomicPopFreeList(ref sharedHeap.freeOwnerList);

                if (descriptorAddress == UIntPtr.Zero) {
                    //
                    // Free list is empty.
                    // Allocate new page and break it up into allocation owner
                    // descriptors.  Use first descriptor to satisfy current
                    // request, put remainder on the free list.
                    //
                    UIntPtr newSpace;
                    uint spaceRemaining;

                    newSpace = sharedHeap.AllocatePages(1);
                    descriptorAddress = newSpace;
                    newSpace += descriptorSize;
                    spaceRemaining = MemoryManager.PageSize - descriptorSize;
                    while (spaceRemaining > descriptorSize) {
                        AtomicPushFreeList(ref sharedHeap.freeOwnerList, newSpace);
                        newSpace += descriptorSize;
                        spaceRemaining -= descriptorSize;
                    }
                }

                //
                // Initialize the owner struct before handing it out.
                //
                Buffer.ZeroMemory((byte *)descriptorAddress, descriptorSize);

                ((AllocationOwner*)descriptorAddress)->sentinel =
                    Allocation.CreateSentinel(sharedHeap);
                ((AllocationOwner*)descriptorAddress)->listLock =
                    new SpinLock(SpinLock.Types.SharedHeapAllocationOwner);
                ownerId.owner = (AllocationOwner*)descriptorAddress;
            }

            ///
            ///  Diagnostic methods
            ///
            public long OutstandingBlocks {
                get { return this.outstandingBlocks; }
            }

            /// <summary>
            /// Calls the visitor with each allocation on the list.
            /// Important: the visitor is not allowed to keep the element!
            /// </summary>
            unsafe public static void Iterate(AllocationOwner* owner,
                                              AllocationVisitor visitor)
            {
                bool wasEnabled = Lock(owner);

                Allocation* sentinel = owner->sentinel;
                //
                // Walk the list.
                //
                Allocation* current = sentinel->next;
                while (current != sentinel) {
                    if (Allocation.GetType(current) !=
                        typeof(RoverType).GetSystemType().id) {
                        visitor(current);
                    }
                    current = current->next;
                }
                Unlock(owner, wasEnabled);
            }

            /// <summary>
            /// Calls the visitor with each matching allocation on the list.
            /// The matcher is not allowed to modify the list.
            /// The visitor is allowed to modify the list (e.g. to delete
            /// the visited element from the list), and the visitor
            /// is called with the owner lock unacquired.  Furthermore,
            /// the iteration releases the owner lock periodically (even
            /// if visitor is never called) so that it doesn't monopolize
            /// the lock.  The matcher should only return true if no other
            /// thread can deallocate the matched element while the lock
            /// is unheld; otherwise, the visitor will be in a race.
            ///
            /// To ensure that iteration is still meaningful in the face
            /// of concurrent mutation, the iterator adds a "rover"
            /// node to the beginning of the list, then steps the rover
            /// one node at a time through the list until it arrives at the
            /// end.
            /// </summary>
            unsafe public static void IterateMatchingForModify(
                AllocationOwnerId ownerId,
                AllocationMatches matches,
                AllocationVisitor visitor)
            {
                const int RELEASE_PERIOD = 128; // periodically release lock
                int releaseCount = 0;
                Allocation roverAllocation;
                Allocation* rover = &roverAllocation;
                UIntPtr roverType = typeof(RoverType).GetSystemType().id;
                Allocation.Initialize(rover, 0, 0, roverType);
                AllocationOwner* owner = ownerId.owner;
                Allocation.AssignOwnership(rover, ownerId);
                bool wasEnabled = Lock(owner);

                Allocation* sentinel = owner->sentinel;
                //
                // Walk the list.
                //
                while (rover->next != sentinel) {
                    releaseCount = (releaseCount + 1) % RELEASE_PERIOD;
                    Allocation* current = rover->next;

                    if (Allocation.GetType(current) != roverType
                        && matches(current)) {
                        Unlock(owner, wasEnabled);
                        visitor(current);
                        wasEnabled = Lock(owner);
                    }
                    else if (releaseCount == 0) {
                        Unlock(owner, wasEnabled);
                        // TODO: pause here? (prevent lock capture effects)
                        wasEnabled = Lock(owner);
                    }
                    Allocation.MoveForward(rover);
                }
                Unlock(owner, wasEnabled);
                Allocation.RemoveOwnership(rover, ownerId);
            }
        }

        // Used by IterateMatchingForModify
        private struct RoverType {}

        // <summary>
        // Opaque type used to hide AllocationOwner structure
        // from everything outside of the SharedHeap.
        // </summary>
        public struct AllocationOwnerId {
            unsafe internal AllocationOwner* owner;

            public void Iterate(AllocationVisitor visitor) {
                unsafe {
                    AllocationOwner.Iterate(owner, visitor);
                }
            }

            public void IterateMatchingForModify(
                AllocationMatches matches,
                AllocationVisitor visitor) {
                AllocationOwner.IterateMatchingForModify(
                    this, matches, visitor);
            }
        }

        // <summary>
        // Initialize the shared heap subsystem.
        // Note: We trust the system to initialize statics to zero.
        // </summary>
        internal unsafe SharedHeap(ProtectionDomain parentDomain,
                                   VirtualMemoryRange range)
        {
            useAllocationOwnerLocks = true;     // required at least for MP

            this.memoryRange = range;
            this.parentDomain = parentDomain;

            //
            // We don't have another memory allocator handy, so we grab
            // ourselves a page and carve it up.
            //
            UIntPtr newSpace = AllocatePages(1);
            freeSmallRegions = (UIntPtr *)newSpace;

            //
            // REVIEW: Allocate doesn't currently zero-fill, so
            // we need to initialize the free lists.
            //
            for (uint Loop = 0; Loop < TotalBuckets; Loop++) {
                freeSmallRegions[Loop] = UIntPtr.Zero;
            }

            // Set up our owner IDs
            allocOwnerId = OwnerInitialize();
            endpointOwnerId = OwnerInitialize();
            endpointPeerOwnerId = OwnerInitialize();
        }

        internal static void Finalize()
        {
            // Doesn't actually do anything.
        }

        //
        // When paging is not enabled, the (one and only) shared heap
        // always uses general-purpose kernel memory.
        //
        private UIntPtr AllocatePages(UIntPtr numPages)
        {
            return AllocatePages(numPages, 0);
        }

        private unsafe UIntPtr AllocatePages(UIntPtr numPages, uint extra)
        {
            if (memoryRange != null) {
                return memoryRange.Allocate(numPages, null, extra, PageType.Shared);
            }
            else {
                return MemoryManager.KernelAllocate(numPages, null, extra, PageType.Shared);
            }
        }

        private unsafe void FreePages(UIntPtr addr, UIntPtr numPages)
        {
            if (memoryRange != null) {
                memoryRange.Free(addr, numPages, null);
            }
            else {
                MemoryManager.KernelFree(addr, numPages, null);
            }
        }

        private unsafe uint* SharedHeapPageTable {
            get {
                if (memoryRange != null) {
                    return memoryRange.PageTable;
                }
                else {
                    return MemoryManager.KernelPageTable;
                }
            }
        }

        private unsafe UIntPtr SharedHeapPageCount {
            get {
                if (memoryRange != null) {
                    return memoryRange.PageCount;
                }
                else {
                    return MemoryManager.KernelPageCount;
                }
            }
        }

        private unsafe UIntPtr PageFromAddr(UIntPtr addr)
        {
            if (memoryRange != null) {
                return memoryRange.PageFromAddr(addr);
            }
            else {
                return MemoryManager.PageFromAddr(addr);
            }
        }

        private unsafe UIntPtr AddrFromPage(UIntPtr pageIdx)
        {
            if (memoryRange != null) {
                return memoryRange.AddrFromPage(pageIdx);
            }
            else {
                return MemoryManager.AddrFromPage(pageIdx);
            }
        }

        // <summary>
        // Initialize internal per-owner data structure.
        // Returns an opaque identifier to the owner (usually a process)
        // for it to use whenever it calls us in the future.
        // </summary>
        public AllocationOwnerId OwnerInitialize()
        {
            AllocationOwnerId ownerId;
            AllocationOwner.ReuseOrCreateOwner(this, out ownerId);
            return ownerId;
        }

        //
        // Moves a block from another shared heap into this one!
        // The source heap must be mapped and accessible.
        //
        public unsafe Allocation* Move(Allocation* source,
                                       SharedHeap sourceHeap,
                                       AllocationOwnerId sourceOwner,
                                       AllocationOwnerId targetOwner)
        {
            //
            // Note that since both the source and destination shared heaps must
            // be accessible, one of them must be the kernel domain's heap!
            //
            sourceHeap.CheckDomain();
            this.CheckDomain();

#if PAGING && (!DISABLE_PAGE_FLIPPING)
            if (Allocation.GetSize(source) > MaxSmallRegion) {
                // Large region. Move it by page-flipping.
                //
                // NOTE: we currently ASSUME that the block
                // being moved is not being shared, since the sharing
                // feature is being deprecated.
                UIntPtr rangeStart = (UIntPtr)Allocation.GetDataUnchecked(source);
                UIntPtr size = Allocation.GetSize(source);
                UIntPtr type = Allocation.GetType(source);
                UIntPtr pagesStart = MemoryManager.PageTrunc(rangeStart);
                UIntPtr pagesLimit = MemoryManager.PagePad(rangeStart + size);
                UIntPtr pageCount = MemoryManager.PagesFromBytes(pagesLimit - pagesStart);

                // Release the memory from the source heap.
                bool lastFree = sourceHeap.DereferenceRegion(rangeStart, size, true /*don't free pages*/);
                DebugStub.Assert(lastFree);

                // Reserve room in our own memory range for the pages
                UIntPtr mapPoint = this.memoryRange.Reserve(pageCount, null, LargeRefToExtra(1),
                                                            PageType.Shared);

                DebugStub.Assert(mapPoint != UIntPtr.Zero);

                UIntPtr stepSource = pagesStart;
                UIntPtr stepTarget = mapPoint;

                // Map each page into our reserved area of memory
                while (stepSource < pagesLimit) {
                    PhysicalAddress phys = VMManager.GetPageMapping(stepSource);
                    DebugStub.Assert(phys != PhysicalAddress.Null);
                    VMManager.MapPage(phys, stepTarget, memoryRange.ParentDomain);

                    stepSource += MemoryManager.PageSize;
                    stepTarget += MemoryManager.PageSize;
                }

                // Unmap the pages from the source range; they're still marked as being used.
                VMManager.UnmapRange(pagesStart, pageCount);

                // Mark the pages as free. Now the source heap and range have completely
                // forgotten about the memory.
                sourceHeap.memoryRange.Unreserve(pagesStart, pageCount, null);

                return AllocationFromRawMemory(mapPoint, size, type, targetOwner);

            }
            else
#endif
            {
                // Small region. Move it by copying.
                Allocation* retval = ShallowCopy(source, targetOwner);
                sourceHeap.Free(source, sourceOwner);
                return retval;
            }
        }

        // Creates a new allocation record and copies the contents of
        // the provided allocation.
        internal unsafe Allocation *ShallowCopy(Allocation* source,
                                                AllocationOwnerId targetOwner)
        {
            CheckDomain();

            Allocation* copy = Allocate(Allocation.GetSize(source),
                                        Allocation.GetType(source),
                                        0,
                                        targetOwner);

            Buffer.MoveMemory((byte*)Allocation.GetDataUnchecked(copy),
                              (byte*)Allocation.GetDataUnchecked(source),
                              Allocation.GetSize(source));

            return copy;
        }

        // <summary>
        // Allocate an arbitrarily-sized region of memory.
        // TODO: Handle memory exhaustion gracefully.
        // </summary>
        public unsafe Allocation *Allocate(  // Returns new region.
            UIntPtr bytes,  // Number of bytes to allocate.
            UIntPtr type,  // Type information.
            uint alignment,  // Allocation alignment requirement.
            AllocationOwnerId ownerId)  // Id of owner to assign region to.
        {
            CheckDomain();
            UIntPtr region;

            // REVIEW: Pull out-of-bounds parameters into bounds instead?
            DebugStub.Assert(bytes >= 0);

            // TODO: deal with alignment.

            //
            // Allocate the memory region.
            //
            // Small regions impose an overhead of sizeof(SmallRegion),
            // so we need to take that into account when determining
            // whether or not we can fit the allocation into one.
            //
            // Zero-sized allocations are allowed, but we do not allocate
            // a memory region for them.
            //
            if (bytes == 0) {
                region = UIntPtr.Zero;
            }
            else {
                if (bytes + sizeof(SmallRegion) > MaxSmallRegion) {
                    region = AllocateLargeRegion(bytes);
                }
                else {
                    region = AllocateSmallRegion(bytes);
                }
                // Allocation failed, request denied.  Should
                // have asked sooner.
                if (region == UIntPtr.Zero) {
                    return null;
                }
            }

            // TODO: deal with alignment.

            return AllocationFromRawMemory(region, bytes, type, ownerId);
        }

        //
        // Wraps a range of raw memory in a new allocation record.
        //
        private unsafe Allocation* AllocationFromRawMemory(
            UIntPtr region,
            UIntPtr bytes,
            UIntPtr type,
            AllocationOwnerId ownerId)
        {
            CheckDomain();

            // Get an allocation descriptor to keep track of the region.
            // TODO: Handle failure here.
            Allocation* allocation = Allocation.Create(this, region, bytes, type);

            //
            // Put descriptor on per-process list.
            // all descriptors live on the kernel proc for now.
            //
            Allocation.AssignOwnership(allocation, ownerId);

            // Figure out who our caller is.
            UIntPtr pc1, pc2, pc3;
            Isa.GetStackReturnAddresses(out pc1, out pc2, out pc3);
            Tracing.Log(Tracing.Debug, "SharedHeap.Allocate stack trace {0:x} {1:x} {2:x}",
                        pc1, pc2, pc3);
            Tracing.Log(Tracing.Debug, "result = {0:x}", (UIntPtr)allocation);

            return allocation;
        }

        // <summary>
        // Allocate a large region of memory out of system pages.
        // </summary>
        private unsafe UIntPtr AllocateLargeRegion(  // Returns new region.
            UIntPtr bytes)  // Number of bytes to allocate.
        {
            UIntPtr region;

            //
            // For large allocations, we just get pages from the system.
            // REVIEW: We round up to a pagesize to keep Allocate happy.
            // Note: Current implementation of Allocate can block.
            //
            bytes = MemoryManager.PagePad(bytes);
            region = AllocatePages(MemoryManager.PagesFromBytes(bytes), LargeRefToExtra(1));

            //
            // Zero-fill the region before handing it off.
            //
            if (region != UIntPtr.Zero) {
                Buffer.ZeroMemory((byte *)region, bytes);
            }

            return region;
        }

        // <summary>
        // Allocate a small region of memory out of a heap page.
        // </summary>
        private unsafe UIntPtr AllocateSmallRegion(
            UIntPtr bytes)  // Number of bytes to allocate.
        {
            byte bucket;
            UIntPtr region;

            //
            // We allocate the region from the bucket which contains the
            // smallest sized regions which will satisfy the request.
            // And we initialize the region's reference count to 1.
            //
            bucket = BucketForSize(bytes + sizeof(SmallRegion));
            region = AtomicPopFreeList(ref freeSmallRegions[bucket]);
            if (region == UIntPtr.Zero) {
                //
                // Free list is empty.
                // Allocate new page and break it up into small regions
                // of this bucket's size.  Use first descriptor to satisfy
                // current request, put remainder on the free list.
                //
                UIntPtr newSpace;
                UIntPtr spaceRemaining;
                UIntPtr regionSize;

                newSpace = AllocatePages(1, BucketToExtra(bucket));

                if (newSpace == UIntPtr.Zero) {
                    return UIntPtr.Zero;
                }

                regionSize = BucketSize(bucket);
                region = newSpace;
                newSpace += regionSize;
                spaceRemaining = MemoryManager.PageSize - regionSize;
                while (spaceRemaining > regionSize) {
                    AtomicPushFreeList(ref freeSmallRegions[bucket], newSpace);
                    newSpace += regionSize;
                    spaceRemaining -= regionSize;
                }
            }

            //
            // Set reference count on the region.
            //
            unsafe {
                ((SmallRegion *)region)->referenceCount = 1;
                region += sizeof(SmallRegion);
            }

            //
            // Zero-fill the region before handing it off.
            //
            Buffer.ZeroMemory((byte *)region, bytes);

            return region;
        }


        ///  <summary>
        ///  Free a previously-allocated region of memory.
        /// </summary>
        /// <returns>true if Free releases last reference to underlying memory</returns>
        public unsafe bool Free(
            Allocation *allocation,  // Allocated region to be freed.
            AllocationOwnerId ownerId)  // Current owner of allocation.
        {
            CheckDomain();
            DebugStub.Assert(Validate(allocation));
            //
            // Remove from owning process's allocation list.
            //
            Allocation.RemoveOwnership(allocation, ownerId);

            //
            // Release our allocation's claim on the underlying region.
            //
            bool freed = DereferenceRegion(Allocation.GetDataUnchecked(allocation),
                                           Allocation.GetSize(allocation));

            //
            // Free our allocation descriptor.
            //
            AtomicPushFreeList(ref freeAllocationList, (UIntPtr)allocation);

            //
            // Tell caller whether last reference was freed
            //
            return freed;
        }

        // <summary>
        // Free all of a given owner's allocated regions.
        // </summary>
        public unsafe void FreeAll(
            AllocationOwnerId ownerId)
        {
            CheckDomain();

            Allocation *first;
            Allocation *current;
            AllocationOwner *owner = ownerId.owner;

            //
            // REVIEW: Do we need this lock?  This should be the last code
            // for this process to ever call the SharedHeap.
            //
            bool wasEnabled = AllocationOwner.Lock(owner);

            //
            // The FreeAll for a process is called by a kernel service
            // thread and not by the process itself.
            // Thus we use unchecked access to the data, since the process
            // id's won't match
            //
            first = owner->sentinel;
            current = Allocation.Next(first);
            while (current != first) {
                Allocation *victim = current;
                current = Allocation.Next(current);
                DereferenceRegion(Allocation.GetDataUnchecked(victim),
                                  Allocation.GetSize(victim));
                AtomicPushFreeList(ref freeAllocationList, (UIntPtr)victim);
            }

            DereferenceRegion(Allocation.GetDataUnchecked(first),
                              Allocation.GetSize(first));
            AtomicPushFreeList(ref freeAllocationList, (UIntPtr)first);
            owner->sentinel = null;

            AllocationOwner.Unlock(owner, wasEnabled);

            //
            // Free our owner descriptor.
            //
            AtomicPushFreeList(ref freeOwnerList, (UIntPtr)ownerId.owner);
        }

        // <summary>
        // Create a second access handle for a previously allocated region.
        //
        // Sharing of a zero-sized region is tolerated, although weird.
        // </summary>
        public unsafe Allocation *Share(  // Returns new handle.
            Allocation *existing,  // Allocated region to share.
            AllocationOwnerId ownerId,  // Owner of above region.
            UIntPtr startOffset,  // Offset at which shared copy starts.
            UIntPtr endOffset)  // Offset at which shared copy ends.
        {
            CheckDomain();

            DebugStub.Assert(Validate(existing));
            Allocation *copy;
            UIntPtr size;

            size = Allocation.GetSize(existing);

            //
            // We don't handle nonsensical parameters.
            // REVIEW: Pull out-of-bounds parameters into bounds instead?
            //
            DebugStub.Assert(startOffset <= size && endOffset >= startOffset &&
                             endOffset <= size);

            //
            // Create a new descriptor for the allocation with (potentially
            // a subset of) the same data and size as the original.
            //
            copy = Allocation.Create(
                this,
                Allocation.GetData(existing) + startOffset,
                endOffset - startOffset,
                Allocation.GetType(existing),
                Allocation.GetOwnerProcessId(existing));

            //
            // Increment the reference count on affected region/page(s).
            //
            ReferenceRegion(Allocation.GetData(copy),
                            Allocation.GetSize(copy));

            //
            // Put new descriptor on owning process's list.
            //
            Allocation.AssignOwnership(copy, ownerId);

            return copy;
        }

        // <summary>
        // Truncate an allocation to a length.
        // </summary>
        public unsafe void Truncate(Allocation *allocation,
                                    UIntPtr     newSize)
        {
            DebugStub.Assert(Validate(allocation));
            UIntPtr size = Allocation.GetSize(allocation);
            DebugStub.Assert(newSize >= 0 && newSize <= size);
            Allocation.TruncateTo(allocation, newSize);
        }

        // <summary>
        // Split a previously allocated region into two smaller regions.
        // The original region is shrunk by the size of the carved-off
        // second region.
        //
        // Splitting off a zero-sized region is tolerated, although weird.
        // </summary>
        public unsafe Allocation *Split(  // Returns latter region.
            Allocation *existing,  // Region to split.
            AllocationOwnerId ownerId,  // Owner of above region.
            UIntPtr offset)  // Offset at which latter region starts.
        {
            CheckDomain();

            DebugStub.Assert(Validate(existing));
            Allocation *copy;
            UIntPtr size;
            UIntPtr splitPoint;

            size = Allocation.GetSize(existing);

            //
            // We don't handle nonsensical parameters.
            // REVIEW: Pull out-of-bounds parameters into bounds instead?
            //
            DebugStub.Assert(offset >= 0 && offset <= size);

            //
            // Create a new descriptor for the allocation using a suffix
            // of the original data.
            //
            splitPoint = Allocation.GetData(existing) + offset;
            copy = Allocation.Create(
                this,
                splitPoint,
                size - offset,
                Allocation.GetType(existing));

            Allocation.TruncateTo(existing, offset);

            //
            // Increment the reference count on any small region or
            // page which ends up getting shared as a result of this split.
            // (Note that any zero-sized allocations created as a result of
            // this split don't share any memory with other allocations)
            //
            // In other words, unless one of the resulting allocations is
            // zero-sized, or the split point occurs at a page boundary,
            // increment the ref count on the page or small region the
            // split occurs in.
            //
            if ((offset != 0) && (offset != size) &&
                (splitPoint != (splitPoint & ~(MemoryManager.PageSize - 1))))
            {
                ReferenceRegion(splitPoint, 1);
            }

            //
            // Put new descriptor on owning process's list.
            //
            Allocation.AssignOwnership(copy, ownerId);

            return copy;
        }


        // <summary>
        // Transfer ownership of an allocated region from one process
        // to another.
        // </summary>
        public static unsafe void TransferOwnership(
            Allocation *allocation,
            AllocationOwnerId oldOwnerId,
            AllocationOwnerId newOwnerId)
        {
            Allocation.RemoveOwnership(allocation, oldOwnerId);
            Allocation.AssignOwnership(allocation, newOwnerId);
        }

        // Returns true if a provided allocation record appears to be
        // a valid record in our heap.
        public unsafe bool Validate(Allocation *allocation)
        {
#if MEMORY_TEST
            CheckDomain();

            UIntPtr pData = (UIntPtr)allocation;

            if (pData != UIntPtr.Zero) {
                if ((pData < memoryRange.DataStartAddr) ||
                    (pData >= memoryRange.DataLimitAddr)) {
                    // This can't be a pointer into our heap;
                    // it's outside the range of pages we use
                    return false;
                }

                UIntPtr dataPage = MemoryManager.PageAlign(pData);
                if (!VMManager.IsPageMapped(dataPage)) {
                    // It would not be a good idea to try to
                    // use this pointer
                    return false;
                }
            }
#endif

            return true;
        }

        // <summary>
        // The free allocation descriptor list.
        // Free descriptors are kept as unstructured memory, with the first
        // UIntPtr bytes of each serving as the pointer to the next one.
        // </summary>
        internal UIntPtr freeAllocationList;

        // <summary>
        // Structure for tracking allocated regions.
        // </summary>
        public partial struct Allocation {
            [Conditional("DEBUG")]
            [NoHeapAllocation]
            private static unsafe void AssertCorrectOwner(Allocation* allocation)
            {
                //
                //if (Thread.CurrentProcess.ProcessId != allocation->owner) {
                //  DebugStub.Break();
                //}
                //
            }

            [NoHeapAllocation]
            public static unsafe UIntPtr GetData(Allocation *allocation)
            {
                AssertCorrectOwner(allocation);
                return allocation->data;
            }

            /// <summary>
            /// Only to be used from
            ///  - TransferToProcess
            ///  - Freeing the Sentinel on FreeAll
            ///  - SharedHeap walker
            ///
            /// All other uses should be checked.
            /// </summary>
            [NoHeapAllocation]
            public static unsafe UIntPtr GetDataUnchecked(Allocation *allocation)
            {
                return allocation->data;
            }

            [NoHeapAllocation]
            public static unsafe UIntPtr GetSize(Allocation *allocation)
            {
                return allocation->size;
            }

            [NoHeapAllocation]
            public static unsafe UIntPtr GetType(Allocation *allocation)
            {
                return allocation->type;
            }

            [NoHeapAllocation]
            public static unsafe int GetOwnerProcessId(Allocation *allocation)
            {
                return allocation->owner;
            }

            [NoHeapAllocation]
            internal static unsafe Allocation *Next(Allocation *allocation)
            {
                return allocation->next;
            }

            [NoHeapAllocation]
            internal static unsafe void SetType(Allocation *allocation, UIntPtr type)
            {
                allocation->type = type;
            }

            internal static unsafe void SetOwnerProcessId(Allocation *allocation,
                                                          int processId)
            {
                unchecked{
                Tracing.Log(Tracing.Debug, "SetOwnerProcessId old:{0} new:{1} who:{2}",
                            (UIntPtr)allocation->owner,
                            (UIntPtr)processId,
                            (UIntPtr)Thread.CurrentProcess.ProcessId);
                }
                // Figure out who our caller is.
                //
                //UIntPtr[] stack = new UIntPtr[15];
                //Processor.GetStackEips(stack);
                //for (int i = 0; i < stack.Length; i++) {
                //  UIntPtr eip = stack[i];
                //  if (eip == UIntPtr.Zero) break;
                //  Tracing.Log(Tracing.Debug, "SetOwnerProcessId stack trace {0:x}", eip);
                //}
                //
                allocation->owner = processId;
            }

            // <summary>
            // Move the allocation one element forward in the list.
            // requires owner lock held.
            // </summary>
            internal static unsafe void MoveForward(Allocation *allocation)
            {
                Allocation *next = allocation->next;
                Allocation *prev = allocation->prev;
                if (next == allocation) return; // only one element; can't move
                // remove allocation from list
                prev->next = next;
                next->prev = prev;
                // insert allocation into next location in list
                Allocation *nextnext = next->next;
                next->next = allocation;
                allocation->prev = next;
                allocation->next = nextnext;
                nextnext->prev = allocation;
            }

            // <summary>
            // Allocate an allocation tracking descriptor.
            // </summary>
            internal static unsafe Allocation *Create(SharedHeap sharedHeap,
                UIntPtr address, UIntPtr size, UIntPtr type)
            {
                Allocation *allocation = ReuseOrCreateAllocation(sharedHeap);
                Initialize(allocation, address, size, type);
                DebugStub.Assert(sharedHeap.Validate(allocation));
                return allocation;
            }

            internal static unsafe Allocation *Create(SharedHeap sharedHeap,
                UIntPtr address, UIntPtr size, UIntPtr type, int ownerprocessId)
            {
                Allocation* result = Create(sharedHeap, address, size, type);
                result->owner = ownerprocessId;
                return result;
            }

            // <summary>
            // Allocate an allocation tracking descriptor.
            // </summary>
            internal static unsafe Allocation *CreateSentinel(SharedHeap sharedHeap)
            {
                Allocation *allocation = ReuseOrCreateAllocation(sharedHeap);
                allocation->data = 0;
                allocation->size = 0;
                allocation->type = 0;
                allocation->next = allocation;
                allocation->prev = allocation;
                allocation->owner = 0;
                return allocation;
            }

            // <summary>
            // Allocate an allocation tracking descriptor.
            // </summary>
            internal static unsafe Allocation *Initialize(
                Allocation* allocation,
                UIntPtr address, UIntPtr size, UIntPtr type)
            {
                allocation->data = address;
                allocation->size = size;
                allocation->type = type;
                allocation->next = allocation;
                allocation->prev = allocation;

                allocation->owner = Thread.CurrentProcess.ProcessId;

                return allocation;
            }

            // <summary>
            // Truncate an existing allocation at a given offset.
            // Note that this merely affects the reported size, the entire
            // region remains allocated, etc.
            // </summary>
            internal static unsafe void TruncateTo(Allocation *allocation,
                                                   UIntPtr offset)
            {
                allocation->size = offset;
            }

            // <summary>
            // Assign ownership of an allocated region to a process.
            // Note: this operation can block.
            // </summary>
            internal static unsafe void AssignOwnership(
                Allocation *allocation,
                AllocationOwnerId ownerId)
            {
                AllocationOwner *owner = ownerId.owner;

#if PAGING
                // Sanity: we shouldn't be putting user blocks onto
                // the kernel's shared heap lists, and vice versa.
                if ((UIntPtr)owner >= Platform.KERNEL_BOUNDARY) {
                    DebugStub.Assert((UIntPtr)allocation >= Platform.KERNEL_BOUNDARY);
                }
                else {
                    DebugStub.Assert((UIntPtr)allocation < Platform.KERNEL_BOUNDARY);
                }
#endif
                bool wasEnabled = AllocationOwner.Lock(owner);

                //
                // Put allocation at beginning of owner's list.
                //
                allocation->next = owner->sentinel->next;
                allocation->prev = owner->sentinel;
                allocation->next->prev = allocation;
                owner->sentinel->next = allocation;
                owner->outstandingBlocks++;
                AllocationOwner.Unlock(owner, wasEnabled);
            }

            // <summary>
            // Remove ownership of an allocated region from a process.
            // </summary>
            internal static unsafe void RemoveOwnership(
                Allocation *allocation,
                AllocationOwnerId ownerId)
            {
                AllocationOwner *owner = ownerId.owner;

                bool wasEnabled = AllocationOwner.Lock(owner);

                //
                // Remove allocation from owner's list.
                //
                allocation->next->prev = allocation->prev;
                allocation->prev->next = allocation->next;

                owner->outstandingBlocks--;
                AllocationOwner.Unlock(owner, wasEnabled);

                //
                // Sanitize this element.
                //
                allocation->next = allocation->prev = null;
            }

            private static unsafe Allocation *ReuseOrCreateAllocation(SharedHeap sharedHeap)
            {
                sharedHeap.CheckDomain();
                UIntPtr descriptorAddress;

                //
                // Attempt to get a descriptor from our free list.
                //
                descriptorAddress = AtomicPopFreeList(ref sharedHeap.freeAllocationList);

                if (descriptorAddress == UIntPtr.Zero) {
                    //
                    // Free list is empty.
                    // Allocate new page and break it up into allocation
                    // descriptors.  Use first descriptor to satisfy current
                    // request, put remainder on the free list.
                    //
                    UIntPtr newSpace;
                    uint spaceRemaining;
                    uint descriptorSize;

                    newSpace = sharedHeap.AllocatePages(1);
                    descriptorSize = (uint)sizeof(Allocation);

                    descriptorAddress = newSpace;
                    newSpace += descriptorSize;
                    spaceRemaining = MemoryManager.PageSize - descriptorSize;
                    while (spaceRemaining > descriptorSize) {
                        AtomicPushFreeList(ref sharedHeap.freeAllocationList, newSpace);
                        newSpace += descriptorSize;
                        spaceRemaining -= descriptorSize;
                    }
                }

                //
                // Turn this chunk of memory into an Allocation.
                //
                return (Allocation *)descriptorAddress;
            }
        }


        // <summary>
        // Pop an unstructured memory region off a singly-linked list.
        // The unstructured memory is expected to hold the address of the
        // next element on the list in its first UIntPtr.
        //
        // Note: requires that the passed-in list head be in a fixed
        // location in memory.
        // </summary>
        internal static unsafe UIntPtr AtomicPopFreeList(  // Returns address.
            ref UIntPtr head)  // List head.
        {
            UIntPtr firstElementLocation;
            UIntPtr secondElementLocation;

            do {
                //
                // Cache the contents of head pointer location (i.e. the
                // address of the first element on the list).
                //
                firstElementLocation = head;

                if (firstElementLocation == UIntPtr.Zero) {
                    //
                    // No first element.  List is empty.
                    //
                    return UIntPtr.Zero;
                }

                //
                // The first element contains the address of the second.
                //
                secondElementLocation = *(UIntPtr *)firstElementLocation;

                //
                // Called this way, Interlocked.CompareExchange will only
                // replace the contents of the head pointer location with
                // the address of the second element if the contents of the
                // the head pointer location (i.e. the first element's address)
                // hasn't changed since we cached it.  If the contents of
                // the head pointer have changed in the meantime, it means
                // some other thread has popped that element off the stack.
                // So we loop back and try it all over again.
                //

            } while (firstElementLocation != Interlocked.CompareExchange(
                        ref head, secondElementLocation,
                        firstElementLocation));

            //
            // We successfully popped an element off the list.
            // Sanitize it before returning it.
            //
            *(UIntPtr *)firstElementLocation = UIntPtr.Zero;
            return firstElementLocation;
        }


        // <summary>
        // Push an unstructured memory region onto a singly-linked list.
        // The unstructured memory must be large enough to hold the address
        // of the next element on the list in its first UIntPtr.
        //
        // Note: requires that the passed-in list head be in a fixed
        // location in memory.
        // </summary>
        internal static unsafe void AtomicPushFreeList(  // Returns address.
            ref UIntPtr head,  // List head.
            UIntPtr newElementLocation)  // Address of element to add to list.
        {
            UIntPtr firstElementLocation;

            do {
                //
                // Cache the contents of head pointer location (i.e. the
                // address of the first element on the list).
                //
                firstElementLocation = head;

                //
                // Put the address of the current first element into
                // our new first element.
                //
                *(UIntPtr *)newElementLocation = firstElementLocation;

                //
                // Called this way, Interlocked.CompareExchange will only swap
                // the contents of the head pointer with that of the new first
                // element's pointer if the contents of the head pointer
                // haven't changed since we cached it.  If the contents of
                // the head pointer have changed in the meantime, it means
                // some other thread has popped that element off the stack.
                // So we loop back and try it all over again.
                //

            } while (firstElementLocation != Interlocked.CompareExchange(
                        ref head, newElementLocation,
                        firstElementLocation));
        }
    }
}
