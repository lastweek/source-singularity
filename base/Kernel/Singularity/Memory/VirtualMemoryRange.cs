////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   VirtualMemoryRange.cs
//
//  Note:
//
//  A VirtualMemoryRange is a window of contiguous virtual memory that supports
//  general-purpose use. It comes with a (very) simple page allocator and a
//  page table that tracks how each virtual page is being used, to support a GC.
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using System.GCs;

using Microsoft.Singularity;
using Microsoft.Singularity.Hal;

namespace Microsoft.Singularity.Memory
{
    //
    // We need to create VirtualMemoryRanges very early, before we have the use
    // of a GCable heap. But later on, it's very useful to be able to pass around
    // references to them as objects. So, we have the struct, which primitive
    // parts of the system use directly, and then a wrapper object (below) for general
    // use.
    //
    [NoCCtor]
    [CLSCompliant(false)]
    public struct VirtualMemoryRange_struct
    {
        /////////////////////////////////////
        // PRIVATE FIELDS
        /////////////////////////////////////

        // The address range that we *manage*
        private readonly UIntPtr rangeBase;
        private readonly UIntPtr rangeLimit;

        // The address range that our page table *describes*
        private readonly UIntPtr descrBase;
        private readonly UIntPtr descrLimit;

        // Data begins above the rangeBase since we need room for our
        // page table.
        private readonly UIntPtr dataStart;

        // Number of data pages we *describe*
        private readonly UIntPtr describedPages;

        // One uint per page in our range
        private unsafe readonly uint* pageTable;


        // Protects non-readonly fields
        private static SpinLock rangeLock;

        // The next address to be alloced
        private UIntPtr nextAlloc;

        // Statistics
        private ulong allocatedBytes;
        private ulong allocatedCount;
        private ulong freedBytes;
        private ulong freedCount;

        /////////////////////////////////////
        // PUBLIC METHODS
        /////////////////////////////////////

        //
        // The range of memory turned over to a VirtualMemoryRange structure
        // must not have *any* mapped pages in it to start out with
        //
        // A VirtualMemoryRange can build a pagetable that *describes*
        // more memory than it *manages* (this supports some kernel GC
        // oddities). In that case, pages out-of-range are marked
        // as PageType.Unknown. Obviously, allocation requests are never
        // satisfied with out-of-bounds data.
        //
        internal unsafe VirtualMemoryRange_struct(
            UIntPtr baseAddr, UIntPtr limitAddr,
            UIntPtr descrBaseAddr, UIntPtr descrLimitAddr,
            ProtectionDomain inDomain)
        {
            DebugStub.Assert(MemoryManager.IsPageAligned(baseAddr));
            DebugStub.Assert(MemoryManager.IsPageAligned(limitAddr));
            DebugStub.Assert(MemoryManager.IsPageAligned(descrBaseAddr));
            DebugStub.Assert(MemoryManager.IsPageAligned(descrLimitAddr));

            // The descriptive range can't be smaller than the managed range
            DebugStub.Assert(descrLimitAddr >= limitAddr);
            DebugStub.Assert(descrBaseAddr <= baseAddr);

            descrBase = descrBaseAddr;
            descrLimit = descrLimitAddr;
            rangeBase = baseAddr;
            rangeLimit = limitAddr;
            rangeLock = new SpinLock(SpinLock.Types.VirtualMemoryRange);

            describedPages = MemoryManager.PagesFromBytes(descrLimit - descrBase);

            // Figure out how many pages we need for a page description table
            UIntPtr pageTableSize = MemoryManager.PagePad(describedPages * sizeof(uint));

            dataStart = baseAddr + pageTableSize;
            nextAlloc = dataStart;

            // Commit and prepare the page table
            pageTable = (uint*)baseAddr;

            bool success = MemoryManager.CommitAndMapRange(
                baseAddr, baseAddr + pageTableSize, inDomain);

            if (!success) {
                Kernel.Panic("Couldn't get pages to create a new VirtualMemoryRange page table");
            }

            allocatedBytes = 0;
            allocatedCount = 0;
            freedBytes = 0;
            freedCount = 0;

            // Describe the pages outside our range as Unknown
            if (descrBase < rangeBase) {
                SetRange(descrBase, rangeBase, MemoryManager.PageUnknown);
            }

            if (descrLimit > rangeLimit) {
                SetRange(rangeLimit, descrLimit, MemoryManager.PageUnknown);
            }

            // The page-table pages themselves are in use by the System
            SetRange((UIntPtr)pageTable,
                     (UIntPtr)pageTable + pageTableSize,
                     MemoryManager.KernelPageNonGC);

            // Describe pages in-range as Free
            SetRange(dataStart, rangeLimit, MemoryManager.PageFree);

#if DEBUG
            // Check that our data range is pristine
            for (UIntPtr stepAddr = dataStart;
                 stepAddr < rangeLimit;
                 stepAddr += MemoryManager.PageSize) {
                DebugStub.Assert(!VMManager.IsPageMapped(stepAddr));
            }
#endif
        }

        //
        // Allocates but does not commit a new range of memory.
        //
        internal UIntPtr Reserve(UIntPtr numPages, Process process,
                                 uint extra, PageType type)
        {
            DebugStub.Assert(numPages > 0);
            bool iflag = Lock();

            try {
                return ReserveInternal(numPages, process, extra, type);
            }
            finally {
                Unlock(iflag);
            }
        }

        //
        // Releases a previously reserved range of memory, but does not
        // uncommit any pages.
        //
        internal UIntPtr Unreserve(UIntPtr startAddr, UIntPtr numPages, Process process)
        {
            DebugStub.Assert(MemoryManager.IsPageAligned(startAddr));
            DebugStub.Assert(numPages > 0);
            UIntPtr blockLimit = startAddr + MemoryManager.BytesFromPages(numPages);
            DebugStub.Assert(startAddr >= dataStart);
            DebugStub.Assert(blockLimit <= rangeLimit);

            // Strictly a sanity check
            uint tag = process != null ? process.ProcessTag : MemoryManager.KernelPage;
            VerifyOwner(startAddr, blockLimit, tag);

            return FreeInternal(startAddr, numPages);
        }

        //
        // Allocates and commits a new range of memory.
        //
        internal UIntPtr Allocate(UIntPtr numPages, Process process,
                                  uint extra, PageType type,
                                  ProtectionDomain inDomain)
        {
            DebugStub.Assert(numPages > 0);
            UIntPtr mapAddr = UIntPtr.Zero;

            bool iflag = Lock();

            // Within our lock, figure out where we're going to stick the newly
            // mapped memory, and mark it used.
            try {
                mapAddr = ReserveInternal(numPages, process, extra, type);

                if (mapAddr == UIntPtr.Zero) {
                    DebugStub.Assert(false, "Failed to find a mapping point for new memory");
                    return mapAddr;
                }
            }
            finally {
                Unlock(iflag);
            }

            UIntPtr limitAddr = mapAddr + MemoryManager.BytesFromPages(numPages);

            // Now actually map pages to the chosen region.
            if (!MemoryManager.CommitAndMapRange(mapAddr, limitAddr, inDomain)) {
                // yikes; failure
                return UIntPtr.Zero;
            }

            allocatedCount++;
            allocatedBytes += (ulong)MemoryManager.BytesFromPages(numPages);

            if (process != null) {
                process.Allocated(MemoryManager.BytesFromPages(numPages));
            }

            return mapAddr;
        }

        //
        // Releases and uncommits a range of memory
        //
        [NoStackLinkCheckTrans]
        [NoStackOverflowCheck]
        internal unsafe UIntPtr Free(UIntPtr startPage,
                                     UIntPtr numPages,
                                     Process process)
        {
            DebugStub.Assert(startPage >= dataStart);
            DebugStub.Assert(MemoryManager.IsPageAligned(startPage));
            UIntPtr blockLimit = startPage + MemoryManager.BytesFromPages(numPages);
            DebugStub.Assert(blockLimit <= rangeLimit);

            //
            // NOTE: This is strictly a sanity check. The pagetable
            // is ultimately not trustworthy because it is writeable by
            // user-mode code.
            //
            uint tag = process != null ? process.ProcessTag : MemoryManager.KernelPage;
            VerifyOwner(startPage, blockLimit, tag);

            // Do it
            return FreeAndUncommit(startPage, numPages);
        }

        // Returns the number of *addressable* pages, which may be less than
        // the number of actually *usable* pages, if we describe a larger
        // range than we manage.
        internal UIntPtr PageCount {
            [NoHeapAllocation]
            get {
                return describedPages;
            }
        }

        // This lets the caller look directly into the page table; beware!
        internal unsafe uint* PageTable {
            [NoHeapAllocation]
            get
            {
                return pageTable;
            }
        }

        internal UIntPtr AllocateExtend(UIntPtr addr,
                                        UIntPtr bytes,
                                        Process process,
                                        uint extra,
                                        PageType type)
        {
            // TODO: Extend not yet implemented
            DebugStub.Break();
            return (UIntPtr)null;
        }

        //
        // Releases and uncommits all pages that are marked as belonging to a
        // particular process.
        //
        internal unsafe UIntPtr FreeAll(Process process)
        {
            DebugStub.Assert(process != null);
            DebugStub.Assert(process.ProcessTag != MemoryManager.KernelPage);

            uint tag = process.ProcessTag & MemoryManager.ProcessPageMask;
            uint *pageLimit = PageTable + PageCount;
            UIntPtr bytesFreed = 0;

            //
            // NOTE: here we choose to use the pagetable data,
            // which is writeable by user-mode code. Keep in mind that
            // it may be corrupt. We choose NOT to lock while traversing
            // for a particular process' pages because no further allocations
            // should occur tagged for that process once it's been stopped.
            // Obviously, a rogue process may make more pages that appear
            // to be owned by the zombie process appear.
            //
            for (uint *begin = PageTable; begin < pageLimit;) {
                uint *limit = begin;
                uint val = (*limit++) & MemoryManager.ProcessPageMask;

                if (val == tag) {
                    while ((((*limit) & MemoryManager.ProcessPageMask) == tag) && (limit < pageLimit)) {
                        limit++;
                    }

                    UIntPtr startPage = (UIntPtr)(begin - PageTable);
                    UIntPtr pageCount = (UIntPtr)(limit - begin);

                    bytesFreed += FreeAndUncommit(AddrFromPage(startPage), pageCount);
                }
                else {
                    while ((((*limit) & MemoryManager.ProcessPageMask) != tag) && (limit < pageLimit)) {
                        limit++;
                    }
                }

                begin = limit;
            }

            if (process != null) {
                process.Freed(bytesFreed);
            }

            return bytesFreed;
        }

        //
        // Sets a range of pages to have the provided tag
        //
        [NoHeapAllocation]
        internal unsafe void SetRange(UIntPtr startAddr, UIntPtr limitAddr, uint tag)
        {
            DebugStub.Assert(startAddr >= descrBase);
            DebugStub.Assert(limitAddr <= descrLimit);

            UIntPtr startIdx = PageFromAddr(startAddr);
            UIntPtr limitIdx = MemoryManager.PageFromAddr(limitAddr - descrBase);
            DebugStub.Assert(limitIdx <= PageCount);

            for (UIntPtr i = startIdx; i < limitIdx; i++) {
                pageTable[(uint)i] = tag;
            }
        }

        internal PageType Query(UIntPtr queryAddr,
                                Process process,
                                out UIntPtr regionAddr,
                                out UIntPtr regionSize)
        {
            // TODO: Query not yet implemented
            DebugStub.Break();
            regionAddr = 0;
            regionSize = 0;
            return 0;
        }

        internal unsafe void Dump(string where)
        {
            DebugStub.WriteLine( "VirtualMemoryRange.Dump: {0}", __arglist(where));

            uint *descriptors = pageTable;
            uint last = *descriptors++ & MemoryManager.SystemPageMask;
            UIntPtr begin = UIntPtr.Zero;

            UIntPtr freePages = UIntPtr.Zero;
            UIntPtr usedPages = UIntPtr.Zero;
            UIntPtr unknownPages = UIntPtr.Zero;
            UIntPtr sharedPages = UIntPtr.Zero;

            for (UIntPtr i = (UIntPtr)1; i < PageCount; i++) {
                uint dsc = *descriptors++;
                uint val = dsc & MemoryManager.SystemPageMask;

                switch (val) {
                    case MemoryManager.PageUnknown:
                        unknownPages++;
                        break;
                    case MemoryManager.PageShared:
                        sharedPages++;
                        break;
                    case MemoryManager.PageFree:
                        freePages++;
                        break;
                    default:
                        usedPages++;
                        break;
                }

                if (dsc != last) {
                    DebugStub.WriteLine( "  {0:x8}..{1:x8} : {2:x8} : {3:x8}",
                        __arglist(
                                begin << MemoryManager.PageBits, i << MemoryManager.PageBits, last,
                                (i - begin) << MemoryManager.PageBits));
                    last = dsc;
                    begin = i;
                }
            }

            DebugStub.WriteLine("  {0:x8}..{1:x8} : {2:x8} : {3:x8}",
                        __arglist(
                        begin << MemoryManager.PageBits, PageCount << MemoryManager.PageBits, last,
                        (PageCount - begin) << MemoryManager.PageBits));

            //DumpFreeNodes(GetFreeList(), false);
            //DumpFreeNodes(GetSaveList(), true);

            DebugStub.WriteLine("Totals: free={0:x8}, used={1:x8}, unknown={2:x8}, reserved={3:x8}",
                        __arglist(
                        freePages << MemoryManager.PageBits,
                        usedPages << MemoryManager.PageBits,
                        unknownPages << MemoryManager.PageBits,
                        sharedPages << MemoryManager.PageBits));
        }

        [NoHeapAllocation]
        public UIntPtr GetMaxMemory()
        {
            // Return the amount of space we *manage*
            return rangeLimit - rangeBase;
        }

        [NoHeapAllocation]
        public unsafe UIntPtr GetFreeMemory()
        {
            // Report as free only that memory above our current
            // allocate-next mark (even though there may be
            // free holes below that mark that get reclaimed
            // later)
            return rangeLimit - nextAlloc;
        }

        [NoHeapAllocation]
        public unsafe UIntPtr GetUsedMemory()
        {
            return GetMaxMemory() - GetFreeMemory();
        }

        [NoHeapAllocation]
        public void GetUsageStatistics(out ulong allocatedCount,
                                       out ulong allocatedBytes,
                                       out ulong freedCount,
                                       out ulong freedBytes)
        {
            allocatedCount = this.allocatedCount;
            allocatedBytes = this.allocatedBytes;
            freedCount = this.freedCount;
            freedBytes = this.freedBytes;
        }

        [NoHeapAllocation]
        internal UIntPtr PageFromAddr(UIntPtr addr)
        {
            DebugStub.Assert(addr >= descrBase);
            DebugStub.Assert(addr < descrLimit);
            return MemoryManager.PageFromAddr(addr - descrBase);
        }

        [NoHeapAllocation]
        internal UIntPtr AddrFromPage(UIntPtr pageNum)
        {
            DebugStub.Assert(pageNum < PageCount);
            return descrBase + MemoryManager.BytesFromPages(pageNum);
        }

        internal UIntPtr BaseAddress
        {
            [NoHeapAllocation]
            get
            {
                // Return the first *described* address
                return descrBase;
            }
        }

        // Returns the first address at which we may allocate memory.
        // For validating pointers into this range.
        internal UIntPtr DataStartAddr
        {
            [NoHeapAllocation]
            get
            {
                return dataStart;
            }
        }

        // Returns the limit of the range we use for allocations.
        internal UIntPtr DataLimitAddr
        {
            [NoHeapAllocation]
            get
            {
                return rangeLimit;
            }
        }

        /////////////////////////////////////
        // PRIVATE METHODS
        /////////////////////////////////////

        //
        // Finds a contiguous block of virtual memory.
        //
        // *** CALLER MUST HOLD OUR PROTECTIVE LOCK! ***
        //
        // We don't acquire the spinlock ourselves in case the caller
        // wants to do more work within it.
        //
        // Currently, the approach is VERY simplistic; we just keep handing out
        // pages starting with the base of the virtual memory space until we
        // bump into the top, and then we become much more inefficient.
        //
        // The expectation is that higher-level components will do smarter
        // space management than this!
        //
        private unsafe UIntPtr ReserveInternal(UIntPtr numPages, Process process, uint extra, PageType type)
        {
            DebugStub.Assert(numPages >= 1);
            UIntPtr mapAddr = UIntPtr.Zero;

            uint tag =
                (process != null ? process.ProcessTag : MemoryManager.KernelPage)
                | (extra & MemoryManager.ExtraMask)
                | (uint)type;

            UIntPtr blockBytes = MemoryManager.BytesFromPages(numPages);

            if (nextAlloc + blockBytes <= rangeLimit) {
                mapAddr = nextAlloc;
                UIntPtr limitAddr = mapAddr + blockBytes;
                nextAlloc = limitAddr;

                SetRange(mapAddr, limitAddr, tag);
            }
            else {
                // slow-path allocation - just do first-fit for now...
                // TODO: Need to integrate freelist management from flatpages et al
                UIntPtr startIdx = PageFromAddr(dataStart);
                UIntPtr limitIdx = MemoryManager.PageFromAddr(rangeLimit - descrBase) - (numPages - 1);
                DebugStub.Assert(limitIdx <= PageCount);

                for (UIntPtr pageIdx = startIdx; pageIdx < limitIdx; pageIdx++) {
                    UIntPtr pageCount = 0;

                    while (pageCount < numPages) {
                        uint pageTag = *(pageTable + pageIdx + pageCount);
                        if (pageTag != MemoryManager.PageFree) {
                            break;
                        }
                        pageCount++;
                    }

                    if (pageCount == numPages) {
                        mapAddr = dataStart + MemoryManager.BytesFromPages(pageIdx - startIdx);

                        SetRange(mapAddr, mapAddr + blockBytes, tag);
                        break;
                    }
                    else {
                        pageIdx += pageCount;
                    }
                }
            }

            return mapAddr;
        }

        [NoStackLinkCheckTrans]
        [NoStackOverflowCheck]
        private unsafe UIntPtr FreeAndUncommit(UIntPtr startPage,
                                               UIntPtr numPages)
        {
            // Drop all the memory
            MemoryManager.UnmapAndReleaseRange(
                startPage, startPage + MemoryManager.BytesFromPages(numPages));

            // Do the bookkeeping
            return FreeInternal(startPage, numPages);
        }

        private unsafe UIntPtr FreeInternal(UIntPtr startPage,
                                            UIntPtr numPages)
        {
            DebugStub.Assert(MemoryManager.IsPageAligned(startPage));
            DebugStub.Assert(startPage >= dataStart);
            UIntPtr blockLimit = startPage + MemoryManager.BytesFromPages(numPages);
            DebugStub.Assert(blockLimit <= rangeLimit);
            DebugStub.Assert(nextAlloc >= blockLimit);

            bool iflag = Lock();

            try {
                // Mark the pages free within our lock so we can rely on
                // blocks being uniformly marked free in here
                SetRange(startPage, blockLimit, MemoryManager.PageFree);

                // Reduce fragmentation: lower the nextAlloc pointer if
                // we have freed the top end of memory.
                if (nextAlloc == blockLimit) {
                    nextAlloc = startPage;

                    //
                    // NOTE: this chooses to use the page table
                    // information, which is currently usermode-accessible
                    // in the case of a user-mode range. Keep in mind that
                    // the information may be corrupt!
                    //

                    // Further optimization: drop nextAlloc more
                    // if the memory below us is free, too.
                    uint* pageTable = PageTable;
                    UIntPtr stepPage = nextAlloc;
                    uint val;

                    do {
                        nextAlloc = stepPage;
                        stepPage -= MemoryManager.PageSize;
                        uint dsc = pageTable[(uint)PageFromAddr(stepPage)];
                        val = dsc & MemoryManager.SystemPageMask;
                    }
                    while ((val == MemoryManager.PageFree) &&
                          (!VMManager.IsPageMapped(stepPage))); // sanity
                }

                freedCount++;
                freedBytes += (ulong)MemoryManager.BytesFromPages(numPages);
            }
            finally {
                Unlock(iflag);
            }

            return MemoryManager.BytesFromPages(numPages);
        }

        // Confirms that the provided tag is consistent with the pagetable over
        // a certain range
        [NoStackLinkCheckTrans]
        [NoStackOverflowCheck]
        private unsafe void VerifyOwner(UIntPtr startAddr, UIntPtr limitAddr, uint tag)
        {
#if DEBUG
            DebugStub.Assert(startAddr >= dataStart);
            DebugStub.Assert(limitAddr <= rangeLimit);

            UIntPtr startIdx = PageFromAddr(startAddr);
            UIntPtr limitIdx = MemoryManager.PagesFromBytes(limitAddr - descrBase);
            DebugStub.Assert(limitIdx <= PageCount);

            tag &= MemoryManager.ProcessPageMask;

            for (UIntPtr i = startIdx; i < limitIdx; i++) {
                DebugStub.Assert
                    ((pageTable[(uint)i] & MemoryManager.ProcessPageMask) == tag,
                     "VirtualMemoryRange.VerifyOwner page={0} i={1} tag={2}",
                     __arglist(i, i, tag));
            }
#endif
        }

        [Inline]
        [NoStackLinkCheckTrans]
        private static bool Lock()
        {
            bool enabled = Processor.DisableInterrupts();
#if SINGULARITY_MP
            rangeLock.Acquire(Thread.CurrentThread);
#endif // SINGULARITY_MP
            return enabled;
        }

        [Inline]
        [NoStackLinkCheckTrans]
        private static void Unlock(bool iflag)
        {
#if SINGULARITY_MP
            rangeLock.Release(Thread.CurrentThread);
#endif // SINGULARITY_MP
            Processor.RestoreInterrupts(iflag);
        }

    }

    //
    // This wrapper is not pretty. We want to use it to wrap structs that were
    // placed at early-boot time into static memory, as well as structs that
    // are allocated later when we have the use of a GC heap.
    //
    // The natural way to write this would be to write an abstract base class
    // and then a subclass that knows how to wrap a pointer, and another that
    // wraps an instance of the struct. Here, we cheezily trade a test for
    // the VTable indirection.
    //
    public class VirtualMemoryRange
    {
        // We only use one or the other of these two fields
        private readonly unsafe VirtualMemoryRange_struct* pRange;
        private VirtualMemoryRange_struct range;
        private readonly bool indirect; // true -> we use pRange
        private readonly ProtectionDomain parentDomain;

        internal unsafe VirtualMemoryRange(VirtualMemoryRange_struct* pRange,
                                           ProtectionDomain inDomain)
        {
            this.pRange = pRange;
            this.indirect = true;
            // never use this.range
            DebugStub.Assert(inDomain != null);
            this.parentDomain = inDomain;
        }

        internal unsafe VirtualMemoryRange(UIntPtr baseAddr,
                                           UIntPtr limitAddr,
                                           ProtectionDomain inDomain)
        {
            DebugStub.Assert(inDomain != null);
            this.parentDomain = inDomain;

            range = new VirtualMemoryRange_struct(baseAddr, limitAddr,
                                                  baseAddr, limitAddr,
                                                  inDomain);
            this.indirect = false;
            // never use this.pRange
        }

        internal ProtectionDomain ParentDomain {
            get {
                return this.parentDomain;
            }
        }

        internal unsafe UIntPtr Reserve(UIntPtr numPages, Process process,
                                        uint extra, PageType type)
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->Reserve(numPages, process, extra, type);
            }
            else {
                return range.Reserve(numPages, process, extra, type);
            }
        }

        internal unsafe UIntPtr Unreserve(UIntPtr startPage, UIntPtr numPages,
                                          Process process)
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->Unreserve(startPage, numPages, process);
            }
            else {
                return range.Unreserve(startPage, numPages, process);
            }
        }

        internal unsafe UIntPtr Allocate(UIntPtr numPages, Process process,
                                         uint extra, PageType type)
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->Allocate(numPages, process, extra, type,
                                        parentDomain);
            }
            else {
                return range.Allocate(numPages, process, extra, type,
                                      parentDomain);
            }
        }

        internal unsafe UIntPtr Free(UIntPtr startPage, UIntPtr numPages,
                                     Process process)
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->Free(startPage, numPages, process);
            }
            else {
                return range.Free(startPage, numPages, process);
            }
        }

        internal unsafe UIntPtr PageCount
        {
            get {
                CheckAddressSpace();

                if (indirect) {
                    return pRange->PageCount;
                }
                else {
                    return range.PageCount;
                }
            }
        }

        internal unsafe uint* PageTable
        {
            get {
                CheckAddressSpace();

                if (indirect) {
                    return pRange->PageTable;
                }
                else {
                    return range.PageTable;
                }
            }
        }

        internal unsafe UIntPtr AllocateExtend(UIntPtr addr,
                                               UIntPtr bytes,
                                               Process process,
                                               uint extra,
                                               PageType type)
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->AllocateExtend(addr, bytes, process, extra, type);
            }
            else {
                return range.AllocateExtend(addr, bytes, process, extra, type);
            }
        }

        internal unsafe UIntPtr FreeAll(Process process)
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->FreeAll(process);
            }
            else {
                return range.FreeAll(process);
            }
        }

        internal unsafe PageType Query(UIntPtr queryAddr,
                                       Process process,
                                       out UIntPtr regionAddr,
                                       out UIntPtr regionSize)
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->Query(queryAddr, process,
                                     out regionAddr, out regionSize);
            }
            else {
                return range.Query(queryAddr, process,
                                   out regionAddr, out regionSize);
            }
        }

        internal unsafe void Dump(string where)
        {
            CheckAddressSpace();

            if (indirect) {
                pRange->Dump(where);
            }
            else {
                range.Dump(where);
            }
        }

        internal unsafe UIntPtr GetMaxMemory()
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->GetMaxMemory();
            }
            else {
                return range.GetMaxMemory();
            }
        }

        internal unsafe UIntPtr GetFreeMemory()
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->GetFreeMemory();
            }
            else {
                return range.GetFreeMemory();
            }
        }

        internal unsafe UIntPtr GetUsedMemory()
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->GetUsedMemory();
            }
            else {
                return range.GetUsedMemory();
            }
        }

        internal unsafe void GetUsageStatistics(out ulong allocatedCount,
                                                out ulong allocatedBytes,
                                                out ulong freedCount,
                                                out ulong freedBytes)
        {
            CheckAddressSpace();

            if (indirect) {
                pRange->GetUsageStatistics(
                    out allocatedCount, out allocatedBytes,
                    out freedCount, out freedBytes);
            }
            else {
                range.GetUsageStatistics(
                    out allocatedCount, out allocatedBytes,
                    out freedCount, out freedBytes);
            }
        }

        internal unsafe UIntPtr PageFromAddr(UIntPtr addr)
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->PageFromAddr(addr);
            }
            else {
                return range.PageFromAddr(addr);
            }
        }

        internal unsafe UIntPtr AddrFromPage(UIntPtr pageNum)
        {
            CheckAddressSpace();

            if (indirect) {
                return pRange->AddrFromPage(pageNum);
            }
            else {
                return range.AddrFromPage(pageNum);
            }
        }

        internal unsafe UIntPtr BaseAddress
        {
            get {
                CheckAddressSpace();

                if (indirect) {
                    return pRange->BaseAddress;
                }
                else {
                    return range.BaseAddress;
                }
            }
        }

        internal unsafe UIntPtr DataStartAddr
        {
            get {
                CheckAddressSpace();

                if (indirect) {
                    return pRange->DataStartAddr;
                }
                else {
                    return range.DataStartAddr;
                }
            }
        }

        internal unsafe UIntPtr DataLimitAddr
        {
            get {
                CheckAddressSpace();

                if (indirect) {
                    return pRange->DataLimitAddr;
                }
                else {
                    return range.DataLimitAddr;
                }
            }
        }

        [Inline]
        private unsafe void CheckAddressSpace()
        {
#if DEBUG
            UIntPtr rangeLimit;

            if (indirect) {
                rangeLimit = pRange->DataLimitAddr;
            }
            else {
                rangeLimit = range.DataLimitAddr;
            }

            if (rangeLimit > Platform.KERNEL_BOUNDARY) {
                // We are a user-space range. We had better
                // be using the right address space!
                DebugStub.Assert(parentDomain.AddressSpace == Processor.GetCurrentAddressSpace());
            } // else we are a kernel range and are always mapped.
#endif
        }
    }
}
