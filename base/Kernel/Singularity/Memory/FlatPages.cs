////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Legacy.cs - Primitive memory manager
//
//  Note:
//

//#define TEST
//#define VERBOSE
//#define MP_VERBOSE
//#define COMPLEX_TEST

#if MARKSWEEPCOLLECTOR
#define ALLOW_BOOT_ARGLIST // Cannot be used during boot for GCs w/ write barrier
#endif
#define NO__TRACE_PAGES

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using System.GCs;

using Microsoft.Singularity;
using Microsoft.Singularity.Hal;
using Microsoft.Bartok.Runtime;
using Microsoft.Singularity.Eventing;

namespace Microsoft.Singularity.Memory
{
    [NoCCtor]
    [CLSCompliant(false)]
    public class FlatPages {

        // WARNING: don't initialize any static fields in this class
        // without manually running the class constructor at startup!
        //private const uint    PageMask = MemoryManager.PageSize - 1;
        private const uint    SmallSize = MemoryManager.PageSize;

        private static UIntPtr lowerLimit;
        private static UIntPtr upperLimit;
        private static UIntPtr pageBase;    // Lowest page.
        private static UIntPtr pageCount;   // Number of pages.
        private static SpinLock pageLock;
        private static UIntPtr baseAddress;
        private static ulong size;

        private static unsafe uint *pageTable;

        // We keep two lists of free pages:
        // The freeList has pages that can be used at any moment.
        // The saveList has pages that were reserved for growing a region.

        private static FreeNode freeListTail;
        private static FreeNode saveListTail;
        private static unsafe FreeNode *freeList;
        private static unsafe FreeNode *saveList;

        //
        // This represents the real time count of available memory
        //
        private static UIntPtr availableMemory;

        [NoHeapAllocation]
        [Inline]
        private unsafe static bool RangeWithinLimits(ulong addr, ulong size, UIntPtr upperLimit, UIntPtr lowerLimit,
                                                     out UIntPtr baseAddress, out ulong newSize)
        {

            baseAddress = addr;
            newSize = size;

            if(addr + size < lowerLimit) {
                return false;
            }
            if(addr > upperLimit) {
                return false;
            }

            if((addr > lowerLimit) && ((addr + size) < upperLimit)) {
                return true;
            }
            //trim the limits to fit into the valid address range
            if(addr < lowerLimit) {
                baseAddress = lowerLimit;
                newSize = newSize - ((ulong)lowerLimit - addr);
            }
            if((addr + size) > upperLimit) {
                newSize = newSize - (((ulong)baseAddress + size) - (ulong)upperLimit);
            }
            return true;
        }

        internal static unsafe void Initialize()
        {
            Tracing.Log(Tracing.Debug, "FlatPages.Initialize() called");

            // Initialize spinlock info
            pageLock = new SpinLock(SpinLock.Types.FlatPages);

            Platform p = Platform.ThePlatform;
            HistogramSize = 64;
            HistogramGranularityShift = 20;
            FreeMemoryCounters = null;
            CurrentSystemLogger = null;

            // Retrieve the highest RAM address
            MemoryManager.PhysicalMemoryLimits(out lowerLimit, out upperLimit);

            DebugStub.WriteLine("MemoryManager Physical limits {0:x8}...{1:x8}\n",
                                __arglist(lowerLimit, upperLimit));

            // Compute page count

	    pageCount = Pad((upperLimit >> MemoryManager.PageBits) + 1,
			    MemoryManager.PageSize / sizeof(uint));

            // Find a spot for the page table.
            pageTable = null;

            // Figure out the lowest possible location for positioning the pageMap
            UIntPtr limit = Pad(lowerLimit, 0x00200000);

            // Make sure "limit" doesn't straddle some of the other non-SMAP regions
            if (p.BootAllocatedMemorySize != 0) {
                if ((p.BootAllocatedMemory < limit) &&
                    (limit < p.BootAllocatedMemory + p.BootAllocatedMemorySize)) {
                    limit = MemoryManager.PagePad(p.BootAllocatedMemory + p.BootAllocatedMemorySize);
                }
            }
            if (p.KernelDllSize != 0) {
                if ((p.KernelDllBase < limit) &&
                    (limit < p.KernelDllBase + p.KernelDllSize)) {
                    limit = MemoryManager.PagePad(p.KernelDllBase + p.KernelDllSize);
                }
            }
            DebugStub.WriteLine("KernelDllBase {0,8:x} size {1,8:x} limit {2,8:x} \n", __arglist(p.KernelDllBase, p.KernelDllSize, limit));

            SMAPINFO *smap = (SMAPINFO*)p.Smap;
            for (uint i = 0; i < p.SmapCount; i++) {
                if (smap[i].type == (ulong)SMAPINFO.AddressType.Free) {
                    if (RangeWithinLimits(smap[i].addr, smap[i].size, upperLimit, lowerLimit, out baseAddress,  out size)){
                        if(baseAddress + size >= limit) {
                            UIntPtr start = baseAddress;
                            UIntPtr end = baseAddress + size;

                            if (start < limit) {
                                start = limit;
                            }
                            if ((end - start) >= pageCount * sizeof(uint)) {
                                pageTable = (uint *) start;
                                break;
                            }
                        }
                    }
                }
            }

            if (pageTable == null) {
                DebugStub.WriteLine("pageTable == null, un-able to find page table memory\n");
                DebugStub.Break();
            }

            DebugStub.WriteLine("p.PhysicalBase 0x{0,8:x8} upperLimit: 0x{1,8:x8}, pageTable: 0x{2,8:x8}",
                                __arglist(p.PhysicalBase, upperLimit, (UIntPtr)pageTable));

            Tracing.Log(Tracing.Debug,
                        "Limit of RAM={0,8:x}, entries={1:x}, table={2:x}",
                        upperLimit, pageCount, (UIntPtr) pageTable);

            // Initialize all page descriptors to Unknown.
            SetPages(0, pageCount, MemoryManager.PageUnknown);

            // Second pass over SMAP, mark known RAM.
            // we use to bootloader knowledge to map our address space
            for (uint i = 0; i < p.SmapCount; i++) {
                if (RangeWithinLimits(smap[i].addr, smap[i].size, upperLimit, lowerLimit, out baseAddress,  out size)) {
                    if (smap[i].type == (ulong)SMAPINFO.AddressType.Free) {
                        SetRange(baseAddress, size, MemoryManager.PageFree);
                    }
                    else if(smap[i].type == (ulong)SMAPINFO.AddressType.KernelNonGc) {
                        SetRange(baseAddress, size, MemoryManager.KernelPageNonGC);
                    }
                    else if(smap[i].type == (ulong)SMAPINFO.AddressType.KernelStack) {
                        SetRange(baseAddress, size, MemoryManager.KernelPageStack);
                    }
                    else {
		        ;
                    }
                }
                else {
                    DebugStub.WriteLine("Ignoring Entry: Smap range {0:x8}...{1:x8} memory range {2:x8}...{3:x8}",
                                        __arglist(
                                            smap[i].addr,
                                            smap[i].addr + smap[i].size,
                                            lowerLimit,
                                            upperLimit)
                                        );
                }
            }

            // Set non-physical pages as unknown
            SetRange(0, Platform.ThePlatform.PhysicalBase, MemoryManager.PageUnknown);

            // Record the page table memory.
            SetRange((UIntPtr) pageTable, pageCount * sizeof(uint), MemoryManager.KernelPageNonGC);


            // Initialize the free and save lists.
            fixed (FreeNode *tail = &freeListTail) {
                freeList = tail;
                FreeNode.Init(freeList, false);
            }
            fixed (FreeNode *tail = &saveListTail) {
                saveList = tail;
                FreeNode.Init(saveList, true);
            }

            availableMemory = UIntPtr.Zero;

            // Initialize the memory reservations
            MemoryReservations.Initialize();

            uint *desc = pageTable;
            uint last = *desc & MemoryManager.SystemPageMask;
            UIntPtr begin = UIntPtr.Zero;

            for (UIntPtr i = UIntPtr.Zero; i < pageCount; i++) {
                uint val = *desc++ & MemoryManager.SystemPageMask;

                if (val != last) {
                    if (last == MemoryManager.PageFree) {
                        FreeNode.CreateAndInsert(freeList,
                                                 AddrFromPage(begin),
                                                 AddrFromPage(i) - AddrFromPage(begin));
                    }
                    begin = i;
                    last = val;
                }
            }
        }

        internal static void Finalize()
        {
            // Doesn't actually do anything.
        }

        [NoStackLinkCheckTrans]
        private static bool Lock()
        {
            bool enabled = Processor.DisableInterrupts();
#if SINGULARITY_MP
            pageLock.Acquire(Thread.CurrentThread);
#endif // SINGULARITY_MP
            return enabled;
        }

        [NoStackLinkCheckTrans]
        private static void Unlock(bool iflag)
        {
#if SINGULARITY_MP
            pageLock.Release(Thread.CurrentThread);
#endif // SINGULARITY_MP
            Processor.RestoreInterrupts(iflag);
        }

        // Currently, we just return the BSP free list.  In the
        // future, this should consult the ProcessorMemoryMap
        private static unsafe FreeNode* GetFreeList()
        {
                return freeList;
        }

        private static unsafe FreeNode* GetSaveList()
        {
                return saveList;
        }



        //////////////////////////////////////////////////////////////////////
        //
        internal static UIntPtr PageCount
        {
            get { return pageCount; }
        }

        internal static unsafe uint * PageTable
        {
            get { return pageTable; }
        }

        [NoStackLinkCheckTrans]
        [FlatPagesLock]
        internal static UIntPtr StackAllocate(UIntPtr bytes,
                                          UIntPtr reserve,
                                          UIntPtr alignment,
                                          Process process,
                                          uint extra,
                                          bool kernelAllocation,
                                          bool initialStack)
        {
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(960);
#endif
            UIntPtr got = new UIntPtr();

            bool iflag = Lock();
            try {
                got = RawAllocate(bytes, reserve, alignment,
                                  (process != null ? process.ProcessTag : MemoryManager.KernelPage)
                                  | (extra & MemoryManager.ExtraMask)
                                  | (uint)PageType.Stack, kernelAllocation);
#if VERBOSE
                Tracing.Log(Tracing.Debug, "{0:x8} Allocate({1:x},{2:x},{3:x}",
                            Kernel.AddressOf(process), bytes, reserve,
                            alignment);
#endif
                if (got != UIntPtr.Zero) {

                    if (initialStack) {
                        // increase our kernel stack reservation
                        MemoryReservations.ThreadCreateNotification();
                    }

                    if (process != null) {
                        process.Allocated(bytes);
                    }
                }
            }
            finally {
                Unlock(iflag);
            }
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(961);
#endif
            return got;
        }

        [NoStackLinkCheckTrans]
        [FlatPagesLock]
        internal static void StackFree(UIntPtr addr,
                                  UIntPtr bytes,
                                  Process process,
                                  bool kernelAllocation,
                                  bool initialStack)
        {
            bool iflag = Lock();
            try {
                RawFree(addr, bytes, process != null ? process.ProcessTag : MemoryManager.KernelPage, true, kernelAllocation);
                if (process != null) {
                    process.Freed(bytes);
                }

                if (initialStack) {
                    // release our kernel stack reservation
                    MemoryReservations.ThreadDestroyNotification();
                }
            }
            finally {
                Unlock(iflag);
            }
            return;
        }

        //
        // If process == null, its a kernel allocation, otherwise its
        // a user (SIP) allocation.
        //
        [NoStackLinkCheckTrans]
        [FlatPagesLock]
        internal static UIntPtr Allocate(UIntPtr bytes,
                                          UIntPtr reserve,
                                          UIntPtr alignment,
                                          Process process,
                                          uint extra,
                                          PageType type)
        {
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(960);
#endif
            UIntPtr got = new UIntPtr();

            bool iflag = Lock();
            try {
                got = RawAllocate(bytes, reserve, alignment,
                                  (process != null ? process.ProcessTag : MemoryManager.KernelPage)
                                  | (extra & MemoryManager.ExtraMask)
                                  | (uint)type, true);
#if VERBOSE
                Tracing.Log(Tracing.Debug, "{0:x8} Allocate({1:x},{2:x},{3:x}",
                            Kernel.AddressOf(process), bytes, reserve,
                            alignment);
#endif
                if (process != null) {
                    process.Allocated(bytes);
                }
            }
            finally {
                Unlock(iflag);
            }
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(961);
#endif
            return got;
        }

        [FlatPagesLock]
        internal static UIntPtr AllocateBelow(UIntPtr limit,
                                              UIntPtr bytes,
                                              UIntPtr alignment,
                                              Process process,
                                              uint extra,
                                              PageType type)
        {
            UIntPtr got = new UIntPtr();

            bool iflag = Lock();
            try {
                got = RawAllocateBelow(limit, bytes, alignment,
                                       (process != null ? process.ProcessTag : MemoryManager.KernelPage)
                                       | (extra & MemoryManager.ExtraMask)
                                       | (uint)type);
                if (process != null) {
                    process.Allocated(bytes);
                }
            }
            finally {
                Unlock(iflag);
            }
            return got;
        }

        [FlatPagesLock]
        internal static UIntPtr AllocateExtend(UIntPtr addr,
                                               UIntPtr bytes,
                                               Process process,
                                               uint extra,
                                               PageType type)
        {
            UIntPtr got = new UIntPtr();

            bool iflag = Lock();
            try {
                uint tag =
                    (process != null ?
                     process.ProcessTag :
                     MemoryManager.KernelPage)
                    | (extra & MemoryManager.ExtraMask)
                    | (uint)type;
                got = RawAllocateExtend(addr, bytes, tag);
                if (got != UIntPtr.Zero && process != null) {
                    process.Allocated(bytes);
                }
            }
            finally {
                Unlock(iflag);
            }
            return got;
        }

        [NoStackLinkCheckTrans]
        [FlatPagesLock]
        internal static void Free(UIntPtr addr,
                                  UIntPtr bytes,
                                  Process process)
        {
            bool iflag = Lock();
            try {
                RawFree(addr, bytes, process != null ? process.ProcessTag : MemoryManager.KernelPage, false, true);
                if (process != null) {
                    process.Freed(bytes);
                }
            }
            finally {
                Unlock(iflag);
            }
        }

        [FlatPagesLock]
        internal static unsafe UIntPtr FreeAll(Process process)
        {
            DebugStub.Assert(process != null,
                             "FlatPages.FreeAll null process");
            DebugStub.Assert(process.ProcessTag != MemoryManager.KernelPage,
                             "FlatPages.FreeAll ProcessTag={0}",
                             __arglist(process.ProcessTag));

            uint tag = process.ProcessTag & MemoryManager.ProcessPageMask;
            uint *pageLimit = pageTable + pageCount;
            UIntPtr bytes = 0;

            Tracing.Log(Tracing.Debug, "FreeAll({0,8:x})", tag);

            for (uint *begin = pageTable; begin < pageLimit;) {
                uint *limit = begin;
                uint val = (*limit++) & MemoryManager.ProcessPageMask;
#if VERBOSE
                unchecked {
                    Tracing.Log(Tracing.Debug, "  {0,8:x}: {1,8:x}",
                                AddrFromPage((UIntPtr)(begin - pageTable)),
                                val);
                }
#endif

                if (val == tag) {
                    while ((((*limit) & MemoryManager.ProcessPageMask) == tag) && (limit < pageLimit)) {
                        limit++;
                    }

                    UIntPtr page = (UIntPtr)(begin - pageTable);
                    UIntPtr size = (UIntPtr)(limit - begin);

                    Tracing.Log(Tracing.Debug,
                                "  {0,8:x}..{1,8:x} : {2,8:x} [will free]",
                                page << MemoryManager.PageBits, (page + size) << MemoryManager.PageBits,
                                *begin);

                    bool iflag = Lock();
                    UIntPtr sizeInBytes = (size  << MemoryManager.PageBits);
                    try {
                        RawFree(AddrFromPage(page), sizeInBytes, tag, false, false);
                    }
                    finally {
                        Unlock(iflag);
                    }

                    bytes += size;
                }
                else {
                    while ((((*limit) & MemoryManager.ProcessPageMask) != tag) && (limit < pageLimit)) {
                        limit++;
                    }

                    UIntPtr page = (UIntPtr)(begin - pageTable);
                    UIntPtr size = (UIntPtr)(limit - begin);

                    Tracing.Log(Tracing.Debug,
                                "- {0,8:x}..{1,8:x} : {2,8:x} [will free]",
                                page << MemoryManager.PageBits, (page + size) << MemoryManager.PageBits,
                                *begin);
                }
                begin = limit;
            }
            if (process != null) {
                process.Freed(bytes * MemoryManager.PageSize);
            }
            return bytes * MemoryManager.PageSize;
        }

        [FlatPagesLock]
        internal static PageType Query(UIntPtr queryAddr,
                                       Process process,
                                       out UIntPtr regionAddr,
                                       out UIntPtr regionSize)
        {
            PageType type = new PageType();

            bool iflag = Lock();
            try {
                type = RawQuery(queryAddr,
                                process != null ? process.ProcessTag : 0,
                                out regionAddr, out regionSize);
            }
            finally {
                Unlock(iflag);
            }
            return type;
        }

        //////////////////////////////////////////////////////////////////////
        //
        [NoStackLinkCheckTrans]
        private static unsafe UIntPtr RawAllocate(UIntPtr bytes,
                                                  UIntPtr reserve,
                                                  UIntPtr alignment,
                                                  uint tag,
                                                  bool kernelAllocation)
        {
            VTable.Assert(Processor.InterruptsDisabled());
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(970);
#endif
            if (alignment < MemoryManager.PageSize) {
                alignment = MemoryManager.PageSize;
            }
            if (reserve < bytes) {
                reserve = bytes;
            }
#if VERBOSE
            Tracing.Log(Tracing.Debug,
                        " size={0:x}, res={1:x}, aln={2:x}, tag={3:x}",
                        bytes, reserve, alignment, tag);
#endif
            // Check the allocation against memory reservations
            if (MemoryReservations.MemoryReservationExceeded((ulong)availableMemory, tag, kernelAllocation, bytes + reserve + alignment)) {
                return UIntPtr.Zero;
            }

            FreeNode * node = FreeNode.FindGoodFit(GetFreeList(), reserve, alignment);
            if (node == null) {
                node = FreeNode.FindGoodFit(GetFreeList(), bytes, alignment);
                if (node == null) {
                    node = FreeNode.FindGoodFit(GetSaveList(), reserve, alignment);
                    if (node == null) {
                        node = FreeNode.FindGoodFit(GetSaveList(), bytes, alignment);
                        if (node == null) {
                            // TODO: We should try to combine free and save pages...
                            // But for now, we just fail.
                            DebugStub.WriteLine("Failed to allocate on the heap!!! {0} bytes kernelalloc {1}\n",
                                                __arglist(bytes, kernelAllocation));
                            return UIntPtr.Zero;
                        }
                    }
                }
            }
            UIntPtr addr = (UIntPtr)node;
            UIntPtr adjust = SpaceNotAligned(addr + node->bytes, alignment);
            UIntPtr found = node->bytes;

#if VERBOSE
            Tracing.Log(Tracing.Debug, "    0. {0:x8}..{1:x8}: res={2:x}, adj={3:x}",
                        addr, addr + found, reserve, adjust);
#endif
            if (found > reserve + adjust) {
                // Put the extraneous pages in the free list.
                FreeNode.ReturnExtraBelow(GetFreeList(), ref addr, ref found, reserve + adjust);
#if VERBOSE
                Tracing.Log(Tracing.Debug, "    1. {0:x8}..{1:x8}",
                            addr, addr + found);
#endif
            }
#if ALLOW_BOOT_ARGLIST
            DebugStub.Assert
                (SpaceNotAligned(addr, alignment) == UIntPtr.Zero,
                 "FlatPages.RawAllocate not aligned addr={0} alignment={1}",
                 __arglist(addr, alignment));
#endif
            if (found > bytes) {
                // Put extra pages in the save list.
                FreeNode.ReturnExtraAbove(GetSaveList(), addr, ref found, bytes);
#if VERBOSE
                Tracing.Log(Tracing.Debug, "    2. {0:x8}..{1:x8}",
                            addr, addr + found);
#endif
            }
#if ALLOW_BOOT_ARGLIST
            DebugStub.Assert
                (found == bytes,
                 "FlatPages.RawAllocate wrong amount found={0} bytes={1}",
                 __arglist(found, bytes));
#endif
            SetRange(addr, found, tag);
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(971);
#endif
            //
            // The owner information is not reliable for determining kernel
            // or SIP allocation when the page type is stack, so the logic
            // is a little extra complicated here.
            //
            if ((tag & MemoryManager.TypeMask) == (uint)PageType.Stack) {

                // Stack pages use the kernelAllocation flag
                if (kernelAllocation) {
                    MemoryReservations.AllocationForStack((ulong)bytes);
                }
                else {
                    MemoryReservations.SIPAllocationForStack((ulong)bytes);
                }
            }
            else if ((tag & MemoryManager.ProcessPageMask) != MemoryManager.KernelPage) {

                    // process tag is reliable for non-stack allocations
                    MemoryReservations.SIPAllocationForHeap((ulong)bytes);
            }
            else {
                MemoryReservations.AllocationForHeap((ulong)bytes);
            }
            LogMemoryOperation(kernelAllocation, tag, addr, bytes);
            return addr;
        }

        private static unsafe UIntPtr RawAllocateBelow(UIntPtr limit,
                                                       UIntPtr bytes,
                                                       UIntPtr alignment,
                                                       uint tag)
        {
            VTable.Assert(Processor.InterruptsDisabled());
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(972);
#endif
            if (alignment < MemoryManager.PageSize) {
                alignment = MemoryManager.PageSize;
            }

#if VERBOSE
            Tracing.Log(Tracing.Debug,
                        "lim={0:x8}, size={1:x8}, align={2}, tag={3:x}",
                        limit, bytes, alignment, tag);
#endif
            // Check the allocation against memory reservations
            if (MemoryReservations.MemoryReservationExceeded((ulong)availableMemory, tag, false, bytes + alignment)) {
                return UIntPtr.Zero;
            }

            FreeNode * node = FreeNode.FindBelow(limit, GetFreeList(), bytes, alignment);
            if (node == null) {
                node = FreeNode.FindBelow(limit, GetSaveList(), bytes, alignment);
                if (node == null) {
                    // TODO: We should try to combine free and save pages...
                    // But for now, we just fail.
                    return UIntPtr.Zero;
                }
            }

            UIntPtr addr = (UIntPtr)node;
            UIntPtr adjust = SpaceToAlign(addr, alignment);
            UIntPtr found = node->bytes;

            if (adjust != UIntPtr.Zero) {
                // Put the alignment pages in free list.
                FreeNode.ReturnExtraBelow(GetFreeList(), ref addr, ref found, found - adjust);
            }
            DebugStub.Assert
                (SpaceNotAligned(addr, alignment) == UIntPtr.Zero,
                 "FlatPages.RawAllocateBelow not aligned addr={0} alignment={1}",
                 __arglist(addr, alignment));

            if (found > bytes) {
                // Put the extra pages in free list.
#if VERBOSE
                Tracing.Log(Tracing.Debug,
                            "found {0:x8}..{1:x8}, found={3:x8}, keep={4:x8}",
                            addr, addr + found, found, bytes);
#endif

                FreeNode.ReturnExtraAbove(GetFreeList(), addr, ref found, bytes);
            }

            DebugStub.Assert
                (found == bytes,
                 "FlatPages.RawAllocateBelow wrong amount found={0} bytes={1}",
                 __arglist(found, bytes));

            SetRange(addr, found, tag);
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(973);
#endif
            // Stacks are only allocated through RawAllocate()
            VTable.Assert((tag & MemoryManager.TypeMask) != (uint)PageType.Stack);

            if ((tag & MemoryManager.ProcessPageMask) != MemoryManager.KernelPage) {
                MemoryReservations.SIPAllocationForHeap((ulong)bytes);
            }
            else {
                MemoryReservations.AllocationForHeap((ulong)bytes);
            }

            LogMemoryOperation(false, tag, addr, bytes);

            return addr;
        }

        private static unsafe UIntPtr RawAllocateExtend(UIntPtr addr,
                                                        UIntPtr bytes,
                                                        uint tag)
        {
            VTable.Assert(Processor.InterruptsDisabled());
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(974);
#endif
            UIntPtr page = MemoryManager.PageFromAddr(addr);
            if (*(pageTable + page) != MemoryManager.PageFreeFirst) {
                Tracing.Log(Tracing.Error,
                            "{0:x} is not first free page {1:x}.",
                            addr, *(pageTable + page));

                return UIntPtr.Zero;
            }

            // Check the allocation against memory reservations
            if (MemoryReservations.MemoryReservationExceeded((ulong)availableMemory, tag, false, bytes)) {
                return UIntPtr.Zero;
            }

            FreeNode *node = (FreeNode *)addr;
            if (node->bytes < bytes) {
                Tracing.Log(Tracing.Error,
                            "Only {0:x} free bytes, not {1:x} as requested.",
                            node->bytes, bytes);
                return UIntPtr.Zero;
            }

#if VERBOSE
            Tracing.Log(Tracing.Debug, "addr={0:x8}, size={1:x8}, tag={2:x}",
                        addr, bytes, tag);
#endif

            // Remove the node from the list.
            FreeNode.Remove(node);

            UIntPtr found = node->bytes;

            if (found > bytes) {
                // Save the extra pages in the save list.
                FreeNode.ReturnExtraAbove(GetSaveList(), addr, ref found, bytes);
            }

            DebugStub.Assert
                (found == bytes,
                 "FlatPages.RawAllocateExtend wrong amount found={0} bytes{1}",
                 __arglist(found, bytes));

            SetRange(addr, found, tag);
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(975);
#endif
            // Stacks are only allocated through RawAllocate()
            VTable.Assert((tag & MemoryManager.TypeMask) != (uint)PageType.Stack);

            if ((tag & MemoryManager.ProcessPageMask) != MemoryManager.KernelPage) {
                MemoryReservations.SIPAllocationForHeap((ulong)bytes);
            }
            else {
                MemoryReservations.AllocationForHeap((ulong)bytes);
            }
            LogMemoryOperation(false, tag, addr, bytes);

            return addr;
        }

        [NoStackLinkCheckTrans]
        private static unsafe bool VerifyOwner(UIntPtr page, UIntPtr pages, uint tag)
        {
            tag &= MemoryManager.ProcessPageMask;
            for (UIntPtr i = UIntPtr.Zero; i < pages; i++) {
                if (((*(pageTable + page + i)) & MemoryManager.ProcessPageMask) != tag) {
                    DebugStub.WriteLine("FlatPages.VerifyOwner page={0} i={1} tag={2} address 0x{3,8:x}",
                                        __arglist(page, i, tag, ((pageTable+page))));
                    return false;
                }
#if false
                DebugStub.Assert
                    (((*(pageTable + page + i)) & MemoryManager.ProcessPageMask) == tag,
                     "FlatPages.VerifyOwner page={0} i={1} tag={2}",
                     __arglist(page, i, tag));
#endif
            }
            return true;
        }

        [NoStackLinkCheckTrans]
        private static unsafe void RawFree(UIntPtr addr, UIntPtr bytes, uint tag, bool stack, bool kernelAllocation)
        {
            VTable.Assert(Processor.InterruptsDisabled());
            UIntPtr bytesIn = bytes;
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(976);
#endif
#if VERBOSE
            Tracing.Log(Tracing.Debug, "adr={0:x}, size={1:x}, tag={2:x}",
                        addr, bytes, tag);
#endif

            bool result = VerifyOwner(MemoryManager.PageFromAddr(addr), MemoryManager.PagesFromBytes(bytes), tag);
            if(false == result) {
                DebugStub.WriteLine("VerifyOwner Failed for addr 0x{0,8:x} bytes {1} page {2} pages {3}\n",
                                    __arglist(addr, bytes, MemoryManager.PageFromAddr(addr), MemoryManager.PagesFromBytes(bytes)));
                DebugStub.Break();
            }

            FreeNode *node = FreeNode.GetNodeAt(addr + bytes);
            FreeNode *prev = FreeNode.GetNodeFromLast(addr - MemoryManager.PageSize);

            SetRange(addr, bytes, MemoryManager.PageFree);
            // Try to combine with the previous region if it isn't a save region.
            if (prev != null && prev->isSave == false) {
                addr = (UIntPtr)prev;
                bytes += prev->bytes;

                FreeNode.Remove(prev);
            }
            // Try to combine with the next region even if it was a save region.
            if (node != null) {
                bytes += node->bytes;
                FreeNode.Remove(node);
                if (node->isSave) {
                    // If next was save, then try to combine with the follower.
                    node = FreeNode.GetNodeAt(addr + bytes);
                    if (node != null) {
                        bytes += node->bytes;
                        FreeNode.Remove(node);
                    }
                }
            }
            // Create the free node.
            FreeNode.CreateAndInsert(GetFreeList(), addr, bytes);
#if NO__TRACE_PAGES
#else
            Kernel.Waypoint(977);
#endif
            // Stack allocations are ambiguous and must be called out separately
            if (stack) {
                if (kernelAllocation) {
                    MemoryReservations.FreeForStack((ulong)bytesIn);
                }
                else {
                    MemoryReservations.SIPFreeForStack((ulong)bytesIn);
                }
            }
            else if (tag != MemoryManager.KernelPage) {

                // Heap pages are reliable as per kernel/SIP
                MemoryReservations.SIPFreeForHeap((ulong)bytesIn);
            }
            else {
                MemoryReservations.FreeForHeap((ulong)bytesIn);
            }
            LogMemoryOperation(false, tag, addr, bytesIn);
        }

        private static unsafe PageType RawQuery(UIntPtr queryAddr,
                                                uint tag,
                                                out UIntPtr regionAddr,
                                                out UIntPtr regionSize)
        {
            VTable.Assert(Processor.InterruptsDisabled());
            UIntPtr page = MemoryManager.PageFromAddr(queryAddr);
            UIntPtr startPage = page;
            UIntPtr limitPage = page + 1;

            PageType type;
            uint val = *(pageTable + startPage);
            bool used = ((val & MemoryManager.ProcessPageMask) != MemoryManager.SystemPage);

            if ((val & MemoryManager.ProcessPageMask) == MemoryManager.SystemPage) {
                // Found a system page.
                type = (tag == 0) ? (PageType)(val & MemoryManager.TypeMask) : PageType.Unknown;

                // Find the start of the SystemPage region.
                for (; startPage > UIntPtr.Zero; startPage--) {
                    val = *(pageTable + startPage - 1);
                    if ((val & MemoryManager.ProcessPageMask) != MemoryManager.SystemPage) {
                        break;
                    }
                }
                // Find the end of the SystemPage region
                for (; limitPage < pageCount; limitPage++) {
                    val = *(pageTable + limitPage);
                    if ((val & MemoryManager.ProcessPageMask) != MemoryManager.SystemPage) {
                        break;
                    }
                }
            }
            else {
                // Found a process page.
                uint ptag = val & MemoryManager.ProcessPageMask;
                type = (tag == 0 || ptag == tag)
                    ? (PageType)(val & MemoryManager.TypeMask) : PageType.Unknown;

                if ((val & MemoryManager.TypeMask) == (uint)PageType.System) {
                    // Find the start of the process code region.
                    for (; startPage > UIntPtr.Zero; startPage--) {
                        val = *(pageTable + startPage - 1);
                        if ((val & MemoryManager.ProcessPageMask) != ptag ||
                            (val & MemoryManager.TypeMask) != (uint)PageType.System) {
                            break;
                        }
                    }
                    // Find the end of the process code region
                    for (; limitPage < pageCount; limitPage++) {
                        val = *(pageTable + limitPage);
                        if ((val & MemoryManager.ProcessPageMask) != ptag ||
                            (val & MemoryManager.TypeMask) != (uint)PageType.System) {
                            break;
                        }
                    }
                }
                else {
                    // Find the start of the process region.
                    for (; startPage > UIntPtr.Zero; startPage--) {
                        val = *(pageTable + startPage - 1);
                        if ((val & MemoryManager.ProcessPageMask) != ptag ||
                            (val & MemoryManager.TypeMask) == (uint)PageType.System) {
                            break;
                        }
                    }
                    // Find the end of the process region
                    for (; limitPage < pageCount; limitPage++) {
                        val = *(pageTable + limitPage);
                        if ((val & MemoryManager.ProcessPageMask) != ptag ||
                            (val & MemoryManager.TypeMask) == (uint)PageType.System) {
                            break;
                        }
                    }
                }
            }
#if VERBOSE
            Tracing.Log(Tracing.Debug, "[{0:x8}..{1:x8}]",
                        AddrFromPage(startPage), AddrFromPage(limitPage));
#endif
            regionAddr = AddrFromPage(startPage);
            regionSize = AddrFromPage(limitPage) - AddrFromPage(startPage);

            return type;
        }

        //////////////////////////////////////////////////////////////////////////
        //
        private static unsafe void DumpQuery(UIntPtr addr)
        {
            UIntPtr regionAddr;
            UIntPtr regionSize;
            PageType type = RawQuery(addr, 0, out regionAddr, out regionSize);

            Tracing.Log(Tracing.Debug, "  {0:x8} => {1:x8}..{2:x8} [{3:x}]",
                        addr, regionAddr, regionAddr + regionSize, (uint)type);
        }

        private static unsafe void DumpFreeNodes(FreeNode *list)
        {
            DumpFreeNodes(list, list->isSave);
        }

        private static unsafe void DumpFreeNodes(FreeNode *list, bool isSave)
        {
            if (isSave) {
                DebugStub.WriteLine(" SaveList:");
            }
            else {
                DebugStub.WriteLine(" FreeList:");
            }

            for (FreeNode *node = list->next; node != list; node = node->next) {
                string fmt = "  {0:x8}..{1:x8} prev={2:x8}, next={3:x8}, last={4:x8} ";
                if (node->isSave != isSave) {
                    if (node->isSave) {
                        fmt = "  {0:x8}..{1:x8} prev={2:x8}, next={3:x8}, last={4:x8} [Save!]";
                    }
                    else {
                        fmt = "  {0:x8}..{1:x8} prev={2:x8}, next={3:x8}, last={4:x8} [Free!]";
                    }
                }
                unchecked {
                    DebugStub.WriteLine( fmt,
                        __arglist(
                                (UIntPtr)node, (UIntPtr)node + node->bytes,
                                (UIntPtr)node->prev, (UIntPtr)node->next,
                                (UIntPtr)node->last));
                }
            }
        }

        internal static unsafe void Dump(string where)
        {
            DebugStub.WriteLine( "FlatPages.Dump: {0}", __arglist(where));

            uint *descriptors = pageTable;
            uint last = *descriptors++ & MemoryManager.SystemPageMask;
            UIntPtr begin = UIntPtr.Zero;

            UIntPtr freePages = UIntPtr.Zero;
            UIntPtr usedPages = UIntPtr.Zero;
            UIntPtr unknownPages = UIntPtr.Zero;
            UIntPtr sharedPages = UIntPtr.Zero;

            for (UIntPtr i = (UIntPtr)1; i < pageCount; i++) {
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
                        begin << MemoryManager.PageBits, pageCount << MemoryManager.PageBits, last,
                        (pageCount - begin) << MemoryManager.PageBits));

            DumpFreeNodes(GetFreeList(), false);
            DumpFreeNodes(GetSaveList(), true);

            DebugStub.WriteLine("Totals: free={0:x8}, used={1:x8}, unknown={2:x8}, reserved={3:x8}",
                        __arglist(
                        freePages << MemoryManager.PageBits,
                        usedPages << MemoryManager.PageBits,
                        unknownPages << MemoryManager.PageBits,
                        sharedPages << MemoryManager.PageBits));
        }

        //////////////////////////////////////////////////////////////////////
        //
        [NoStackLinkCheckTrans]
        [NoHeapAllocation]
        private static unsafe void SetPages(UIntPtr startPage, UIntPtr pageCount, uint tag)
        {
            uint * descriptor = pageTable + startPage;

#if VERY_VERBOSE
            Tracing.Log(Tracing.Audit,
                        "SetPages(beg={0:x},num={1:x},val={2:x}",
                        startPage << MemoryManager.PageBits,
                        pageCount << MemoryManager.PageBits,
                        tag);

#endif

            while (pageCount > UIntPtr.Zero) {
                *descriptor++ = tag;
                pageCount--;
            }
        }

        [NoStackLinkCheckTrans]
        [NoHeapAllocation]
        internal static void SetRange(UIntPtr start, UIntPtr bytes, uint tag)
        {
            if (start > upperLimit) {
                return;
            }
            if (start + bytes > upperLimit) {
                bytes = upperLimit - start;
            }
            SetPages(MemoryManager.PageFromAddr(start), MemoryManager.PagesFromBytes(bytes), tag);
        }
        //////////////////////////////////////////////////////////////////////////
        //

        public static UIntPtr GetMaxMemory()
        {
            return upperLimit;
        }

        [FlatPagesLock]
        public static unsafe UIntPtr GetFreeMemory()
        {
#if TEST_MEMORY_TRACKING
            UIntPtr retval = 0;
            bool iflag = Lock();

            try {
                uint *descriptors = pageTable;

                 // Count free pages
                 for (UIntPtr i = (UIntPtr)1; i < pageCount; i++) {
                     uint dsc = *descriptors++;
                     uint val = dsc & MemoryManager.SystemPageMask;

                     if (val == MemoryManager.PageFree) {
                         retval++;
                     }
                 }

                 //
                 // Make sure everything reports the same info
                 //
                 UIntPtr freeListSize = FreeNode.GetFreeListTotalSize(freeList);
                 UIntPtr saveListSize = FreeNode.GetFreeListTotalSize(saveList);
                 UIntPtr totalFreeList = freeListSize + saveListSize;

                 if (((retval * MemoryManager.PageSize) != totalFreeList) ||
                     (totalFreeList != availableMemory)) {

                     DebugStub.WriteLine("GetFreeMemory: Internal inconsistency");

                     DebugStub.WriteLine("Pages total 0x{0:x8}", __arglist(retval * MemoryManager.PageSize));

                     DebugStub.WriteLine("FreeList 0x{0:x8}, SaveList 0x{1:x8}, Total 0x{2:x8}",
                                          __arglist(
                                              (ulong)freeListSize, (ulong)saveListSize,
                                              ((ulong)freeListSize + (ulong)saveListSize)));

                     DebugStub.WriteLine("availableMemory: 0x{0:x8}\n", __arglist(availableMemory));

                     DebugStub.Break();
                 }
            }
            finally {
                Unlock(iflag);
            }

            return retval * MemoryManager.PageSize;
#else
            //
            // We track it in real time so it may be used by other components
            // at runtime.
            //
            return availableMemory;
#endif
        }

        public static unsafe UIntPtr GetUsedMemory()
        {
            uint *descriptors = pageTable;
            UIntPtr retval = 0;

            // Count non-free pages
            for (UIntPtr i = (UIntPtr)1; i < pageCount; i++) {
                uint dsc = *descriptors++;
                uint val = dsc & MemoryManager.SystemPageMask;

                if (val != MemoryManager.PageFree) {
                    retval++;
                }
            }

            return retval * MemoryManager.PageSize;
        }

        //
        //  Memory monitoring support
        //

        [Inline]
        private static void LogMemoryOperation(bool isKernelMemory, uint tag, UIntPtr address, UIntPtr size)
        {
            if (CurrentSystemLogger != null) {

                ushort memoryType = (ushort)(tag & MemoryManager.TypeMask);

                if (isKernelMemory && ((tag & MemoryManager.TypeMask) == (uint)PageType.Stack)) {

                    memoryType |= 0x8000;
                }

                CurrentSystemLogger.Log((ushort)((tag & MemoryManager.ProcessPageMask) >> 16),
                                        memoryType,
                                        address,
                                        size);
            }
        }

        public static void InitializeMemoryMonitoring()
        {
            CurrentSystemLogger = SystemAllocationLogger.Create("SystemMemoryLogger");
            DebugStub.Assert(CurrentSystemLogger != null);

            FreeMemoryCounters = FreeMemoryDistribution.Create("FreeMemoryCounters", HistogramSize);
            DebugStub.Assert(FreeMemoryCounters != null);

            InitializeMemoryCounters();
        }

        [FlatPagesLock]
        // moved into separate function to localize lock auditing
        private static void InitializeMemoryCounters()
        {
            bool iflag = Lock();
            try {

                for (int i = 0; i < HistogramSize; i++) {
                    FreeMemoryCounters.Buffer[i].BlockCount = 0;
                    FreeMemoryCounters.Buffer[i].TotalBucketSize = 0;
                }

                unsafe {
                    RegisterExitentFreeNodes(GetFreeList());
                    RegisterExitentFreeNodes(GetSaveList());
                }
            }
            finally {
                Unlock(iflag);
            }
        }

        internal static int HistogramSize;
        internal static int HistogramGranularityShift;
        private static FreeMemoryDistribution FreeMemoryCounters;
        private static SystemAllocationLogger CurrentSystemLogger;

        [Inline]
        internal static int GetBucketIndex(UIntPtr bytes)
        {
            UIntPtr bucket = bytes >> 20;

            if (bucket < (UIntPtr)HistogramSize) {

                return (int)bucket;
            }

            return (HistogramSize - 1);
        }


        [NoStackLinkCheckTrans]
        internal static void RegisterFreeNode(UIntPtr blockSize)
        {
            if (FreeMemoryCounters != null) {

                int i = GetBucketIndex(blockSize);

                FreeMemoryCounters.Buffer[i].BlockCount += 1;
                FreeMemoryCounters.Buffer[i].TotalBucketSize += blockSize;
            }
        }

        [NoStackLinkCheckTrans]
        internal static void DeRegisterFreeNode(UIntPtr blockSize)
        {
            if (FreeMemoryCounters != null) {

                int i = GetBucketIndex(blockSize);

                DebugStub.Assert((FreeMemoryCounters.Buffer[i].BlockCount > 0),
                                 "ASSERT: FreeMemoryCounters.BlockCount > 0");

                DebugStub.Assert((FreeMemoryCounters.Buffer[i].TotalBucketSize >= blockSize),
                                 "ASSERT: FreeMemoryCounters.TotalBucketSize > blockSize");

                FreeMemoryCounters.Buffer[i].BlockCount -= 1;
                FreeMemoryCounters.Buffer[i].TotalBucketSize -= blockSize;
            }
        }

        private static unsafe void RegisterExitentFreeNodes(FreeNode *list)
        {
            for (FreeNode *node = list->next; node != list; node = node->next) {

                RegisterFreeNode(node->bytes);
            }
        }


        //////////////////////////////////////////////////////////////////////
        //

        [Inline]
        internal static UIntPtr AddrFromPage(UIntPtr page)
        {
            return (page  << MemoryManager.PageBits);
        }

        [Inline]
        private static UIntPtr Align(UIntPtr data, UIntPtr size)
        {
            return ((data) & ~(size - 1));
        }

        [Inline]
        private static UIntPtr Pad(UIntPtr data, UIntPtr size)
        {
            return ((data + size - 1) & ~(size - 1));
        }

        [Inline]
        private static UIntPtr SpaceToAlign(UIntPtr data, UIntPtr size)
        {
            return Pad(data, size) - data;
        }

        [Inline]
        private static UIntPtr SpaceNotAligned(UIntPtr data, UIntPtr size)
        {
            return ((data) & (size - 1));
        }

        //////////////////////////////////////////////////////////////////////
        //
        [StructLayout(LayoutKind.Sequential)]
        private struct LastNode
        {
            internal const uint Signature   = 0xaa2222aa;
            internal const uint Removed     = 0xee1111ee;

            internal uint signature;
            internal unsafe FreeNode * node;

            [NoStackLinkCheckTrans]
            internal static unsafe LastNode * Create(UIntPtr addr, FreeNode *node)
            {
                LastNode *last = (LastNode *)addr;
                last->signature = LastNode.Signature;
                last->node = node;
                node->last = last;
#if VERBOSE
                Tracing.Log(Tracing.Debug, "addr={0:x8}, node={1:x8}",
                            addr, (UIntPtr) last->node);
#endif
                return last;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe void Remove(LastNode *last)
            {
                last->signature = Removed;
                last->node = null;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe void PrintLastNode(UIntPtr addr)
            {
                LastNode *last = (LastNode *)addr;
                DebugStub.WriteLine("ln.{1:x8}  ", __arglist((UIntPtr)last->node));
            }

        }


        //////////////////////////////////////////////////////////////////////
        //
        [StructLayout(LayoutKind.Sequential)]
        private struct FreeNode
        {
            internal const uint Signature   = 0x22aaaa22;
            internal const uint Removed     = 0x11eeee11;

            internal uint signature;
            internal unsafe FreeNode * prev;
            internal unsafe FreeNode * next;
            internal unsafe LastNode * last;
            internal UIntPtr bytes;
            internal bool isSave;

            [NoStackLinkCheckTrans]
            internal static unsafe void Init(FreeNode *list, bool isSave)
            {
                list->signature = Signature;
                list->prev = list;
                list->next = list;
                list->last = null;
                list->bytes = 0;
                list->isSave = isSave;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe bool Remove(FreeNode *node)
            {
                FreeNode * prev;
                FreeNode * next;

                availableMemory -= node->bytes;
                DeRegisterFreeNode(node->bytes);

                UIntPtr page = MemoryManager.PageFromAddr((UIntPtr)node);
                *(pageTable + page) = MemoryManager.PageFree;

                next = node->next;
                prev = node->prev;
                prev->next = next;
                next->prev = prev;

                if (node->last != null) {
                    LastNode.Remove(node->last);
                }
                node->signature = Removed;

                return (next == prev);
            }

            [NoStackLinkCheckTrans]
            private static unsafe void InsertAsPrev(FreeNode *list, FreeNode *node)
            {
                FreeNode * prev;

                prev = list->prev;
                node->next = list;
                node->prev = prev;
                prev->next = node;
                list->prev = node;
            }

            [NoStackLinkCheckTrans]
            private static unsafe void InsertAsNext(FreeNode *list, FreeNode *node)
            {
                FreeNode * next;

                next = list->next;
                node->prev = list;
                node->next = next;
                next->prev = node;
                list->next = node;
            }

            [NoStackLinkCheckTrans]
            private static unsafe void InsertBySize(FreeNode *list, FreeNode *node)
            {
#if ALLOW_BOOT_ARGLIST
                DebugStub.Assert(node->bytes > 0,
                                 "FlatPages.InsertBySize node->bytes={0}",
                                 __arglist(node->bytes));
#endif
                if (node->bytes <= SmallSize) {
                    // If the size is pretty small, we insert from the back of the list...
                    for (FreeNode *step = list->prev; step != list; step = step->prev) {
                        if (step->bytes >= node->bytes) {
                            InsertAsNext(step, node);
                            return;
                        }
                    }
                    InsertAsNext(list, node);
                }
                else {
                    // Insert a region into the list by size.
                    for (FreeNode *step = list; step->next != list; step = step->next) {
                        if (step->next->bytes <= node->bytes) {
                            InsertAsNext(step, node);
                            return;
                        }
                    }
                    InsertAsPrev(list, node);
                }
            }

            ///////////////////////////////////////////////////////////
            // FreeNode's new routines start here

            internal static unsafe void PrintFreeList(FreeNode *list)
            {
                int count = 0;
                DebugStub.WriteLine
                    ("        PRINT FREE LIST  (tail.{0:x8}  prev.{1:x8}  next.{2:x8})",
                     __arglist((UIntPtr)(list),
                               (UIntPtr)list->prev,
                               (UIntPtr)list->next));
                DebugStub.WriteLine("        ---------------------------------------------------");

                for (FreeNode *node = list->next;
                     node != list; node = node->next) {
                    DebugStub.Print
                        ("        [{0}] b.{1:x8} e.{2:x8} {3,8}KB p.{4:x8} n.{5:x8} l.{6:x8}  --  ",
                         __arglist(
                                   count,
                                   (UIntPtr)node, (UIntPtr)node + node->bytes,
                                   node->bytes/(1024),
                                   (UIntPtr)node->prev,
                                   (UIntPtr)node->next,
                                   (UIntPtr)node->last));
                    if (node->last != null) {
                        LastNode.PrintLastNode((UIntPtr)(node->last));
                    }
                    else {
                        DebugStub.WriteLine();
                    }
                    if (count++ > 20) {
                        DebugStub.WriteLine("\n        **** ERROR INFINITE LIST ****\n");
                        DebugStub.Break();
                    }
                }
            }

            internal static unsafe UIntPtr GetFreeListTotalSize(FreeNode *list)
            {
                UIntPtr size = 0;
                for (FreeNode *node = list->next;
                     node != list; node = node->next) {
                    size += node->bytes;
                }
                return size;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe FreeNode* GetFreeNodeAtBreakAddr(FreeNode *list, UIntPtr breakAddr)
            {
                int count = 0;

                for (FreeNode *node = list->next;
                     node != list; node = node->next) {

                    if ((UIntPtr)node <= breakAddr
                        && breakAddr < ((UIntPtr)node + node->bytes)) {
                        return node;
                    }
                    if (count++ > 20) {
                        DebugStub.WriteLine("  WARNING: Can't GetFreeNode ListTail.{0:x8} at {1:x8} after 20 iterations",
                                            __arglist((UIntPtr)list, breakAddr));
                        DebugStub.Break();
                    }

                }
                return null;
            }


            [NoStackLinkCheckTrans]
            internal static unsafe FreeNode * FindGoodFit(FreeNode *list,
                                                          UIntPtr bytes, UIntPtr alignment)
            {
#if ALLOW_BOOT_ARGLIST
                DebugStub.Assert(bytes > 0,
                                 "FlatPages.FindGoodFit bytes={0}",
                                 __arglist(bytes));
#endif
                // If it is a small allocation, we try to accelerate the search.
                if (bytes <= SmallSize && alignment <= MemoryManager.PageSize) {
                    for (FreeNode *node = list->prev; node != list; node = node->prev) {
                        if (node->bytes >= bytes) {
                            Remove(node);
                            return node;
                        }
                    }
                    return null;
                }
                else {
                    // First try to find a region closest in size to bytes...
                    FreeNode *best = null;
                    for (FreeNode *node = list->next; node != list; node = node->next) {
                        if (bytes <= node->bytes) {
                            UIntPtr full = SpaceToAlign((UIntPtr)node, alignment) + bytes;
                            if (full <= node->bytes) {
                                // If we find a candidate, remember it.
                                best = node;
                                if (full == node->bytes) {
                                    // Stop if it is the ideal region.
                                    break;
                                }
                            }
                        }
                        else {
                            // Stop if we have a candidate and we've reach smaller regions.
                            if (best != null) {
                                break;
                            }
                        }
                    }
                    if (best != null) {
                        Remove(best);
                    }
                    return best;
                }
            }

            [NoStackLinkCheckTrans]
            internal static unsafe FreeNode * FindBelow(UIntPtr limit, FreeNode *list,
                                                        UIntPtr bytes, UIntPtr alignment)
            {
                DebugStub.Assert(bytes > 0,
                                 "FlatPages.FindBelow bytes={0}",
                                 __arglist(bytes));

                // Try to find the first region below the limit address.
                for (FreeNode *node = list->next; node != list; node = node->next) {
                    if ((UIntPtr)node + bytes < limit && node->bytes >= bytes) {
                        UIntPtr full = SpaceToAlign((UIntPtr)node, alignment) + bytes;
                        if ((UIntPtr)node + full < limit && node->bytes >= full) {
                            Remove(node);
                            return node;
                        }
                    }
                }
                return null;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe FreeNode * GetNodeAt(UIntPtr addr)
            {
                UIntPtr page = MemoryManager.PageFromAddr(addr);

                if (*(pageTable + page) == MemoryManager.PageFreeFirst) {
                    return (FreeNode *)addr;
                }
                return null;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe FreeNode * GetNodeFromLast(UIntPtr addr)
            {
                UIntPtr page = MemoryManager.PageFromAddr(addr);

                if (*(pageTable + page) == MemoryManager.PageFree &&
                    *(pageTable + page + 1) != MemoryManager.PageFree) {

                    return ((LastNode *)addr)->node;
                }
                if (*(pageTable + page) == MemoryManager.PageFreeFirst) {
                    return (FreeNode *)addr;
                }
                return null;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe FreeNode * Create(UIntPtr addr, UIntPtr bytes, bool isSave)
            {
                // Mark a page as a node in the free list, initialize the node struct.
                FreeNode * node = (FreeNode *)addr;

#if VERY_VERBOSE
                Tracing.Log(Tracing.Debug,
                            isSave ?
                            "{0:x8}..{1:x8}, last={4:x8}" :
                            "{0:x8}..{1:x8}, last={4:x8}",
                            addr, addr+bytes, addr + bytes - MemoryManager.PageSize);
#endif

                UIntPtr page = MemoryManager.PageFromAddr(addr);
                *(pageTable + page) = MemoryManager.PageFreeFirst;

                node->signature = FreeNode.Signature;
                node->bytes = bytes;
                node->isSave = isSave;
                node->prev = null;
                node->next = null;
                node->last = null;

                if (bytes > MemoryManager.PageSize) {
                    LastNode.Create(addr + bytes - MemoryManager.PageSize, node);
                }
                return node;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe void CreateAndInsert(FreeNode *list,
                                                        UIntPtr addr,
                                                        UIntPtr bytes)
            {
                FreeNode * node = Create(addr, bytes, list->isSave);
                //
                // This memory is available on the freeList, or the
                // SaveList.
                //
                // Upper level memory lock protects access to this field.
                //
                availableMemory += bytes;
                RegisterFreeNode(bytes);
#if VERBOSE
                Tracing.Log(Tracing.Debug,
                            list->isSave ?
                            "({0:x8}, {1:x8}, true), prev={3:x8}, next={4:x8}, last={5:x8}" :
                            "({0:x8}, {1:x8}, false), prev={3:x8}, next={4:x8}, last={5:x8}",
                            addr, bytes, (UIntPtr) node->prev,
                            (UIntPtr) node->next, (UIntPtr) node->last);
#endif


#if ALLOW_BOOT_ARGLIST
                DebugStub.Assert((bytes & MemoryManager.PageMask) == 0,
                                 "FlatPages.CreateAndInsert bytes={0}",
                                 __arglist(bytes));
                DebugStub.Assert((node->bytes & MemoryManager.PageMask) == 0,
                                 "FlatPages.CreateAndInsert node->bytes={0}",
                                 __arglist(node->bytes));
#endif
                InsertBySize(list, node);
            }

            [NoStackLinkCheckTrans]
            internal static unsafe void ReturnExtraAbove(FreeNode *list,
                                                         UIntPtr addr,
                                                         ref UIntPtr found,
                                                         UIntPtr keep)
            {
                CreateAndInsert(list, addr + keep, found - keep);
                found = keep;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe void ReturnExtraBelow(FreeNode *list,
                                                         ref UIntPtr addr,
                                                         ref UIntPtr found,
                                                         UIntPtr keep)
            {
                CreateAndInsert(list, addr, found - keep);
                addr = addr + found - keep;
                found = keep;
            }
        }
    }
}
