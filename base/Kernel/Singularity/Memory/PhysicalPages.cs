////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PhysicalPages.cs - Primitive memory manager
//
//  Notes:
//
//  This module manages access to the machine's physical memory pages.
//  This serves as the substrate to paging, so this code cannot assume
//  that it can actually read and write the physical pages themselves,
//  as no mapping to them is likely to exist.
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.Singularity.Hal;

namespace Microsoft.Singularity.Memory
{
    [NoCCtor]
    [CLSCompliant(false)]
    public class PhysicalPages
    {
        /////////////////////////////////////
        // CONSTANTS
        /////////////////////////////////////

        // Never use physical memory below this limit
        internal const ulong LowerRAMBlackout = 0x200000; // 2MB

        /////////////////////////////////////
        // CONSTANTS
        /////////////////////////////////////
        private static SpinLock pagesLock;

        private static uint freeList; // index into the table or PageBlock.Sentinel
        private static unsafe PageBlock* physTable;
        private static uint numBlocks;
        private static ulong tableSize;

        // The physical max RAM address
        private static ulong addressLimit;

        /////////////////////////////////////
        // PUBLIC METHODS
        /////////////////////////////////////

        //
        // Initialize() must be called during OS boot *BEFORE* paging
        // is enabled, so that physical memory can be accessed
        // directly. We consult the system's memory map to pick a
        // range of memory where we can situate the physical page
        // table, and initialize it.
        //
        // the reserveSize argument specifies how much physical
        // memory to set aside and return a PhysicalAddress to.
        // This is used by the MemoryManager to reserve an area
        // of contiguous physical memory for use in I/O operations.
        //
        // After Initialize()ation, the PhysicalPages module
        // assumes that its page table will be identity-mapped
        // into the kernel's virtual memory space.
        //
        internal static unsafe PhysicalAddress Initialize(ulong reserveSize)
        {
            Platform p = Platform.ThePlatform;
            UIntPtr lowerAddress = UIntPtr.Zero;
            UIntPtr upperAddress = UIntPtr.Zero;

            // NB: our initialization is currently naive; we
            // set up a table to describe all of physical memory,
            // even though there are holes in it for reserved
            // memory that we will never be able to use.
            // This makes indexing much easier, though.

            InitializeLock();

            // Retrieve the highest RAM address
            MemoryManager.PhysicalMemoryLimits(out lowerAddress, out upperAddress);
            addressLimit = (ulong)upperAddress;

            DebugStub.WriteLine("Highest usable RAM address is 0x{0:x8}",
                                __arglist(addressLimit));

            // How much room do we need for the pageblock table?
            numBlocks = GetNumBlocks(addressLimit);
            ulong requiredSpace = (ulong)numBlocks * (ulong)sizeof(PageBlock);

            // Now we need to find a location in physical memory
            // where we can stick the physical pageblock table.
            ulong startAddr = LowerRAMBlackout;
            if (p.BootAllocatedMemorySize != 0) {
                if (startAddr > p.BootAllocatedMemory &&
                    startAddr < p.BootAllocatedMemory + p.BootAllocatedMemorySize) {
                    startAddr = (ulong)p.BootAllocatedMemory + (ulong)p.BootAllocatedMemorySize;
                }
            }

            ulong physLocation = FindFreeBlockInSMAP(startAddr, requiredSpace);

            if (physLocation == 0) {
                // Failed to find a spot to park the physical page
                // table. This is fatal!
                Kernel.Panic("Couldn't find enough room to initialize hardware page table");
            }

            // Initialize all the descriptor blocks as "free" (zeroed)
            physTable = (PageBlock*)physLocation;
            tableSize = requiredSpace;
            freeList = 0; // First descriptor

            for (uint i = 0; i < numBlocks; i++) {
                PageBlock* thisBlock = GetBlock(i);
                thisBlock->Initialize();
                thisBlock->prevIdx = (i == 0) ? PageBlock.Sentinel : i - 1;
                thisBlock->nextIdx = (i == numBlocks - 1) ? PageBlock.Sentinel : i + 1;
            }

            // Mark the blackout area of low physical memory as used
            MarkRangeUsed(0, startAddr - 1);

            // Now mark the range of physical pages occupied by the
            // hardware table itself as being used!
            MarkRangeUsed((ulong)physTable, requiredSpace);

            // Mark any non-Free areas (according to SMAP) as in use
            SMAPINFO* smap = p.Smap;
            for (uint i = 0; i < p.SmapCount; i++) {
                if ((smap[i].type != (ulong)SMAPINFO.AddressType.Free) &&
                    ((smap[i].addr + smap[i].size) > startAddr) &&
                    (smap[i].addr < addressLimit)) {

                    ulong unaccountedStart, unaccountedLength;

                    if (smap[i].addr >= startAddr) {
                        unaccountedStart = smap[i].addr;
                        unaccountedLength = smap[i].size;
                    }
                    else {
                        // Part of this memory window is already accounted for
                        unaccountedStart = startAddr;
                        unaccountedLength = smap[i].size - (startAddr - smap[i].addr);
                    }

                    MarkRangeUsed(unaccountedStart, unaccountedLength);
                }
            }

            // Mark out all the Platform special regions as busy
            if (p.MiniDumpLimit != 0) {
                ulong miniDumpSize = (ulong)p.MiniDumpLimit - (ulong)p.MiniDumpBase;
                MarkRangeUsed((ulong)p.MiniDumpBase,
                              MemoryManager.PagePad(miniDumpSize));
            }
            if (p.KernelDllSize != 0) {
                MarkRangeUsed((ulong)p.KernelDllBase,
                              MemoryManager.PagePad((ulong)p.KernelDllSize));
            }
            if (p.BootAllocatedMemorySize != 0) {
                MarkRangeUsed((ulong)p.BootAllocatedMemory,
                              MemoryManager.PagePad((ulong)p.BootAllocatedMemorySize));
            }

            // Last step: find an available area to situate the caller's
            // requested reserve-block, if any.
            PhysicalAddress reservedPtr = PhysicalAddress.Null;

            if (reserveSize != 0) {
                reservedPtr = new PhysicalAddress(
                    FindFreeBlockInSMAP(
                        MemoryManager.PagePad((ulong)physTable + tableSize),
                        reserveSize));

                if (reservedPtr == PhysicalAddress.Null) {
                    Kernel.Panic("Couldn't find enough physically contiguous memory to reserve");
                }

                if (reservedPtr.Value + reserveSize > 0xFFFFFF) {
                    Kernel.Panic("Couldn't find enough physically contiguous memory below 0xFFFFFF for I/O memory");
                }
            }

            // Mark the reserved block as used. It's up to the caller
            // to administer its use.
            MarkRangeUsed(reservedPtr.Value, reserveSize);

            CheckConsistency();

            DebugStub.WriteLine("PhysicalPages initialized at 0x{0:x8} - 0x{1:x8} with {2} physical pages available.",
                                __arglist(reservedPtr.Value,
                                          reservedPtr.Value + reserveSize,
                                          GetFreePageCount()));

            return reservedPtr;
        }

        // Allocate a single hardware page
        internal unsafe static PhysicalAddress AllocPage()
        {
            bool iflag = Lock();

            try {
                CheckConsistency();

                if (freeList != PageBlock.Sentinel) {
                    uint blockIdx = freeList;
                    DebugStub.Assert(GetBlock(blockIdx)->IsLinked(freeList));
                    uint freePage = GetBlock(blockIdx)->FirstFreePage();
                    MarkPageInBlockUsed(blockIdx, freePage);

                    ulong physPage =
                        ((ulong)blockIdx * (ulong)PageBlock.PagesPerBlock) + freePage;

                    ulong physAddr = (ulong)MemoryManager.PageSize * physPage;

                    return new PhysicalAddress(physAddr);
                }

                DebugStub.WriteLine("** Physical memory exhausted! **");
                return PhysicalAddress.Null;
            }
            finally {
                CheckConsistency();
                Unlock(iflag);
            }
        }

        // Free a single physical page
        internal unsafe static void FreePage(PhysicalAddress addr)
        {
            bool iflag = Lock();

            try {
                CheckConsistency();
                ulong pageNum = MemoryManager.PagesFromBytes(addr.Value);
                uint blockIdx = (uint)(pageNum / (ulong)PageBlock.PagesPerBlock);
                uint pageIdx = (uint)(pageNum % (ulong)PageBlock.PagesPerBlock);
                PageBlock* thisBlock = GetBlock(blockIdx);
                bool wasFull = thisBlock->Full;

                thisBlock->MarkAsFree(pageIdx);

                if (wasFull) {
                    // This block now has a page available; put it on the
                    // free list
                    DebugStub.Assert(!thisBlock->IsLinked(freeList));
                    thisBlock->Link(ref freeList);
                }
            }
            finally {
                CheckConsistency();
                Unlock(iflag);
            }
        }

        // Report how many pages are free
        internal unsafe static ulong GetFreePageCount()
        {
            bool iflag = Lock();

            try {
                return FreePageCountFromList();
            }
            finally {
                Unlock(iflag);
            }
        }

        public static ulong GetMaxMemory()
        {
            return addressLimit;
        }

        public static unsafe ulong GetFreeMemory()
        {
            return GetFreePageCount() * MemoryManager.PageSize;
        }

        public static unsafe ulong GetUsedMemory()
        {
            return GetMaxMemory() - GetFreeMemory();
        }

        /////////////////////////////////////
        // PRIVATE METHODS
        /////////////////////////////////////

        [Inline]
        private unsafe static PageBlock* GetBlock(uint blockIdx)
        {
            DebugStub.Assert(blockIdx < numBlocks);
            DebugStub.Assert(blockIdx != PageBlock.Sentinel);
            return &(physTable[blockIdx]);
        }

        // Get the number of descriptor blocks that are necessary for
        // a given amount of physical RAM
        private static uint GetNumBlocks(ulong physicalRAM)
        {
            ulong pages = MemoryManager.PagesFromBytes(physicalRAM);

            // Round up the number of blocks needed
            ulong blocks = pages / PageBlock.PagesPerBlock;

            if ((pages % PageBlock.PagesPerBlock) > 0) {
                blocks++;
            }

            return (uint)blocks;
        }

        private static unsafe void MarkPageInBlockUsed(uint blockIdx,
                                                       uint pageInBlock)
        {
            PageBlock* pBlock = GetBlock(blockIdx);
            pBlock->MarkAsUsed(pageInBlock);

            if (pBlock->Full) {
                pBlock->Unlink(ref freeList);
            }
        }

        // Mark a range of physical memory as being used. THIS IS ONLY
        // USED DURING INITIALIZATION, and so is not particularly
        // efficient.
        //
        // Addresses do not have to be page-aligned, but whole pages will
        // be marked.
        //
        // To allow SMAP overlaps with HAL regions make this ignore
        // region overlaps.
        private static unsafe void MarkRangeUsed(ulong startAddr, ulong length)
        {
            ulong firstPage = startAddr & ~MemoryManager.PageMask;
            // lastPage ends up being the address of the page immediately *after*
            // the data ends.
            ulong lastPage = MemoryManager.PagePad(startAddr + length);

            for (ulong pageAddr = firstPage; pageAddr < lastPage; pageAddr += MemoryManager.PageSize) {
                ulong pageNum = MemoryManager.PagesFromBytes(pageAddr);
                uint blockIdx = (uint)(pageNum / (ulong)PageBlock.PagesPerBlock);
                uint pageInBlock = (uint)(pageNum % (ulong)PageBlock.PagesPerBlock);
                PageBlock* pBlock = GetBlock(blockIdx);

                if (!pBlock->PageInUse(pageInBlock)) {
                    pBlock->MarkAsUsed(pageInBlock);

                    if (pBlock->Full) {
                        pBlock->Unlink(ref freeList);
                    }
                }
            }
        }

        private static unsafe ulong FindFreeBlockInSMAP(ulong startAddr, ulong requiredSpace)
        {
            SMAPINFO *smap = Platform.ThePlatform.Smap;

            for (uint i = 0; i < Platform.ThePlatform.SmapCount; i++) {
                if (smap[i].type == (ulong)SMAPINFO.AddressType.Free &&
                    smap[i].addr + smap[i].size > startAddr) {

                    ulong usableSize, usableStart;

                    if (smap[i].addr < startAddr) {
                        usableSize = smap[i].size - (startAddr - smap[i].addr);
                        usableStart = startAddr;
                    }
                    else {
                        usableSize = smap[i].size;
                        usableStart = smap[i].addr;
                    }

                    if (usableSize >= requiredSpace) {
                        return usableStart;
                    }
                }
            }

            return 0;
        }

        private unsafe static ulong FreePageCountFromList()
        {
            ulong retval = 0;
            uint freeIdx = freeList;

            while (freeIdx != PageBlock.Sentinel) {
                PageBlock* pBlock = GetBlock(freeIdx);
                DebugStub.Assert(!pBlock->Full);
                retval += pBlock->FreePages;
                freeIdx = pBlock->nextIdx;
            }

            return retval;
        }

        private unsafe static void CheckConsistency()
        {
#if SELF_TEST
            ulong pagesFromFreeList = FreePageCountFromList();
            ulong pagesFromWalk = 0;

            // Now walk the whole page table and count up
            // pages that way
            for (uint i = 0; i < numBlocks; i++) {
                PageBlock* pBlock = GetBlock(i);
                pagesFromWalk += pBlock->FreePages;
            }

            DebugStub.Assert(pagesFromWalk == pagesFromFreeList);
#endif
        }

        private static void InitializeLock()
        {
#if SINGULARITY_MP
            pagesLock = new SpinLock(SpinLock.Types.PhysicalPages);
#endif // SINGULARITY_MP
        }

        [NoStackLinkCheckTrans]
        private static bool Lock()
        {
            bool enabled = Processor.DisableInterrupts();
#if SINGULARITY_MP
            pagesLock.Acquire(Thread.CurrentThread);
#endif // SINGULARITY_MP
            return enabled;
        }

        [NoStackLinkCheckTrans]
        private static void Unlock(bool iflag)
        {
#if SINGULARITY_MP
            pagesLock.Release(Thread.CurrentThread);
#endif // SINGULARITY_MP
            Processor.RestoreInterrupts(iflag);
        }


        /////////////////////////////////////
        // HELPER STRUCTS
        /////////////////////////////////////

        // This is our descriptor for a range of physical
        // pages. Each PageBlock describes a range of
        // physical pages with a used/not-used bitmap.
        [System.Runtime.InteropServices.StructLayout(LayoutKind.Sequential)]
        private struct PageBlock
        {
            // CONSTS

            // "null" value for indexes
            internal const uint Sentinel = uint.MaxValue;
            private const uint RegionsPerBlock = 29;
            internal const uint PagesPerBlock = RegionsPerBlock * 32;
            private const uint FullRegion = uint.MaxValue;
            private const uint BlockMapMask = 0x1FFFFFFF; // 29 bits
            private const uint FullMap = BlockMapMask;
            private const uint UnusedMask = 0xE0000000;

            // ------------------------------ struct fields
            internal unsafe uint prevIdx; // 4 bytes
            internal unsafe uint nextIdx; // +4 bytes = 8bytes

            // The PageBlock has a mini-tree structure:
            // this first word is a bitmap indicating
            // the availability of 29 subregions.

            // The bit for a subregion is SET if it is
            // *completely full*, and CLEAR otherwise.
            // The top 3 bits are kept SET.
            internal uint blockMap;       // +4 bytes = 12 bytes

            // Each region has 4 bytes, making PageBlock
            // 128 bytes in size all together. Each region
            // describes 32 pages, one per bit. Each bit
            // is SET if the page is in use, and CLEAR
            // if it is free.

            // Due to C# madness, here are some dummy
            // variables to block out the space.
            uint  i1;                    // +4 bytes = 16bytes
            ulong l1, l2, l3, l4, l5,
                  l6, l7, l8, l9, l10,
                  l11, l12, l13, l14;    // +112 bytes = 128bytes

            // ------------------------------

            internal void Initialize()
            {
                prevIdx = nextIdx = Sentinel;
                blockMap = 0;
                l1 = l2 = l3 = l4 = l5 =
                    l6 = l7 = l8 = l9 = l10 =
                    l11 = l12 = l13 = l14 = 0;
                i1 = 0;
                CheckConsistency();
            }

            internal unsafe void Unlink(ref uint listHead)
            {
                DebugStub.Assert(IsLinked(listHead));

                if (prevIdx != Sentinel) {
                    DebugStub.Assert(GetBlock(prevIdx)->nextIdx == Index, "PhysicalPages.PageBlock.Unlink: inconsistent prev->next");
                    GetBlock(prevIdx)->nextIdx = nextIdx;
                }
                else {
                    // We are the list head.
                    DebugStub.Assert(listHead == Index, "PhysicalPages.PageBlock.Unlink: inconsistent head");
                    listHead = nextIdx;
                }

                if (nextIdx != Sentinel) {
                    DebugStub.Assert(GetBlock(nextIdx)->prevIdx == Index, "PhysicalPages.PageBlock.Unlink: inconsistent next->prev");
                    GetBlock(nextIdx)->prevIdx = prevIdx;
                }

                nextIdx = Sentinel;
                prevIdx = Sentinel;
            }

            internal unsafe void Link(ref uint listHead)
            {
                DebugStub.Assert(!IsLinked(listHead));

                if (listHead != Sentinel) {
                    DebugStub.Assert(GetBlock(listHead)->prevIdx == Sentinel, "PhysicalPages.PageBlock.Link: Inconsistent head-entry prev link");
                    GetBlock(listHead)->prevIdx = Index;
                }

                nextIdx = listHead;
                listHead = Index;
                prevIdx = Sentinel;
            }

            internal unsafe bool PageInUse(uint pageIdx)
            {
                CheckConsistency();
                DebugStub.Assert(pageIdx < PagesPerBlock, "PhysicalPages.PageBlock.PageInUse: Bad page index");

                fixed ( uint* pBeforeRegions = &blockMap ) {
                    uint* pRegions = pBeforeRegions; // Point just before regions
                    pRegions++; // Advance to the first region word
                    uint regionIdx = pageIdx / 32;
                    uint bitIdx = pageIdx % 32;
                    return ((pRegions[regionIdx] & (1 << (int)bitIdx)) != 0);
                }
            }

            [Inline]
            internal unsafe bool RegionFull(uint regionIdx)
            {
                DebugStub.Assert(regionIdx < RegionsPerBlock, "PhysicalPages.PageBlock.RegionFull: Bad region index");
                return ((blockMap & (1 << (int)regionIdx)) != 0);
            }

            // pageIdx specifies a page within this block
            // (zero is the first, PagesPerBlock-1 is the last)
            internal unsafe void MarkAsUsed(uint pageIdx)
            {
                CheckConsistency();

                fixed( uint *pBeforeRegions = &blockMap ) {
                    uint* pRegions = pBeforeRegions; // Point just before regions
                    pRegions++; // Advance to the first region word
                    uint regionIdx = pageIdx / 32;
                    uint bitIdx = pageIdx % 32;

                    DebugStub.Assert(pageIdx < PagesPerBlock, "PhysicalPages.PageBlock.MarkAsUsed: Bad page index");
                    DebugStub.Assert(!PageInUse(pageIdx), "PhysicalPages.PageBlock.MarkAsUsed: Page already in use");
                    DebugStub.Assert(!RegionFull(regionIdx), "PhysicalPages.PageBlock.MarkAsUsed: Region already full");

                    // Mark the page used in its subregion
                    pRegions[regionIdx] |= ((uint)1 << (int)bitIdx);

                    // If our whole subregion is full, mark the blockMap
                    if (pRegions[regionIdx] == FullRegion) {
                        blockMap |= ((uint)1 << (int)regionIdx);
                    }
                }

                CheckConsistency();
            }

            internal unsafe void MarkAsFree(uint pageIdx)
            {
                CheckConsistency();

                fixed( uint *pBeforeRegions = &blockMap ) {
                    uint* pRegions = pBeforeRegions; // Point just before regions
                    pRegions++; // Advance to the first region word
                    uint regionIdx = pageIdx / 32;
                    uint bitIdx = pageIdx % 32;
                    DebugStub.Assert(pageIdx < PagesPerBlock, "PhysicalPages.PageBlock.MarkAsFree: Bad page index");
                    DebugStub.Assert(PageInUse(pageIdx), "PhysicalPages.PageBlock.MarkAsFree: Page already free");

                    // Mark the page free in its subregion
                    pRegions[regionIdx] &= ~((uint)1 << (int)bitIdx);

                    // Mark our subregion as being usable
                    blockMap &= ~((uint)1 << (int)regionIdx);
                }

                CheckConsistency();
            }

            // Illegal to call this on a full block.
            internal unsafe uint FirstFreePage()
            {
                DebugStub.Assert(!Full, "PhysicalPages.PageBlock.FirstFreePage: Block already full");

                // Look for a clear bit in the region map
                for (int i = 0; i < RegionsPerBlock; i++) {
                    if ((blockMap & (uint)((uint)1 << i)) == 0) {
                        // This region is available. Look
                        // for a free page in the specific
                        // region.
                        fixed (uint* pBeforeRegions = &blockMap) {
                            uint* pRegion = pBeforeRegions + i + 1;
                            for (int j = 0; j < 32; j++) {
                                if ((*pRegion & ((uint)1 << j)) == 0) {
                                    // This page is free.
                                    return ((uint)i * 32) + (uint)j;
                                }
                            }
                        }
                    }
                }

                // If we're not full, we should never get here.
                Kernel.Panic("Inconsistency in PhysicalPages.PageBlock.FirstFreePage()");
                return 0;
            }

            internal bool Full {
                [Inline]
                get {
                    CheckConsistency();
                    return (blockMap & BlockMapMask) == FullMap;
                }
            }


            internal bool Empty {
                [Inline]
                 get {
                    CheckConsistency();
                    return (blockMap & BlockMapMask) == 0;
                }
            }

            // Illegal to call this on a full block.
            internal unsafe uint FreePages {
                get {
                    CheckConsistency();

                    uint retval = 0;

                    for (int i = 0; i < RegionsPerBlock; i++) {
                        if ((blockMap & (uint)((uint)1 << i)) == 0) {
                            // This region has free pages.
                            fixed (uint* pBeforeRegions = &blockMap) {
                                uint* pRegion = pBeforeRegions + i + 1;
                                for (int j = 0; j < 32; j++) {
                                    if ((*pRegion & ((uint)1 << j)) == 0) {
                                        // This page is free.
                                        retval++;
                                    }
                                }
                            }
                        }
                    }

                    return retval;
                }
            }

            internal bool IsLinked(uint listHead) {
                CheckConsistency();

                if (prevIdx == Sentinel) {
                    // We are the head of *some* list
                    return listHead == Index;
                }

                if ((prevIdx != Sentinel) || (nextIdx != Sentinel)) {
                    // We are linked into *some* list. We only
                    // have the freeList at the moment, so for now
                    // skip the expensive process of walking the list
                    // to confirm we're in the right one
                    return true;
                }

                return false;
            }

            internal unsafe uint Index {
                [Inline]
                get {
                    fixed( PageBlock* pThis = &this ) {
                        DebugStub.Assert(pThis >= physTable, "PhysicalPages.PageBlock.Index: this < physTable");
                        DebugStub.Assert((ulong)pThis < (ulong)physTable + (ulong)tableSize, "PhysicalPages.PageBlock.Index: this > table bounds");
                        return (uint)(pThis - physTable);
                    }
                }
            }

            private unsafe void CheckConsistency()
            {
#if SELF_TEST
                // Top bits should be kept clear
                DebugStub.Assert((blockMap & UnusedMask) == 0);

                fixed ( uint* pBeforeRegions = &blockMap ) {
                    uint* pRegion = pBeforeRegions;
                    pRegion++;

                    for (uint i = 0; i < RegionsPerBlock; i++, pRegion++) {
                        if ((*pRegion) != FullRegion) {
                            DebugStub.Assert((blockMap & ((uint)1 << (int)i)) == 0, "PhysicalPages.PageBlock.CheckConsistency: blockMap shows a free region as full");
                        }
                        else {
                            DebugStub.Assert((blockMap & ((uint)1 << (int)i)) != 0, "PhysicalPages.PageBlock.CheckConsistency: blockMap shows a full region as free");
                        }
                    }
                }
#endif
            }
        }
    }
}

