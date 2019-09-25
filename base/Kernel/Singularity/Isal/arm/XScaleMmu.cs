///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note: A very random bag of memory related functionality.
//
//  Caveat emptor:
//   - In TLB management the assumption is UNIPROC.
//   - TLB management assumes 1:1 page translation.
//   - TLB managment only invalidates DTLB entries.

namespace Microsoft.Singularity.Isal.Arm.XScale
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    using Singularity.Io;

#if !SINGULARITY_KERNEL
#error "Compiling bad stuff into user space."
#endif // SINGULARITY_KERNEL

    [CLSCompliant(false)]
    [AccessedByRuntime("referenced in asm")]
    public sealed class Mmu
    {
        static UIntPtr ttb;

        static IoMemory l2TablePool; // Pool used for finite number of L2 pages
        static uint []  l2UsedBitmap;

        const uint CacheLineSize  = 32;
        const uint L2CacheSize    = 512 * 1024;
        const uint L1ICacheSize   = 32 * 1024;
        const uint L1DCacheSize   = 32 * 1024;

        const uint L2TableEntries = 256;
        const uint L2EntrySize    = 4;
        const uint L2TableSize    = L2TableEntries * L2EntrySize;
        static readonly uint MaxL2Tables;

        const uint L1SectionSize  = 0x100000;
        const uint L2SectionSize  = 0x1000;
        const int  L1SectionShift = 20;
        const int  L2SectionShift = 12;

        static Mmu()
        {
            ttb = GetTTB();

            // NB Table is 1MB section and 1MB aligned to avoid modifying page table entries on
            // page containing pool of

            l2TablePool  = IoMemory.AllocatePhysical(L1SectionSize, L1SectionSize);
            DebugStub.Assert(RangeIsPageAligned(l2TablePool.VirtualAddress,
                                                (uint)l2TablePool.Length,
                                                L1SectionSize));

            MaxL2Tables = L1SectionSize / L2TableSize;

            l2UsedBitmap = new uint [MaxL2Tables / 32];
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Page table management
        //

        [NoHeapAllocation]
        static private bool RangeIsPageAligned(UIntPtr start, UIntPtr length, UIntPtr pageSize)
        {
            return ((start & pageSize - 1) == 0) && ((length & pageSize - 1) == 0);
        }

        [NoHeapAllocation]
        private unsafe static UIntPtr AllocateL2Table()
        {
            for (int i = 0; i < l2UsedBitmap.Length; i++) {
                if (l2UsedBitmap[i] == 0xff) {
                    continue;
                }
                for (int j = 0; j < 32; j++) {
                    uint bit = 1u << j;
                    if ((l2UsedBitmap[i] & bit) == 0) {
                        l2UsedBitmap[i] |= bit;
                        int index = i * 32 + j;
                        return l2TablePool.VirtualAddress + (uint)(index * L2TableSize);
                    }
                }
            }
            return UIntPtr.Zero;
        }

        [NoHeapAllocation]
        private unsafe static void FreeL2Table(UIntPtr tableAddress)
        {
            DebugStub.Assert(
                tableAddress >= l2TablePool.VirtualAddress &&
                tableAddress <= (l2TablePool.VirtualAddress + MaxL2Tables * L2TableSize));
            int tableIndex = (int)((tableAddress - l2TablePool.VirtualAddress) / L2TableSize);
            uint mask = ~(1u << (tableIndex & 31));
            l2UsedBitmap[tableIndex / 32] &= mask;
        }

        [NoHeapAllocation]
        [Inline]
        private static bool IsSectionType(uint l1Entry)
        {
            return ((l1Entry & L1.TypeMask) == L1.SectionType) &&
                ((l1Entry & L1.SupersectionTypeMask) != L1.SupersectionType);
        }

        [NoHeapAllocation]
        private unsafe static void ConvertL1EntryToL2Table(uint l1EntryIndex)
        {
            DebugStub.Assert(Processor.InterruptsDisabled());
            uint* l1EntryPtr = ((uint*)ttb) + l1EntryIndex;
            uint l1Entry = *l1EntryPtr;

            // Convert page attributes from L1Entry to L2Entry

            DebugStub.Assert(IsSectionType(l1Entry));
            uint tex = (l1Entry & L1.TexMask) >> L1.TexRoll;
            uint ap  = (l1Entry & L1.ApMask) >> L1.ApRoll;
            uint cb  = l1Entry & (L1.CBit | L1.BBit);

            uint l2Bits = (L2Coarse.ExtendedSmallPageType |
                           cb | (ap << L2Coarse.Ap0Roll) |
                           (tex << L2Coarse.ExtendedSmallPageTexRoll));

            // Fill L2 Page Table

            uint addr    = l1Entry & L1.SectionAddressMask;

            UIntPtr l2Table = AllocateL2Table();
            DebugStub.Assert(((uint)l2Table & (L2TableSize - 1)) == 0);

            uint* l2EntryPtr = (uint*)l2Table;
            for (uint i = 0; i < L2TableEntries; i++) {
                *l2EntryPtr = addr | l2Bits;
                addr += 4096;
                l2EntryPtr++;
            }

            // Convert L1 section entry to L1 coarse page entry
            // and update.
            l1Entry &= (L1.DomainMask | L1.PBit);
            l1Entry |= L1.CoarsePageTableType;
            l1Entry |= (uint)l2Table;

            InvalidateDTlbEntry(*l1EntryPtr & L1.SectionAddressMask);
            *l1EntryPtr = l1Entry;

            CleanInvalidateDCacheLine((UIntPtr) l1EntryPtr);
            CleanInvalidateDCacheLines(l2Table, L2TableSize);
        }

        [NoHeapAllocation]
        private unsafe static void MakeRangeL1Entries(UIntPtr start, UIntPtr length)
        {
            DebugStub.Assert(RangeIsPageAligned(start, length, L1SectionSize));

            for (UIntPtr limit = start + length; start != limit; start += L1SectionSize) {
                uint* entryPtr = ((uint*)ttb) + (start >> L1SectionShift);
                uint type = *entryPtr & L1.TypeMask;
                if (type == L1.CoarsePageTableType) {
                    uint* l2Start = (uint*)(*entryPtr & L1.CoarsePageTableAddressMask);
                    uint  l2Entry = *l2Start;
                    for (int i = 0; i < L2TableEntries; i++) {
                        // Invalidate translations for entries in L2 table
                        InvalidateDTlbEntry(l2Start[i] & L2Coarse.ExtendedSmallPageAddressMask);
                    }

                    FreeL2Table((UIntPtr)l2Start);
                    CleanInvalidateDCacheLines((UIntPtr)l2Start, L2TableSize);

                    // Change entry from L2 Table pointer to L1 Section Entry
                    uint l1Entry = *entryPtr;

                    l1Entry &= (L1.DomainMask | L1.PBit);
                    l1Entry |= (l2Entry & (L2Coarse.ExtendedSmallPageTexMask | L2Coarse.Ap0Mask)) << (L1.ApRoll - L2Coarse.Ap0Roll);
                    l1Entry |= l2Entry & (L2Coarse.CBit | L2Coarse.BBit);
                    l1Entry |= L1.SectionType;
                    l1Entry |= start & L1.SectionAddressMask;

                    *entryPtr = l1Entry;
                    InvalidateDTlbEntry(start);
                }
                else {
                    DebugStub.Assert(IsSectionType(*entryPtr));
                }
            }
        }

        [NoHeapAllocation]
        private unsafe static void MakeRangeL2Entries(UIntPtr start, UIntPtr length)
        {
            DebugStub.Assert(RangeIsPageAligned(start, length, L2SectionSize));

            UIntPtr limit = (start + length + L1SectionSize - 1) & ~(L1SectionSize - 1);
            for (start = start & ~(L1SectionSize - 1); start != limit; start += L1SectionSize) {
                uint* entryPtr = ((uint*)ttb) + (start >> L1SectionShift);
                uint oldEntry = *entryPtr;
                uint type = *entryPtr & L1.TypeMask;
                if (type == L1.SectionType) {
                    ConvertL1EntryToL2Table((uint)start >> L1SectionShift);

                    uint addr = oldEntry & L1.SectionAddressMask;
                    InvalidateDTlbEntry((UIntPtr)addr);
                }
                else {
                    DebugStub.Assert(type == L1.CoarsePageTableType);
                }
            }
        }

        [NoHeapAllocation]
        private unsafe static void SetL2Attributes(UIntPtr start,
                                                   UIntPtr length,
                                                   bool cacheable,
                                                   bool bufferable)
        {
            DebugStub.Assert(RangeIsPageAligned(start, length, L2SectionSize));
            DebugStub.Assert((start & (L2SectionSize - 1)) + length <= L1SectionSize);

            uint* l1EntryPtr = ((uint*)ttb) + (start >> L1SectionShift);
            uint l1Entry = *l1EntryPtr;
            DebugStub.Assert((l1Entry & L1.TypeMask) == L1.CoarsePageTableType);

            uint cb = 0;
            if (cacheable) {
                cb |= L2Coarse.CBit;
            }
            if (bufferable) {
                cb |= L2Coarse.BBit;
            }
            const uint cbMask = ~(L2Coarse.CBit | L2Coarse.BBit);

            uint* l2StartPtr = (uint*)(l1Entry & L1.CoarsePageTableAddressMask);
            l2StartPtr += (start & L1SectionSize - 1) >> L2SectionShift;

            uint done = 0;

            uint* l2EndPtr = l2StartPtr + (length >> L2SectionShift);
            for (uint* l2Ptr = l2StartPtr; l2Ptr != l2EndPtr; l2Ptr++) {
                *l2Ptr = (*l2Ptr & cbMask) | cb;

                uint addr = *l2Ptr & L2Coarse.ExtendedSmallPageAddressMask;
                InvalidateDTlbEntry((UIntPtr)addr);
                CleanInvalidateDCacheLine(new UIntPtr(l2Ptr));

                DebugStub.Assert(addr != 0);
                done++;
            }
        }

        [NoHeapAllocation]
        private unsafe static void SetL1Attributes(UIntPtr  start,
                                                   UIntPtr  length,
                                                   bool     cacheable,
                                                   bool     bufferable)
        {
            DebugStub.Assert(RangeIsPageAligned(start, length, L1SectionSize));

            uint cbBits = 0;
            if (cacheable) {
                cbBits |= L1.CBit;
            }
            if (bufferable) {
                cbBits |= L1.BBit;
            }

            uint l1EntryOffset = ((uint)start) / L1SectionSize;

            uint* l1EntryStart = ((uint*)(ttb)) + l1EntryOffset;
            uint* l1EntryEnd   = l1EntryStart + ((length + L1SectionSize - 1) >> L1SectionShift);

            for (uint* l1Entry = l1EntryStart; l1Entry != l1EntryEnd; l1Entry++) {

                DebugStub.Assert(IsSectionType(*l1Entry));
                DebugStub.Assert((*l1Entry & L1.SectionSbz) == 0);

                *l1Entry &= ~(L1.CBit|L1.BBit);
                *l1Entry |= cbBits;

                uint addr = *l1Entry & L1.SectionAddressMask;
                InvalidateDTlbEntry((UIntPtr)addr);
                CleanInvalidateDCacheLine(new UIntPtr(l1Entry));
            }
        }

        [NoHeapAllocation]
        public unsafe static void SetCacheAttributes(UIntPtr startVA, UIntPtr length, bool cacheable, bool bufferable)
        {
            if (length == 0) {
                return;
            }

            DebugStub.Assert(
                RangeIsPageAligned(startVA, length, L1SectionSize) ||
                RangeIsPageAligned(startVA, length, L2SectionSize)
                );

            bool en = Processor.DisableInterrupts();
            try {
                UIntPtr todo = length;

                if (RangeIsPageAligned(startVA, todo, L1SectionSize)) {
                    MakeRangeL1Entries(startVA, todo);
                    SetL1Attributes(startVA, todo, cacheable, bufferable);
                }
                else if (RangeIsPageAligned(startVA, todo, L2SectionSize)) {
                    UIntPtr l1Boundary = (startVA + L1SectionSize - 1) & ~(L1SectionSize - 1);
                    if (startVA != l1Boundary) {
                        UIntPtr unaligned = l1Boundary - startVA;
                        if (unaligned > todo) {
                            unaligned = todo;
                        }
                        MakeRangeL2Entries(startVA, unaligned);
                        SetL2Attributes(startVA, unaligned, cacheable, bufferable);
                        todo -= unaligned;
                    }

                    if (todo > L1SectionSize) {
                        UIntPtr l1Todo = todo & ~(L1SectionSize - 1);
                        MakeRangeL1Entries(l1Boundary, l1Todo);
                        SetL1Attributes(l1Boundary, l1Todo,
                                        cacheable, bufferable);
                        l1Boundary += l1Todo;
                        todo -= l1Todo;
                    }

                    if (todo > 0) {
                        MakeRangeL2Entries(l1Boundary, todo);
                        SetL2Attributes(l1Boundary, todo,
                                        cacheable, bufferable);
                    }
                }
                else {
                    DebugStub.Break();
                }
            }
            finally {
                if (cacheable == false || bufferable == false) {
                    DebugStub.Assert(length != 0);
                    CleanInvalidateDCacheLines(startVA, length);
                }
                Processor.RestoreInterrupts(en);
            }
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Cache management
        //

        [NoHeapAllocation]
        public static void CleanInvalidateDCacheLines(UIntPtr start, UIntPtr length)
        {
            Tracing.Log(Tracing.Debug, "CleanInvalidateDCacheLines({0:x8}..{1:x8})",
                        start, start + length);

            DebugStub.Assert(length < new UIntPtr(256 * 1024 * 1024));

            if (length == 0) {
                return;
            }

            DebugStub.Assert(length < new UIntPtr(256 * 1024 * 1024));

            bool en = Processor.DisableInterrupts();
            FlushPrefetch();
            MemoryFence();
            try {
                if (length >= L1DCacheSize) {
                    CleanInvalidateL1DCache();
                }
                else {
                    CleanInvalidateL1DCacheLines((uint)start, (uint)length);
                }

                if (length >= L2CacheSize) {
                    CleanInvalidateL2Cache();
                }
                else {
                    CleanInvalidateL2CacheLines((uint)start, (uint)length);
                }
            }
            finally {
                FlushPrefetch();
                MemoryFence();
                Processor.RestoreInterrupts(en);
            }
        }

        [NoHeapAllocation]
        public static void CleanDCacheLines(UIntPtr start, UIntPtr length)
        {
            if (length == 0) {
                return;
            }

            bool en = Processor.DisableInterrupts();
            FlushPrefetch();
            MemoryFence();
            try {
                if (length >= L1DCacheSize) {
                    CleanL1DCache();
                }
                else {
                    CleanL1DCacheLines((uint)start, (uint)length);
                }

                if (length >= L2CacheSize) {
                    CleanL2Cache();
                }
                else {
                    CleanL2CacheLines((uint)start, (uint)length);
                }
            }
            finally {
                FlushPrefetch();
                MemoryFence();
                Processor.RestoreInterrupts(en);
            }
        }

#if false
        [NoHeapAllocation]
        public static void InvalidateICacheLines(UIntPtr start, UIntPtr length)
        {
            Tracing.Log(Tracing.Debug, "InvalidateICacheLines({0:x8}..{1:x8})",
                        start, start + length);

            UIntPtr end = start + length;

            bool en = Processor.DisableInterrupts();
            FlushPrefetch();
            MemoryFence();
            try {
                if ((start & (CacheLineSize - 1)) != 0) {
                    start = start & ~(CacheLineSize - 1);
                    CleanInvalidateICacheLine((uint)start);
                    start += CacheLineSize;
                }
                if (start < end && (end & (CacheLineSize - 1)) != 0) {
                    end = end & ~(CacheLineSize - 1);
                    CleanInvalidateICacheLine((uint)end);
                }

                if (start < end) {
                    UIntPtr alength = end - start;

                    if (alength >= L1ICacheSize) {
                        InvalidateL1ICache();
                    }
                    else {
                        InvalidateL1ICacheLines((uint)start, (uint)alength);
                    }

                    InvalidateL2CacheLines((uint)start, (uint)alength);
                }
            }
            finally {
                FlushPrefetch();
                MemoryFence();
                Processor.RestoreInterrupts(en);
            }
        }
#endif

        [NoHeapAllocation]
        public static void InvalidateDCacheLines(UIntPtr start,
                                                 UIntPtr length)
        {
            if (length == 0) {
                return;
            }

            DebugStub.Assert(length < new UIntPtr(256 * 1024 * 1024));

            bool en = Processor.DisableInterrupts();
            FlushPrefetch();
            MemoryFence();
            try {
                if ((start & (CacheLineSize - 1)) != 0) {
                    // Start is not aligned, line may other data on it.
                    CleanInvalidateDCacheLine(start);
                }

                if (((start + length) & (CacheLineSize - 1)) != 0) {
                    // End is not aligned, line may other data on it.
                    CleanInvalidateDCacheLine((start + length) & ~(CacheLineSize - 1));
                }

                // NB Invalidate lines over specified range, never
                // invalidate entire cache since it likely contains
                // other peoples modified data.
                InvalidateL1DCacheLines((uint)start, (uint)length);
                InvalidateL2CacheLines((uint)start, (uint)length);
            }
            finally {
                FlushPrefetch();
                MemoryFence();
                Processor.RestoreInterrupts(en);
            }
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Native methods
        //

        [AccessedByRuntime("defined in mmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(16)]
        private static extern UIntPtr GetTTB();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        public static extern void FlushPrefetch();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        public static extern void MemoryFence();

        //
        // TLB Management
        //

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        public static extern void InvalidateIAndDTlb();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateITlb();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateDTlb();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateITlbEntry(UIntPtr entry);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateDTlbEntry(UIntPtr entry);

        //
        // Cache Management (PRIVATE)
        //
        // All assume interrupts disabled.
        //

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanL1DCacheLines(UIntPtr start, UIntPtr length);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanInvalidateL1DCacheLines(UIntPtr start, UIntPtr length);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateL1DCacheLines(UIntPtr alignedStart, UIntPtr alignedLength);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateL1ICacheLines(UIntPtr alignedStart, UIntPtr alignedLength);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanInvalidateL2CacheLines(UIntPtr alignedStart, UIntPtr alignedLength);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanL2CacheLines(UIntPtr alignedStart, UIntPtr alignedLength);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateL2CacheLines(UIntPtr alignedStart, UIntPtr alignedLength);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanDCacheLine(UIntPtr addr);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanInvalidateDCacheLine(UIntPtr addr);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateICacheLine(UIntPtr addr);

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanL1DCache();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanInvalidateL1DCache();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateL1DCache();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void InvalidateL1ICache();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanInvalidateL2Cache();

        [AccessedByRuntime("defined in XscaleMmu.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        private static extern void CleanL2Cache();
    }
}
