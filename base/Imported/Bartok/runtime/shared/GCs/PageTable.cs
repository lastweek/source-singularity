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

    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;
    using Microsoft.Bartok.Runtime;

#if SINGULARITY_KERNEL
    using Microsoft.Singularity;
    using Microsoft.Singularity.Memory;
    using Sing_MemoryManager = Microsoft.Singularity.Memory.MemoryManager;
#elif SINGULARITY_PROCESS
    using Microsoft.Singularity;
    using Microsoft.Singularity.V1.Services;
#endif

    [RequiredByBartok]
    [AccessedByRuntime("referenced from brtforgc.asm/halforgc.asm")]
    abstract internal class PageTable {

        // WARNING: don't initialize any static fields in this class
        // without manually running the class constructor at startup!

        // The following are the several flavors for page table design:
        // 1. Centralized: Only one table for all the memory. There are two
        //    cases within it: HIMEM or not. HIMEM forces the table to put beyond
        //    4G. HIMEM means for correctness testing, not for performance.
        //    In both cases, an address is composed of two parts:
        //              (Page number) (offset in the page)
        // 2. Otherwise: there are multiple page tables (DistributedPT). Two cases are allowed:
        //      (1) FlatDistributedPT: All the page tables manage the same-sized
        //              space. A page table itself is within the space it manages, and the
        //              offset of it to the starting address of the space is fixed.
        //              An address has three parts:
        //                  (Segment number)(page number in the segment)(Offset in the page)
        //              Since a page table is located in a fixed offset of the segment it
        //              manages, we do not need a segment table. The segment number
        //              tells the segment address. With the fixed offset, we get the
        //              the page table.
        //      (2) two level hierarchy. An address has also three parts But
        //              each page table can be put at an arbitrary place. So we need a
        //              segment table to find the requested page table. Not implemented yet. But
        //              is straightforward based on the flat distributed page table.
        //     Note: to keep consistent with the previous central table, function Page()
        //     will return (segment number)(page number in the segment) as the page number.

        // Note: In distributed case, pageTableCount refers to the total entries in all
        // page tables that have already been allocated.

        internal static UIntPtr pageTableCount;
#if SINGULARITY
        public static UIntPtr baseAddr;
        public static UIntPtr limitAddr;
#endif

        [AccessedByRuntime("referenced from brtforgc.asm/halforgc.asm")]
        internal static unsafe uint *halPageDescriptor;

        [Intrinsic]
        internal static PTType ptType;

#if SINGULARITY
        internal const uint kernelProcessTag = 0x10000;
#endif

#if SINGULARITY_KERNEL
        internal const uint ProcessPageMask = Sing_MemoryManager.ProcessPageMask;
        internal static uint processTag;

        internal static unsafe void Initialize()
        {
            Tracing.Log(Tracing.Debug, "Initialize.");

            processTag = kernelProcessTag;
            baseAddr = Sing_MemoryManager.KernelBaseAddr;
            pageTableCount = Sing_MemoryManager.KernelPageCount;
            limitAddr = baseAddr + (pageTableCount << PageBits);
            halPageDescriptor = Sing_MemoryManager.KernelPageTable;
        }
#elif SINGULARITY_PROCESS
        internal const uint ProcessPageMask = 0xffff0000u;
        internal static uint processTag;

        internal static unsafe void Initialize()
        {
            Tracing.Log(Tracing.Debug, "Initialize.");

            processTag = PageTableService.GetProcessTag();
            baseAddr = PageTableService.GetBaseAddress();
            pageTableCount = PageTableService.GetPageCount();
            limitAddr = baseAddr + (pageTableCount << PageBits);
            halPageDescriptor = PageTableService.GetPageTable();
        }
#else

        private static uint processTag {
            get { VTable.NotReached("should not be using processTag outside of Singularity"); return 0; }
            set { VTable.NotReached("should not be using processTag outside of Singularity"); }
        }

        // Initialization sets up page table in the memory. The pagetable must be
        // set up before anything else (bootstrapmemory, GC,...) works.

        // This function is implemented in each subclass by "new static", which
        // is in general not ideal, but here since we explicitly call them by the class
        // names, and they do not call other "new static" functions, there
        // should not be any confusion.

        // Also note that every function in this class that have different implementations
        // in subclasses is implemented by testing ptType, and then calling the specific
        // class. We cannot use the same idea as GC does, which use an "instance" of
        // the specified GC type. The reason is that the instance needs allocate space
        // from bootstrapmemory, which however, at each allocation, needs to change
        // the pagetable. Since the pagetable has not generated an instance yet, the
        // bootstrapmemory cannot access the pagetable through an instance.

        [PreInitRefCounts]
        [NoStackLinkCheck]
        internal static void Initialize() {
            switch(ptType) {
              case PTType.CentralPT: {
                  CentralPT.Initialize();
                  break;
              }
              case PTType.CentralPTHimem: {
                  CentralPTHimem.Initialize();
                  break;
              }
              case PTType.FlatDistributedPT: {
                  FlatDistributedPT.Initialize();
                  break;
              }
              case PTType.FlatDistributedPTTest: {
                  FlatDistributedPTTest.Initialize();
                  break;
              }
              default: {
                  VTable.NotReached("Unknown PT type: "+ptType);
                  break;
              }
            }
        }
#endif

        [System.Diagnostics.Conditional("SINGULARITY")]
        internal static void SetProcessTag(uint tag) {
            processTag = tag;
        }

        internal static bool Dump(ushort process)
        {
            UIntPtr pages = (UIntPtr) 0;
            UIntPtr freePages = UIntPtr.Zero;
            UIntPtr usedPages = UIntPtr.Zero;
            UIntPtr stackPages = UIntPtr.Zero;
            UIntPtr fixedPages = UIntPtr.Zero;
            UIntPtr sharedPages = UIntPtr.Zero;
            UIntPtr unknownPages = UIntPtr.Zero;

            for (UIntPtr i = (UIntPtr) 1; i < pageTableCount; i++) {
                if (Process(i) != process) {
                    continue;
                }

                PageType type = Type(i);

                pages++;
                switch (type) {
                    case PageType.UnusedDirty:
                    case PageType.UnusedClean:
                    case PageType.Unallocated:
                        freePages++;
                        break;

                    case PageType.NonGC:
                    case PageType.System:
                        fixedPages++;
                        break;

                    case PageType.Stack:
                        stackPages++;
                        break;

                    case PageType.Shared:
                        sharedPages++;
                        break;

                    case PageType.Unknown:
                        unknownPages++;
                        break;

                    case PageType.Owner2:
                    case PageType.Owner3:
                        type = PageType.Owner2;
                        usedPages++;
                        break;

                    default:
                        usedPages++;
                        break;
                }
            }

            if (pages > 0) {
                VTable.DebugPrint("{0:d6}: free={1:d6}, use={2:d6}, stk={3:d6}, fix={4:d6}, shr={5:d6}, unk={6:d6}\n",
                                  __arglist(process,
                                            freePages,
                                            usedPages,
                                            stackPages,
                                            fixedPages,
                                            sharedPages,
                                            unknownPages));
                return true;
            }
            return false;
        }

        internal static void Dump(String s)
        {
            VTable.DebugPrint("PageTable.Dump({0}):\n",
                              __arglist(s));

            ushort empty = 0;
            for (ushort proc = 0; proc < 10240; proc++) {
                if (Dump(proc)) {
                    empty = 0;
                }
                else {
                    empty++;
                }
                if (empty > 512) {
                    break;
                }
            }
            Dump((ushort)0xffff);

            PageType lastType = Type(UIntPtr.Zero);
            ushort lastProcess = Process((UIntPtr) 1);
#if NOTHING
            UIntPtr begin = UIntPtr.Zero;
#endif
            UIntPtr freePages = UIntPtr.Zero;
            UIntPtr usedPages = UIntPtr.Zero;
            UIntPtr stackPages = UIntPtr.Zero;
            UIntPtr fixedPages = UIntPtr.Zero;
            UIntPtr sharedPages = UIntPtr.Zero;
            UIntPtr unknownPages = UIntPtr.Zero;

            for (UIntPtr i = (UIntPtr) 1; i < pageTableCount; i++) {
                PageType type = Type(i);

                switch (type) {
                    case PageType.UnusedDirty:
                    case PageType.UnusedClean:
                    case PageType.Unallocated:
                        freePages++;
                        break;
                    case PageType.NonGC:
                    case PageType.System:
                        fixedPages++;
                        break;

                    case PageType.Stack:
                        stackPages++;
                        break;

                    case PageType.Shared:
                        sharedPages++;
                        break;

                    case PageType.Unknown:
                        unknownPages++;
                        break;

                    case PageType.Owner2:
                    case PageType.Owner3:
                        type = PageType.Owner2;
                        usedPages++;
                        break;

                    default:
                        usedPages++;
                        break;
                }

                if ((type != lastType) || (Process(i) != lastProcess)) {
#if NOTHING
                    VTable.DebugPrint("  {0:x8}..{1:x8} ({2:d6} pages) : {3:x2} for {4:d5}\n",
                                      __arglist(
                                          ((ulong)begin) << PageBits,
                                          ((ulong)i) << PageBits,
                                          i - begin,
                                          (uint)lastType,
                                          lastProcess));
#endif
                    lastType = type;
                    lastProcess = Process(i);
#if NOTHING
                    begin = i;
#endif
                }
            }

#if NOTHING
            VTable.DebugPrint("  {0:x8}..{1:x8} ({2:d6} pages) : {3:x2} for {4:d5}\n",
                              __arglist(
                                  ((ulong)begin) << PageBits,
                                  ((ulong)pageTableCount) << PageBits,
                                  pageTableCount - begin,
                                  (uint)lastType,
                                  lastProcess));
#endif

            VTable.DebugPrint(" =====: free={1:d6}, use={2:d6}, stk={3:d6}, fix={4:d6}, shr={5:d6}, unk={6:d6}\n",
                              __arglist(0,
                                        freePages,
                                        usedPages,
                                        stackPages,
                                        fixedPages,
                                        sharedPages,
                                        unknownPages));
        }

        internal static byte PageBits {
            [Inline]
            get { return 12; }
        }

        internal static UIntPtr PageSize {
            [Inline]
            get { return (UIntPtr)(1U << PageBits); }
        }

        internal static UIntPtr PageMask {
            [Inline]
            get { return PageSize - 1; }
        }

        internal static UIntPtr PageAlignMask {
            [Inline]
            get { return ~PageMask; }
        }

        [Inline]
        internal static PageType MyType(UIntPtr page) {
#if SINGULARITY
            uint value = PageTableEntry(page);
            if ((value & ProcessPageMask) == processTag) {
                return (PageType)(value & 0xf);
            }
            else {
                return PageType.Unknown;
            }
#else
            return Type(page);
#endif
        }

        [Inline]
        internal static PageType Type(UIntPtr page) {
            VTable.Assert(page < pageTableCount, "page out of count");
            return (PageType)(PageTableEntry(page) & 0xf);
        }

        [Inline]
        internal static void SetType(UIntPtr page, PageType newType) {
            VTable.Assert(page < pageTableCount);

            // for the Generational Collector, keep track of the max and min
            // page of each generation.

            switch(GC.gcType) {
#if !SINGULARITY || ADAPTIVE_COPYING_COLLECTOR || SEMISPACE_COLLECTOR || SLIDING_COLLECTOR
                case GCType.AdaptiveCopyingCollector:
                case GCType.SemispaceCollector:
                case GCType.SlidingCollector:
                    int generation = (int)newType;

                    if (generation >= (int)GCs.GenerationalGCData.MIN_GENERATION
                        && generation <= (int)GCs.GenerationalGCData.MAX_GENERATION)
                    {
                        if (page < GCs.GenerationalGCData.MinGenPage[generation])
                        {
                            GCs.GenerationalGCData.MinGenPage[generation] = page;
                        }
                        if (page > GCs.GenerationalGCData.MaxGenPage[generation])
                        {
                            GCs.GenerationalGCData.MaxGenPage[generation] = page;
                        }
                    }
                    break;
#endif
#if !SINGULARITY || MARK_SWEEP_COLLECTOR || CONCURRENT_MS_COLLECTOR || NULL_COLLECTOR
                case GCType.MarkSweepCollector:
                case GCType.TableMarkSweepCollector:
                case GCType.ReferenceCountingCollector:
                case GCType.ConcurrentMSCollector:
                case GCType.CoCoMSCollector:
                case GCType.AtomicRCCollector:
                case GCType.DeferredReferenceCountingCollector:
                case GCType.NullCollector:
                    // do nothing if not a Generational Collector
                    break;
#endif
                default:
                    VTable.Assert(false, "Unknown Garbage Collector.");
                    break;
            }

            uint value = (PageTableEntry(page) & ~0xfU) | (uint)newType;
            SetPageTableEntry(page, value);
        }

        [System.Diagnostics.Conditional("DEBUG")]
        internal static void VerifyType(UIntPtr page, PageType pageType)
        {
            VTable.Assert(PageTable.Type(page) == pageType);
        }

        [Inline]
        internal static uint Extra(UIntPtr page) {
            VTable.Assert(page < pageTableCount);
            uint result = (PageTableEntry(page) & 0xfff0U) >> 4;
            VTable.Assert(((short) result)>=0);
            return result;
        }

        [Inline]
        internal static void SetExtra(UIntPtr page, uint extra) {
            VTable.Assert(page < pageTableCount);
            VTable.Assert(extra <= 0xfff);
            uint value = (PageTableEntry(page) & ~0xfff0U) | (extra << 4);
            SetPageTableEntry(page, value);
        }

        [System.Diagnostics.Conditional("DEBUG")]
        internal static void VerifyExtra(UIntPtr page, uint extra) {
            VTable.Assert(Extra(page) == extra);
        }

        [Inline]
        internal static ushort Process(UIntPtr page) {
#if SINGULARITY
            VTable.Assert(page < pageTableCount);
            return (ushort)((PageTableEntry(page) & 0xffff0000u) >> 16);
#else
            return 0;
#endif
        }

        [Inline]
        [System.Diagnostics.Conditional("SINGULARITY")]
        internal static void SetProcess(UIntPtr page, ushort processId) {
            VTable.Assert(page < pageTableCount);
            uint value = (PageTableEntry(page) & ~0xffff0000U) | ((uint) processId << 16);
            SetPageTableEntry(page, value);
        }

#if SINGULARITY
        [Inline]
        private static uint ProcessTag(UIntPtr page) {
            VTable.Assert(page < pageTableCount);
            return PageTableEntry(page) & 0xffff0000u;
        }
#endif

        [Inline]
        [System.Diagnostics.Conditional("SINGULARITY")]
        private static void SetProcessTag(UIntPtr page, uint processTag) {
            VTable.Assert(page < pageTableCount);
            VTable.Assert(processTag > 0x0000ffffU);
            uint  value = (PageTableEntry(page) & ~0xffff0000U) | processTag;
            SetPageTableEntry(page, value);
        }

        [Inline]
        internal static void SetType(UIntPtr startPage,
                                     UIntPtr pageCount,
                                     PageType newType)
        {
            while (pageCount > UIntPtr.Zero) {
                SetType(startPage, newType);
                startPage++;
                pageCount--;
            }
        }

        [System.Diagnostics.Conditional("DEBUG")]
        internal static void VerifyType(UIntPtr startPage,
                                        UIntPtr pageCount,
                                        PageType pageType)
        {
            while (pageCount > UIntPtr.Zero) {
                VerifyType(startPage, pageType);
                startPage++;
                pageCount--;
            }
        }

        [Inline]
        internal static void SetExtra(UIntPtr startPage,
                                      UIntPtr pageCount,
                                      uint extra)
        {
            while (pageCount > UIntPtr.Zero) {
                SetExtra(startPage, extra);
                startPage++;
                pageCount--;
            }
        }

        [System.Diagnostics.Conditional("DEBUG")]
        internal static void VerifyExtra(UIntPtr startPage,
                                         UIntPtr pageCount,
                                         uint extra)
        {
            while (pageCount > UIntPtr.Zero) {
                VerifyExtra(startPage, extra);
                startPage++;
                pageCount--;
            }
        }

        [Inline]
        [System.Diagnostics.Conditional("SINGULARITY")]
        internal static void SetProcess(UIntPtr startPage,
                                        UIntPtr pageCount)
        {
            PageTable.SetProcessTag(startPage, pageCount, processTag);
        }

        [Inline]
        [System.Diagnostics.Conditional("SINGULARITY")]
        internal static void SetProcess(UIntPtr startPage,
                                        UIntPtr pageCount,
                                        ushort processId)
        {
            while (pageCount > UIntPtr.Zero) {
                SetProcess(startPage, processId);
                startPage++;
                pageCount--;
            }
        }

        [Inline]
        [System.Diagnostics.Conditional("SINGULARITY")]
        internal static void SetProcessTag(UIntPtr startPage,
                                           UIntPtr pageCount,
                                           uint processTag)
        {
            while (pageCount > UIntPtr.Zero) {
                SetProcessTag(startPage, processTag);
                startPage++;
                pageCount--;
            }
        }

        [Inline]
        internal static bool IsGcPage(UIntPtr page)
        {
            return IsGcPage(Type(page));
        }

        [Inline]
        internal static bool IsMyGcPage(UIntPtr page) {
            return (PageTable.IsMyPage(page) && PageTable.IsGcPage(page));
        }

        // NOTE: The following 5 functions are dependent on the definition of
        // System.GCs.PageType.

        [Inline]
        internal static bool IsGcPage(PageType pageType) {
            return pageType >= PageType.Owner0;
        }

        [Inline]
        internal static bool IsZombiePage(PageType pageType) {
            return (pageType & PageType.TypeMask) == PageType.ZombieMask;
        }

        [Inline]
        internal static bool IsLiveGcPage(PageType pageType) {
            return ( (pageType >= PageType.Owner0) && (pageType < PageType.ZombieMask));
        }

        [Inline]
        internal static PageType ZombieToLive(PageType pageType)
        {
            VTable.Assert(IsZombiePage(pageType), "not a zombie page");
            PageType type = (PageType)(pageType - PageType.Zombie);
            return type;
        }

        [Inline]
        internal static PageType LiveToZombie(PageType pageType)
        {
            VTable.Assert(IsLiveGcPage(pageType), "not a live GC page");
            return (pageType | PageType.Zombie);
        }
        // End of PageType dependent functions

        [Inline]
        internal static bool IsNonGcPage(PageType pageType) {
            return pageType == PageType.NonGC;
        }

        [Inline]
        internal static bool IsStackPage(PageType pageType) {
            return pageType == PageType.Stack;
        }

        [Inline]
        internal static bool IsSystemPage(PageType pageType) {
            return pageType == PageType.System;
        }

        [Inline]
        internal static bool IsSharedPage(PageType pageType) {
            return pageType == PageType.Shared;
        }

        [Inline]
        internal static bool IsUnknownPage(PageType pageType) {
            return pageType == PageType.Unknown;
        }

        [Inline]
        internal static bool IsUnallocatedPage(PageType pageType) {
            return pageType == PageType.Unallocated;
        }

        [Inline]
        internal static bool IsUnusedPage(UIntPtr page) {
            return IsUnusedPageType(PageTable.Type(page));
        }

        [Inline]
        internal static bool IsUnusedPageType(PageType pageType) {
            return (pageType == PageType.UnusedDirty ||
                    pageType == PageType.UnusedClean);
        }

        [Inline]
        internal static bool IsMyPage(UIntPtr page) {
#if SINGULARITY
            return PageTable.ProcessTag(page) == processTag;
#else
            return true;
#endif
        }

#if SINGULARITY
        [Inline]
        internal static bool IsKernelPage(UIntPtr page) {
            return PageTable.ProcessTag(page) == kernelProcessTag;
        }
#endif

        [Inline]
        internal static bool IsForeignAddr(UIntPtr addr) {
#if SINGULARITY
            return (addr < baseAddr) || (addr >= limitAddr);
#else
            return false;
#endif
        }

        [Inline]
        internal static UIntPtr Page(UIntPtr addr) {
#if SINGULARITY
            VTable.Assert((addr >= baseAddr) && (addr < limitAddr));
            return (addr - baseAddr) >> PageBits;
#else
            return (addr >> PageBits);
#endif
        }

        [Inline]
        internal static bool IsAddrOnPage(UIntPtr addr, UIntPtr page) {
#if SINGULARITY
            return ((addr - baseAddr) >> PageBits) == page;
#else
            return (addr >> PageBits) == page;
#endif
        }

        [Inline]
        internal static UIntPtr PageCount(UIntPtr size) {
            return ((size + PageMask) >> PageBits);
        }

        [Inline]
        internal static UIntPtr PageAddr(UIntPtr page) {
#if SINGULARITY
            return ((page << PageBits) + baseAddr);
#else
            return (page << PageBits);
#endif
        }

        [Inline]
        internal static UIntPtr RegionSize(UIntPtr pageCount) {
            return (pageCount << PageBits);
        }

        [Inline]
        internal static bool PageAligned(UIntPtr addr) {
            return ((addr & PageMask) == UIntPtr.Zero);
        }

        [Inline]
        internal static UIntPtr PageAlign(UIntPtr addr) {
            return addr & PageAlignMask;
        }

        [Inline]
        internal static UIntPtr PagePad(UIntPtr addr) {
            return ((addr + PageMask) & ~PageMask);
        }

        [Inline]
        internal static UIntPtr PadBytesToPages(UIntPtr size)
        {
            return ((size + PageSize - 1) >> PageBits);
        }

        // The following functions have an implementation in each specific subclass. To avoid
        // any potential "new static" confusion, we have the names with "Impl" suffix.

        [Inline]
        internal static uint PageTableEntry(UIntPtr page)
        {
            switch(ptType) {
              case PTType.CentralPT:
              case PTType.CentralPTHimem:
                  return CentralPT.PageTableEntryImpl(page);

#if !SINGULARITY
              case PTType.FlatDistributedPT:
              case PTType.FlatDistributedPTTest:
                  return FlatDistributedPT.PageTableEntryImpl(page);
#endif
              default: {
                  VTable.NotReached("Unknown PT type: "+ptType);
                  return 0xffffffff;
              }
            }
        }

        [Inline]
        internal static void SetPageTableEntry(UIntPtr page, uint value)
        {
            switch(ptType) {
              case PTType.CentralPT:
              case PTType.CentralPTHimem: {
                  CentralPT.SetPageTableEntryImpl(page, value);
                  break;
              }
#if !SINGULARITY
              case PTType.FlatDistributedPT:
              case PTType.FlatDistributedPTTest: {
                    FlatDistributedPT.SetPageTableEntryImpl(page, value);
                    break;
              }
#endif
              default: {
                  VTable.NotReached("Unknown PT type: "+ptType);
                  break;
              }
            }
        }

        internal static void CreateNewPageTablesIfNecessary(UIntPtr startPage,
                                                            UIntPtr pageCount)
        {
#if !SINGULARITY
            if (ptType == PTType.FlatDistributedPT ||ptType == PTType.FlatDistributedPTTest) {
                    FlatDistributedPT.CreateNewPageTablesIfNecessaryImpl(startPage, pageCount);
           }
#endif
        }

        [Inline]
        internal static unsafe bool ValidMemAddress(void* addr)
        {
#if !SINGULARITY
            if (ptType == PTType.CentralPTHimem) {
                return CentralPTHimem.ValidMemAddressImpl(addr);
            }
#endif
            return true;
        }

    }

}
