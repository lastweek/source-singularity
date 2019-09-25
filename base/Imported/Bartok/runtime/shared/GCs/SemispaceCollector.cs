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

    using Microsoft.Bartok.Runtime;
    using System.Collections;
    using System.Runtime.CompilerServices;
    using System.Threading;

#if SINGULARITY_KERNEL
    using Microsoft.Singularity;
#endif

    [NoCCtor]
    internal unsafe class SemispaceCollector: GenerationalCollector
    {

        // WARNING: don't initialize any static fields in this class!

        internal static CopyScan[] copyScanners;

        internal static SemispaceCollector instance;

        // Visitor instances used for marking objects
        private static ForwardReferenceVisitor generalReferenceVisitor;
        private static ForwardThreadReference threadReferenceVisitor;
        private static RegisterPinnedReference pinnedReferenceVisitor;
        private static ForwardOnlyReferenceVisitor forwardOnlyReferenceVisitor;

        private SemispaceCollector() {
        }

        public static new void Initialize() {
            GenerationalCollector.Initialize();
            // copyScanners = new CopyScan[MAX_GENERATION+1];
            copyScanners = (CopyScan[])
                BootstrapMemory.Allocate(typeof(CopyScan[]),
                                         (uint)MAX_GENERATION+1);
            for (int i = (int)MIN_GENERATION; i <= (int)MAX_GENERATION; i++) {
                switch (GC.copyscanType) {
                  case CopyScanType.CheneyScan: {
                      copyScanners[i] = (CopyScan)
                          BootstrapMemory.Allocate(typeof(CheneyScan));
                      break;
                  }
                  case CopyScanType.HierarchicalScan: {
                      copyScanners[i] = (CopyScan)
                          BootstrapMemory.Allocate(typeof(HierarchicalScan));
                      break;
                  }
                  case CopyScanType.NestedHierarchicalScan: {
                      copyScanners[i] = (CopyScan)
                          BootstrapMemory.Allocate(typeof(NestedHierarchicalScan));
                      break;
                  }
                  default: {
                      VTable.NotReached("Unknown CopyScan type: "+
                                        GC.copyscanType);
                      break;
                  }
                }
                copyScanners[i].Initialize((PageType) i);
            }
            // SemispaceCollector.instance = new SemispaceCollector();
            SemispaceCollector.instance = (SemispaceCollector)
                BootstrapMemory.Allocate(typeof(SemispaceCollector));
            // generalReferenceVisitor = new ForwardReferenceVisitor();
            SemispaceCollector.generalReferenceVisitor = (ForwardReferenceVisitor)
                BootstrapMemory.Allocate(typeof(ForwardReferenceVisitor));
            // threadReferenceVisitor = new ForwardThreadReference(generalReferenceVisitor);
            SemispaceCollector.threadReferenceVisitor = (ForwardThreadReference)
                BootstrapMemory.Allocate(typeof(ForwardThreadReference));
            // pinnedReferenceVisitor = new RegisterPinnedReference();
            SemispaceCollector.pinnedReferenceVisitor = (RegisterPinnedReference)
                BootstrapMemory.Allocate(typeof(RegisterPinnedReference));
            // forwardOnlyReferenceVisitor = new ForwardOnlyReferenceVisitor();
            SemispaceCollector.forwardOnlyReferenceVisitor = (ForwardOnlyReferenceVisitor)
                BootstrapMemory.Allocate(typeof(ForwardOnlyReferenceVisitor));
        }

        internal override void TruncateOlderAllocationAreas(int generation) {
            for (int i = (int)MIN_GENERATION; i <= generation; i++) {
                copyScanners[i].TruncateAllocationArea();
            }
        }

        internal override void CollectGeneration(int generation,
                                                 UIntPtr generationPageCount)
        {
            UIntPtr fromSpacePageCountTotal = UIntPtr.Zero;
            for (int i = MinGeneration; i <= generation; i++) {
                fromSpacePageCountTotal += fromSpacePageCounts[i];
            }

            PageType maxDestGeneration = (generation < (int)MAX_GENERATION)
                ? (PageType)(generation+1)
                : MAX_GENERATION;

            // The real work: find the roots, copy reachable objects
            CollectorStatistics.Event(GCEvent.ComputeRootSet);
#if !VC
            TryAllManager.PreGCHookTryAll();
#endif
            bool onlyNew = false;
            if (generation == (int)nurseryGeneration) {
                onlyNew = true;
            }
            MultiUseWord.PreGCHook(false, /* don't use shadows */
                                   onlyNew /* only scan new EMUs */);
            Finalizer.PrepareCollectFinalizers();
            CallStack.ScanStacks(null, pinnedReferenceVisitor);
            pinnedReferenceVisitor.ProcessPinnedPages(generalReferenceVisitor);
            CallStack.ScanStacks(threadReferenceVisitor, null);
            Thread.VisitBootstrapData(generalReferenceVisitor);
#if SINGULARITY
            Thread.UpdateAfterGC();
#endif
            Thread currentThread = Thread.threadTable[collectorThreadIndex];
#if SINGULARITY_KERNEL
            Kernel.VisitSpecialData(generalReferenceVisitor);
            Kernel.UpdateAfterGC(currentThread);
#endif
            MultiUseWord.VisitStrongRefs(generalReferenceVisitor,
                                         false /* Don't use shadows */);
#if !VC
            TryAllManager.VisitStrongRefs(generalReferenceVisitor);
#endif
            StaticData.ScanStaticData(generalReferenceVisitor);
            if ((PageType)generation < MAX_GENERATION) {
                installedRemSet.Clean();
                this.ScanRemSet((PageType) generation);
            }
            installedRemSet.Reset();
            CollectorStatistics.Event(GCEvent.TraceStart);
            this.ScanAndCopy(maxDestGeneration);
            CollectorStatistics.Event(GCEvent.TraceSpecial);
            WeakReference.Process(forwardOnlyReferenceVisitor, true, true);
            Finalizer.ResurrectCandidates(forwardOnlyReferenceVisitor,
                                          generalReferenceVisitor,
                                          true);
            this.ScanAndCopy(maxDestGeneration);
            WeakReference.Process(forwardOnlyReferenceVisitor, true, false);
            MultiUseWord.VisitWeakRefs(forwardOnlyReferenceVisitor,
                                       false /* Don't use shadows */);
#if !VC
            TryAllManager.VisitWeakRefs(forwardOnlyReferenceVisitor);
#endif
            CollectorStatistics.Event(GCEvent.CollectionComplete);
            // Clean up the auxiliary data structures
            for (int i = MinGeneration + 1; i <= (int)maxDestGeneration; i++) {
                copyScanners[i].Cleanup();
            }
            UnmanagedPageList.ReleaseStandbyPages();
            pinnedReferenceVisitor.CleanPinnedPages();
            MultiUseWord.PostGCHook(onlyNew);
            Finalizer.ReleaseCollectFinalizers();
#if !VC
            TryAllManager.PostGCHookTryAll();
#endif
        }

        internal override void EnableHeap() {
            base.EnableHeap();
            // Ensure that we don't call any type initializers during a GC
            ArrayList pageList = new ArrayList();
            pageList.Add(new UIntPtr(11));
            pageList.Add(new UIntPtr(10));
            UIntPtrComparer comparer = new UIntPtrComparer();
            pageList.Sort(comparer);
        }

        // Internal workings of the collector

        // Scan is large and will be inlined here.  This is a performance
        // workaround that performs manual specialization of the Scan method.
        [NoInline]
        private void ScanRemSet(PageType generation) {
            installedRemSet.Scan(generalReferenceVisitor, generation);
        }


        private void ScanAndCopy(PageType maxDestGeneration) {
            bool repeat = true;
            while (repeat) {
                repeat = false;
                for (int gen = MinGeneration; gen <= (int)maxDestGeneration; gen++) {
                    if (copyScanners[gen].Scan(generalReferenceVisitor)) {
                        repeat = true;
                    }
                }
            }
        }

        // No objects can be resurrected using this mechanism
        private class ForwardOnlyReferenceVisitor : NonNullReferenceVisitor
        {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsZombiePage(pageType)) {
                    VTable.Assert(PageTable.IsGcPage(pageType) ||
                                  PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType),
                                  "Semispace:ForwardOnlyReferenceVisitor");
                    return;
                }
                PageType gen = PageTable.ZombieToLive(pageType);
                UIntPtr vtableAddr = Allocator.GetObjectVTable(addr);
                UIntPtr vtablePageIndex = PageTable.Page(vtableAddr);
                if (PageTable.Type(vtablePageIndex) == gen) {
                    // The vtable field is really a forwarding pointer
                    *loc = vtableAddr;
                } else {
                    // The object was not live
                    *loc = UIntPtr.Zero;
                }
            }

#region HELP_DEVIRT
            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            internal override UIntPtr VisitReferenceFields(Object obj)
            {
                return this.VisitReferenceFields(Magic.addressOf(obj),
                                                 obj.vtable);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            [InlineIntoOnce]
            internal override
            UIntPtr VisitReferenceFields(UIntPtr objectBase, VTable vtable)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, objectBase);
                return VisitReferenceFieldsTemplate(ref objDesc);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [Inline]
            protected override unsafe sealed
            void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
            {
                base.Filter(location, ref objDesc);
            }
#endregion

        }

        internal class ForwardReferenceVisitor : NonNullReferenceVisitor
        {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr objAddr = *loc;
                UIntPtr page = PageTable.Page(objAddr);
                Trace.Log(Trace.Area.Pointer,
                          "FwdRef: loc={0}, addr={1}, page={2}",
                          __arglist(loc, objAddr, page));
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsZombiePage(pageType)) {
                    VTable.Assert(PageTable.IsGcPage(pageType) ||
                                  PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType),
                                  "Semispace:ForwardReferenceVisitor");
                    return;
                }
                PageType gen = PageTable.ZombieToLive(pageType);
                VTable.Assert(gen > MIN_GENERATION);
                Object obj = Magic.fromAddress(objAddr);
                UIntPtr vtableAddr = *obj.VTableFieldAddr;
                UIntPtr vtablePageIndex = PageTable.Page(vtableAddr);
                if (PageTable.Type(vtablePageIndex) == gen) {
                    // The vtable field is really a forwarding pointer
                    Trace.Log(Trace.Area.Pointer,
                              "FwdRef: VT fwd: {0} -> {1}",
                              __arglist(objAddr, vtableAddr));
                    *loc = vtableAddr;
                    return;
                }
                Object newObject = copyScanners[(int)gen].Copy(obj);
                *loc = Magic.addressOf(newObject);
            }

#region HELP_DEVIRT
            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            internal override UIntPtr VisitReferenceFields(Object obj)
            {
                return this.VisitReferenceFields(Magic.addressOf(obj),
                                                 obj.vtable);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            [InlineIntoOnce]
            internal override
            UIntPtr VisitReferenceFields(UIntPtr objectBase, VTable vtable)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, objectBase);
                return VisitReferenceFieldsTemplate(ref objDesc);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [Inline]
            protected override unsafe sealed
            void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
            {
                base.Filter(location, ref objDesc);
            }
#endregion

        }

        private class ForwardThreadReference : NonNullReferenceVisitor
        {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                Trace.Log(Trace.Area.Pointer,
                          "FwdThrRef: loc={0}, addr={1}, page={2}",
                          __arglist(loc, addr, page));
                PageType pageType = PageTable.Type(page);
                // if an object "spills" into a page that 
                // is pinned, and the object is copied 
                // during a collection, we will end up with
                // the first part of the object in a zombie page
                // the second part of the object in a GC page.
                // We need to find the start of the object and
                // use that to determine whether the object has
                // been moved.
                if (!PageTable.IsZombiePage(pageType) &&
                    !PageTable.IsGcPage(pageType)) {
                    VTable.Assert(PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType) ||
                                  VTable.BuildC2Mods,
                                  "Semispace:ForwardThreadReference");
                    return;
                }
                
                UIntPtr objectPtr = InteriorPtrTable.Find(addr);
                if (objectPtr == addr) {
                    generalReferenceVisitor.Visit(loc);
                } else {
                    // we can check for the page type of 
                    // objectPtr here to see if it is zombie page. 
                    // If true we can just return.
                    UIntPtr newObject = objectPtr;
                    generalReferenceVisitor.Visit(&newObject);
                    UIntPtr newAddr = newObject + (addr - objectPtr);
                    Trace.Log(Trace.Area.Pointer,
                              "FwdThrRef: {0} -> {1}",
                              __arglist(addr, newAddr));
                    *loc = newAddr;
                }
            }

#region HELP_DEVIRT
            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            internal override UIntPtr VisitReferenceFields(Object obj)
            {
                return this.VisitReferenceFields(Magic.addressOf(obj),
                                                 obj.vtable);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            [InlineIntoOnce]
            internal override
            UIntPtr VisitReferenceFields(UIntPtr objectBase, VTable vtable)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, objectBase);
                return VisitReferenceFieldsTemplate(ref objDesc);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [Inline]
            protected override unsafe sealed
            void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
            {
                base.Filter(location, ref objDesc);
            }
#endregion

            internal ForwardReferenceVisitor ptrVisitor;

        }

        private class RegisterPinnedReference : NonNullReferenceVisitor
        {

            // BUGBUG: We are allocating an ArrayList while the collector
            // is running.  If the ArrayList gets big enough to be
            // allocated in the older generation, then the RemSet has the
            // potential to overflow since the boxed integers will reside
            // in the young generation.  We should eventually eliminate
            // the use of ArrayList in this class as well as avoid boxing
            // the page indices.

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsZombiePage(pageType)) {
                    VTable.Assert(PageTable.IsGcPage(pageType) ||
                                  PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType) ||
                                  VTable.BuildC2Mods,
                                  "Semispace:RegisterPinnedReference:1");
                    return;
                }
                PageType gen = PageTable.ZombieToLive(pageType);
                UIntPtr pinnedObjectAddr = InteriorPtrTable.Find(addr);
                if (pinnedPageList == null) {
                    pinnedPageList = new ArrayList();
                    comparer = new UIntPtrComparer();
                }
                Object pinnedObject = Magic.fromAddress(pinnedObjectAddr);
                UIntPtr objectSize =
                    ObjectLayout.ObjectSize(pinnedObjectAddr,
                                            pinnedObject.vtable);
                UIntPtr beforeObjectAddr = pinnedObjectAddr - PreHeader.Size;
                UIntPtr pastObjectAddr = beforeObjectAddr + objectSize;
                UIntPtr firstPage = PageTable.Page(beforeObjectAddr);
                UIntPtr lastPage = PageTable.Page(pastObjectAddr - 1);
                for (UIntPtr i = firstPage; i <= lastPage; i++) {
                    if (!pinnedPageList.Contains(i)) {
                        Trace.Log(Trace.Area.Pointer,
                                  "RegPin: ptr={0} page={1} gen={2}",
                                  __arglist(pinnedObjectAddr, i, gen));
                        GenerationalCollector.gcPromotedTable[(int) gen-1] +=
                            PageTable.PageSize;
                        pinnedPageList.Add(i);
                    }
                }
            }

#region HELP_DEVIRT
            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            internal override UIntPtr VisitReferenceFields(Object obj)
            {
                return this.VisitReferenceFields(Magic.addressOf(obj),
                                                 obj.vtable);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            [InlineIntoOnce]
            internal override
            UIntPtr VisitReferenceFields(UIntPtr objectBase, VTable vtable)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, objectBase);
                return VisitReferenceFieldsTemplate(ref objDesc);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [Inline]
            protected override unsafe sealed
            void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
            {
                base.Filter(location, ref objDesc);
            }
#endregion

            internal void ProcessPinnedPages(ReferenceVisitor ptrVisitor) {
                if (pinnedPageList == null || pinnedPageList.Count == 0) {
                    return;
                }
                pinnedPageList.Sort(comparer);
                int limit = pinnedPageList.Count;
                for (int i = 0; i < limit; i++) {
                    UIntPtr page = (UIntPtr) pinnedPageList[i];
                    PageType fromSpaceType = PageTable.Type(page);
                    VTable.Assert(PageTable.IsZombiePage(fromSpaceType),
                                  "Semispace:RegisterPinnedReference:2");
                    PageType toSpaceType =
                        PageTable.ZombieToLive(fromSpaceType);
                    PageTable.SetType(page, toSpaceType);
                }
                int pageIndex = 0;
                while (pageIndex < limit) {
                    UIntPtr startPage = (UIntPtr) pinnedPageList[pageIndex];
                    UIntPtr endPage = startPage + 1;
                    pageIndex++;
                    while (pageIndex < limit &&
                           (UIntPtr) pinnedPageList[pageIndex] == endPage) {
                        pageIndex++;
                        endPage++;
                    }
                    UIntPtr objectAddr = FirstPinnedObjectAddr(startPage);
                    UIntPtr pastAddr = PostPinnedObjectAddr(endPage);
                    while (objectAddr < pastAddr) {
                        if (Allocator.IsAlignment(objectAddr)) {
                            objectAddr += UIntPtr.Size;
                        } else if (BumpAllocator.IsUnusedSpace(objectAddr)) {
                            objectAddr = (PageTable.PagePad(objectAddr) +
                                          PreHeader.Size);
                        } else {
                            Object obj = Magic.fromAddress(objectAddr);
                            objectAddr += ptrVisitor.VisitReferenceFields(obj);
                        }
                    }
                }
            }

            internal void CleanPinnedPages() {
                if (pinnedPageList == null || pinnedPageList.Count == 0) {
                    return;
                }
                int pageIndex = 0;
                int limit = pinnedPageList.Count;
                UIntPtr lastPostPinnedAddr = UIntPtr.Zero;
                while (pageIndex < limit) {
                    UIntPtr startPage = (UIntPtr) pinnedPageList[pageIndex];
                    UIntPtr endPage = startPage + 1;
                    pageIndex++;
                    while (pageIndex < limit &&
                           (UIntPtr) pinnedPageList[pageIndex] == endPage) {
                        pageIndex++;
                        endPage++;
                    }
                    // Zero out the area between the start of the page and
                    // the first object on the page
                    UIntPtr firstObjectAddr = FirstPinnedObjectAddr(startPage);
                    UIntPtr firstAddr = firstObjectAddr - PreHeader.Size;
                    UIntPtr trashAddr = PageTable.PageAddr(startPage);
                    if (firstAddr < trashAddr) {
                        // The first object "spills" into the previous page,
                        // presumably by no more than HEADER_BYTES bytes
                        VTable.Assert(
                            PageTable.Page(firstAddr) == startPage - 1,
                            "Semispace:RegisterPinnedReference:3");
                        // Prepare to zero the preceding page unless it also
                        // had pinned data on it
                        trashAddr = PageTable.PageAddr(startPage - 1);
                        InteriorPtrTable.ClearFirst(startPage - 1);
                        if (trashAddr >= lastPostPinnedAddr) {
                            // Need to mark the spilled-onto page live to
                            // keep the spilled data around
                            PageType fromSpaceType =
                                PageTable.Type(startPage - 1);
                            VTable.Assert(
                                PageTable.IsZombiePage(fromSpaceType),
                                "Semispace:RegisterPinnedReference:4");
                            PageType toSpaceType =
                                PageTable.ZombieToLive(fromSpaceType);
                            PageTable.SetType(startPage - 1, toSpaceType);
                        }
                    }
                    // If lastPostPinnedAddr is on the page that trashAddr
                    // starts, pinned data from the last run of pinned pages
                    // and pinned data from this run of pinned data are on the
                    // same page, so just write alignment tokens from
                    // lastPostPinnedAddr to the first pinned object.
                    // Otherwise, write an unused marker at lastPostPinnedAddr
                    // since the rest of its page must be copied or dead.
                    if (trashAddr < lastPostPinnedAddr) {
                        trashAddr = lastPostPinnedAddr;
                    } else {
                        CleanPageTail(lastPostPinnedAddr);
                    }

                    if (GC.remsetType == RemSetType.Cards &&
                        trashAddr < firstAddr) {
                        UIntPtr firstCard = CardTable.CardNo(trashAddr);
                        UIntPtr lastCard = CardTable.CardNo(firstAddr -1);

                        if (!OffsetTable.NoObjectPtrToTheCard(firstCard)) {
                            UIntPtr offset= OffsetTable.GetOffset(firstCard);
                            UIntPtr objPtr =
                                CardTable.CardAddr(firstCard) + offset;
                            UIntPtr size = OffsetTable.ObjectSize(objPtr);
                            VTable.Assert
                                ((objPtr + size - PreHeader.Size <= trashAddr)
                                 || (objPtr >= trashAddr),
                                 "Object should be totally "
                                 + "above or below trashAddr");
                            if (objPtr >= trashAddr) {
                                // The offset in this card needs to be updated
                                OffsetTable.ClearCards(firstCard, firstCard);
                            }
                        }

                        OffsetTable.ClearCards(firstCard+1, lastCard-1);

                        if (lastCard != CardTable.CardNo(firstObjectAddr)) {
                            OffsetTable.ClearCards(lastCard, lastCard);
                        } else {
                            VTable.Assert(OffsetTable.GetOffset(lastCard)
                                          >= (firstObjectAddr
                                              - CardTable.CardAddr(lastCard)),
                                          "wrong offset");
                        }
                    }

                    {
                        // trashAddr should go back at most one page.

                        UIntPtr trashPage = PageTable.Page(trashAddr);
                        UIntPtr firstObjectAddrPage =
                            PageTable.Page(firstObjectAddr);
                        VTable.Assert((trashPage == firstObjectAddrPage - 1)
                                      || (trashPage == firstObjectAddrPage));
                    }

                    // If the InteriorPtrTable already had a value, then this is
                    // redundant, but if the call to First above has to compute
                    // the value, then (since it won't store it in the table) we
                    // should store it.  Why?  At this point the previous page
                    // would be "connected" to this one.  After this collection
                    // the previous page will be unused or re-used and unrelated
                    // to this page and subsequent calls to First would then
                    // rely on it making the leap between unrelated pages.
                    InteriorPtrTable.SetFirst(firstObjectAddr);

                    while (trashAddr < firstAddr) {
                        Allocator.WriteAlignment(trashAddr);
                        trashAddr += UIntPtr.Size;
                    }

                    // Zero out the area between the last whole object on
                    // the last page and the end of the last page
                    UIntPtr pastAddr = PostPinnedObjectAddr(endPage);
                    UIntPtr newEndPage =
                        PageTable.Page(PageTable.PagePad(pastAddr));
                    while (endPage < newEndPage) {
                        // The last object spills into the next page(s), so
                        // mark those page(s) live
                        PageType fromPageType = PageTable.Type(endPage);
                        if (PageTable.IsZombiePage(fromPageType)) {
                            PageType toSpaceType =
                                PageTable.ZombieToLive(fromPageType);
                            PageTable.SetType(endPage, toSpaceType);
                        } else {
                            // final page might be live already because
                            // something else on it was pinned.
                            // pageIndex has already been incremented,
                            // so it points to the start of the next
                            // set of contiguous pages
                            VTable.Assert(
                                PageTable.IsLiveGcPage(fromPageType) &&
                                pageIndex < limit &&
                                endPage ==
                                    (UIntPtr) pinnedPageList[pageIndex],
                                "Semispace:RegisterPinnedReference:5");
                        }
                        ++endPage;
                    }
                    lastPostPinnedAddr = pastAddr;
                }
                CleanPageTail(lastPostPinnedAddr);
                pinnedPageList = null;
                comparer = null;
            }

            private static void CleanPageTail(UIntPtr postPinnedAddr) {
                if (!PageTable.PageAligned(postPinnedAddr)) {
                    // If postPinnedAddr points to the first object on its page,
                    // then we are removing all objects (specifically the part
                    // of the object that the InteriorPtrTable tracks, the
                    // vtables) from the page, so we should clear the page's
                    // entry in the InteriorPtrTable.

                    UIntPtr page = PageTable.Page(postPinnedAddr);
                    UIntPtr firstObjPtr = InteriorPtrTable.First(page);
                    if (firstObjPtr > postPinnedAddr) {
                        VTable.Assert
                            (firstObjPtr - PreHeader.Size >= postPinnedAddr,
                             "postPinnedAddr should not point to the "
                             + "interior of an object (1)");
                        InteriorPtrTable.ClearFirst(page);
                    } else if (!BumpAllocator.IsUnusedSpace(firstObjPtr)) {
                        UIntPtr firstObjSize =
                            InteriorPtrTable.ObjectSize(firstObjPtr);
                        VTable.Assert
                            (firstObjPtr + firstObjSize - PreHeader.Size
                             <= postPinnedAddr,
                             "postPinnedAddr should not point to the "
                             + "interior of an object (2)");
                    }

                    UIntPtr byteCount = PageTable.PagePad(postPinnedAddr)
                                        - postPinnedAddr;
                    Util.MemClear(postPinnedAddr, byteCount);
                    BumpAllocator.WriteUnusedMarker(postPinnedAddr);

                    if (GC.remsetType == RemSetType.Cards && byteCount > 0) {
                        UIntPtr firstCard = CardTable.CardNo(postPinnedAddr);
                        UIntPtr lastCard =
                            CardTable.CardNo(postPinnedAddr + byteCount -1);

                        if (!OffsetTable.NoObjectPtrToTheCard(firstCard)) {
                            UIntPtr offset = OffsetTable.GetOffset(firstCard);
                            UIntPtr objPtr =
                                CardTable.CardAddr(firstCard) + offset;
                            UIntPtr size = OffsetTable.ObjectSize(objPtr);

                            VTable.Assert
                                ((objPtr + size - PreHeader.Size
                                  <= postPinnedAddr)
                                 || (objPtr >= postPinnedAddr),
                                 "Object should be totally "
                                 + "above or below postPinnedAddr");
                            if (objPtr >= postPinnedAddr) {
                                OffsetTable.ClearCards(firstCard, firstCard);
                            }
                        }

                        OffsetTable.ClearCards(firstCard + 1, lastCard);
                    }
                }
            }

            private static UIntPtr FirstPinnedObjectAddr(UIntPtr startPage) {
                return InteriorPtrTable.First(startPage);
            }

            private static UIntPtr PostPinnedObjectAddr(UIntPtr endPage) {
                UIntPtr endAddr = PageTable.PageAddr(endPage);
                UIntPtr postLastObjectAddr = InteriorPtrTable.Last(endPage-1);
                if (postLastObjectAddr < endAddr &&
                    !BumpAllocator.IsUnusedSpace(postLastObjectAddr)) {
                    // If the next object straddles into the next page,
                    // return the location just past the object
                    Object lastObject = Magic.fromAddress(postLastObjectAddr);
                    UIntPtr lastObjectSize =
                        ObjectLayout.ObjectSize(postLastObjectAddr,
                                                lastObject.vtable);
                    postLastObjectAddr += lastObjectSize;
                }
                return postLastObjectAddr - PreHeader.Size;
            }

            internal ArrayList pinnedPageList;
            internal UIntPtrComparer comparer; // type defined in UIntPtr.cs

        }

    }

    // N.B. Must get two UIntPtrs!

    internal class UIntPtrComparer : Collections.IComparer
    {
        public int Compare(Object x, Object y)
        {
            VTable.Assert(x is UIntPtr);
            VTable.Assert(y is UIntPtr);

            UIntPtr u = (UIntPtr) x;
            UIntPtr v = (UIntPtr) y;

            if(u < v) {
                return -1;
            }
            if(u > v) {
                return 1;
            }
            return 0;
        }
    }

}
