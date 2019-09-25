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
    using System.Runtime.CompilerServices;
    using System.Threading;

#if SINGULARITY_KERNEL
    using Microsoft.Singularity;
#endif

    [NoCCtor]
    internal class SlidingCollector: GenerationalCollector {

        internal static SlidingCollector instance;

        // Visitor instances used for marking objects
        private static MarkReferenceVisitor markReferenceVisitor;
        private static RegisterThreadReference registerThreadReferenceVisitor;
        private static RegisterPinnedReference registerPinnedReferenceVisitor;
        private static UpdateThreadReference updateThreadReferenceVisitor;
        private static ForwardReferenceVisitor forwardReferenceVisitor;

        // Internally used data structures
        private UIntPtrQueue skippedPageQueue = new UIntPtrQueue();
        private UIntPtrQueue relocationQueue = new UIntPtrQueue();

      // WARNING: don't initialize any static fields in this class
      // without manually running the class constructor at startup!

        private SlidingCollector() {
        }

        public static new void Initialize() {
            GenerationalCollector.Initialize();
            // SlidingCollector.instance = new SlidingCollector();
            SlidingCollector.instance = (SlidingCollector)
                BootstrapMemory.Allocate(typeof(SlidingCollector));
            // markReferenceVisitor = new MarkReferenceVisitor();
            markReferenceVisitor = (MarkReferenceVisitor)
                BootstrapMemory.Allocate(typeof(MarkReferenceVisitor));
            // registerThreadReferenceVisitor = new RegisterThreadReference();
            registerThreadReferenceVisitor = (RegisterThreadReference)
                BootstrapMemory.Allocate(typeof(RegisterThreadReference));
            // registerPinnedReferenceVisitor = new RegisterPinnedReference();
            registerPinnedReferenceVisitor = (RegisterPinnedReference)
                BootstrapMemory.Allocate(typeof(RegisterPinnedReference));
            // updateThreadReferenceVisitor = new UpdateThreadReference();
            updateThreadReferenceVisitor = (UpdateThreadReference)
                BootstrapMemory.Allocate(typeof(UpdateThreadReference));
            // forwardReferenceVisitor = new ForwardReferenceVisitor();
            forwardReferenceVisitor = (ForwardReferenceVisitor)
                BootstrapMemory.Allocate(typeof(ForwardReferenceVisitor));
        }

        internal override void TruncateOlderAllocationAreas(int generation) {
            // We don't use any allocators for the older generation,
            // so there is nothing to do
        }

        internal override void CollectGeneration(int generation,
                                                 UIntPtr generationPageCount)
        {
            VTable.Assert(IsValidGeneration(generation));
            // 1) Mark the live objects
            CollectorStatistics.Event(GCEvent.TraceStart);
            MultiUseWord.PreGCHook(true /* use shadows */);
            Finalizer.PrepareCollectFinalizers();
            CallStack.ScanStacks(registerThreadReferenceVisitor,
                                 registerPinnedReferenceVisitor);
            registerThreadReferenceVisitor.ForwardReferences();
            if (generation < (int)MAX_GENERATION) {
                // These calls must be done early, as they rely on the
                // contents of Thread.threadTable being intact.
                installedRemSet.Clean();
                installedRemSet.Uniquify();
                this.ScanRemSet((PageType) generation);
            }
            // Process runtime data that is allocated from SystemMemory
            Thread.VisitBootstrapData(markReferenceVisitor);
#if SINGULARITY_KERNEL
            Kernel.VisitSpecialData(markReferenceVisitor);
#endif
            MultiUseWord.VisitStrongRefs(markReferenceVisitor,
                                         true /* use shadows */);
            StaticData.ScanStaticData(markReferenceVisitor);
            CollectorStatistics.Event(GCEvent.TraceSpecial);
            WeakReference.Process(forwardReferenceVisitor, false, true);
            Finalizer.ResurrectCandidates(forwardReferenceVisitor,
                                          markReferenceVisitor,
                                          false);
            markReferenceVisitor.Cleanup();
            // 2) Forward pointers and compact the live objects
            CollectorStatistics.Event(GCEvent.SweepStart, TotalMemory);
            WeakReference.Process(forwardReferenceVisitor, false, false);
            MultiUseWord.VisitWeakRefs(forwardReferenceVisitor,
                                       true /* use shadows */);
            UIntPtr oldAllocPtr;
            UIntPtr newLimit = this.ForwardReferences((PageType)generation,
                                                      out oldAllocPtr);
            this.CompactHeapObjects(oldAllocPtr);
#if SINGULARITY
            Thread.UpdateAfterGC();
#endif
            Thread currentThread = Thread.threadTable[collectorThreadIndex];
#if SINGULARITY_KERNEL
            Kernel.UpdateAfterGC(currentThread);
#endif
            CallStack.ScanStacks(updateThreadReferenceVisitor,
                                 updateThreadReferenceVisitor);
            this.CompactPhaseCleanup(currentThread,
                                     (PageType)generation,
                                     newLimit);
            // Resetting the GC state
            CollectorStatistics.Event(GCEvent.SweepSpecial);
            installedRemSet.Reset();
            MultiUseWord.PostGCHook();
            Finalizer.ReleaseCollectFinalizers();
            CollectorStatistics.Event(GCEvent.CollectionComplete, TotalMemory);
        }

        // Internal workings of the collector

        // Scan is large and will be inlined here.  This is a performance
        // workaround that performs manual specialization of the Scan method.
        [NoInline]
        private void ScanRemSet(PageType generation) {
            installedRemSet.Scan(markReferenceVisitor, generation);
        }


        // Routines for updating pointers to new locations of marked objects
        // No objects can be resurrected using this mechanism
        private class ForwardReferenceVisitor : NonNullReferenceVisitor {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsZombiePage(pageType)) {
                    VTable.Assert(PageTable.IsGcPage(pageType) ||
                                  PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType));
                    return;
                }
                UIntPtr vtableAddr = Allocator.GetObjectVTable(addr);
                if ((vtableAddr & 0x1) == 0x1) {
                    // Link this field to be updated
                    *loc = vtableAddr;
                    Allocator.SetObjectVTable(addr, (UIntPtr) loc+1);
                } else {
                    // Zero the reference (not marked)
                    *loc = UIntPtr.Zero;
                }
            }
        }

        // Routines for marking objects and linking object references
        private class MarkReferenceVisitor : NonNullReferenceVisitor {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsZombiePage(pageType)) {
                    VTable.Assert(PageTable.IsGcPage(pageType) ||
                                  PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType));
                    return;
                }
                UIntPtr vtableAddr = Allocator.GetObjectVTable(addr);
                // Mark object
                if (vtableAddr == UIntPtr.Zero) {
                    VTable.DebugPrint("Found null vtable in MarkReference (loc = 0x{0:x8}, addr = 0x{1:x8})\n",
                                      __arglist(((UIntPtr)loc), addr));
                    VTable.NotReached();
                }
                *loc = vtableAddr;
                Allocator.SetObjectVTable(addr, (UIntPtr) loc+1);
                // If first visit to the object, schedule visit of fields
                if ((vtableAddr & 0x1) == 0) {
                    MarkVisit(addr, vtableAddr & (UIntPtr) ~2U);
                }
            }

            private void MarkVisit(UIntPtr addr, UIntPtr vtableAddr) {
                // Mark scheduling
                if (fMarkInProgress) {
                    ScheduleMarkedObject(addr, vtableAddr);
                } else {
                    fMarkInProgress = true;
                    VTable vtable =
                        Magic.toVTable(Magic.fromAddress(vtableAddr));
                    this.VisitReferenceFields(addr, vtable);
                    this.ProcessScheduledObjects();
                    fMarkInProgress = false;
                }
            }

            private void ScheduleMarkedObject(UIntPtr addr,
                                              UIntPtr vtableAddr) {
                this.markQueue.Write(addr);
                this.markQueue.Write(vtableAddr);
            }

            private void ProcessScheduledObjects() {
                while (!this.markQueue.IsEmpty) {
                    UIntPtr addr = this.markQueue.Read();
                    UIntPtr vtableAddr = this.markQueue.Read();
                    VTable vtable =
                        Magic.toVTable(Magic.fromAddress(vtableAddr));
                    this.VisitReferenceFields(addr, vtable);
                }
            }

            internal void Cleanup() {
                VTable.Assert(this.markQueue.IsEmpty);
                this.markQueue.Cleanup(true);
            }

            private bool fMarkInProgress;
            private UIntPtrQueue markQueue = new UIntPtrQueue();

        }

        // Routines for linking and updating thread pointers
        private class RegisterThreadReference : NonNullReferenceVisitor {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsZombiePage(pageType)) {
                    VTable.Assert(PageTable.IsGcPage(pageType) ||
                                  PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType));
                    return;
                }
                UIntPtr objectAddr = InteriorPtrTable.Find(addr);
                this.threadPtrQueue.Write(objectAddr);
                this.threadPtrQueue.Write(addr - objectAddr);
            }

            internal unsafe void ForwardReferences() {
                UIntPtrQueue.Enumerator queueEnumerator =
                    new UIntPtrQueue.Enumerator(ref this.threadPtrQueue);
                while (queueEnumerator.MoveNext()) {
                    markReferenceVisitor.Visit(queueEnumerator.CurrentAddr);
                    queueEnumerator.MoveNext();
                }
            }

            internal void Cleanup() {
                // Free up the last thread pointer page
                this.threadPtrQueue.Cleanup(true);
            }

            internal UIntPtrQueue threadPtrQueue = new UIntPtrQueue();

        }

        private class RegisterPinnedReference : NonNullReferenceVisitor {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsZombiePage(pageType)) {
                    VTable.Assert(PageTable.IsGcPage(pageType) ||
                                  PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType));
                    return;
                }
                UIntPtr objectAddr = InteriorPtrTable.Find(addr);
                registerThreadReferenceVisitor.threadPtrQueue.Write(objectAddr);
                registerThreadReferenceVisitor.threadPtrQueue.Write(addr-objectAddr);
                *Allocator.GetObjectVTableAddress(objectAddr) |= (UIntPtr) 2U;
            }

        }

        private class UpdateThreadReference : NonNullReferenceVisitor {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                if (!PageTable.IsZombiePage(PageTable.Type(page))) {
                    return;
                }
                UIntPtr objectAddr =
                    registerThreadReferenceVisitor.threadPtrQueue.Read();
                UIntPtr addressDelta =
                    registerThreadReferenceVisitor.threadPtrQueue.Read();
                *loc = objectAddr + addressDelta;
            }

        }

        // Reference updates and object relocation

        private unsafe UIntPtr ForwardReferences(PageType generation,
                                                 out UIntPtr oldAllocPtr)
        {
            VTable.Assert(IsValidGeneration((int)generation));

            UIntPtr destPage = UIntPtr.Zero;
            UIntPtr destCursor;
            UIntPtr destLimit;
            PageType destGeneration;
            if (generation < MAX_GENERATION) {
                destGeneration = generation + 1;
            } else {
                destGeneration = MAX_GENERATION;
            }
            destCursor = UIntPtr.Zero;
            destLimit = UIntPtr.Zero;
            oldAllocPtr = destCursor;
            UIntPtr runLength = UIntPtr.Zero;
            for (UIntPtr i=UIntPtr.Zero; i < PageTable.pageTableCount; i++) {
                if (!IsMyZombiePage(i)) {
                    continue;
                }
                UIntPtr deltaBytes = (UIntPtr) 0x80000000;
                UIntPtr sourceCursor = PageTable.PageAddr(i);
                do {
                    i++;
                } while (i < PageTable.pageTableCount && IsMyZombiePage(i));
                UIntPtr sourceLimit = PageTable.PageAddr(i);
                while (true) {
                    if (sourceCursor >= sourceLimit) {
                        break;
                    }
                    if (Allocator.IsAlignmentMarkerAddr(sourceCursor)) {
                        sourceCursor += UIntPtr.Size;
                        deltaBytes += UIntPtr.Size;
                        continue;
                    }
                    if (BumpAllocator.IsUnusedMarkerAddr(sourceCursor)) {
                        sourceCursor += UIntPtr.Size;
                        sourceCursor = PageTable.PagePad(sourceCursor);
                        deltaBytes = (UIntPtr) 0x80000000;
                        continue;
                    }
                    UIntPtr objectAddr = sourceCursor + PreHeader.Size;
                    UIntPtr vtableOrMarker =
                        Allocator.GetObjectVTable(objectAddr);
                    if (vtableOrMarker == UIntPtr.Zero) {
                        // We found the end of an allocation page
                        sourceCursor = PageTable.PagePad(sourceCursor);
                        deltaBytes = (UIntPtr) 0x80000000;
                        continue;
                    }
                    UIntPtr vtableAddr;
                    if ((vtableOrMarker & 1) != 0) {
                        UIntPtr temp = *(UIntPtr *) (vtableOrMarker - 1);
                        while ((temp & 1) != 0) {
                            temp = *(UIntPtr *) (temp-1);
                        }
                        VTable.Assert(PageTable.IsNonGcPage(PageTable.Type(PageTable.Page(temp))));
                        vtableAddr = temp;
                        if ((temp & 2) != 0) {
                            // Found pinned object
                            SkipDestinationAreas(ref destPage, destCursor,
                                                 ref destLimit,
                                                 sourceCursor);
                            deltaBytes -= (sourceCursor - destCursor);
                            destCursor = sourceCursor;
                            vtableAddr -= 2; // Remove "pinned" bit
                        }
                        Allocator.SetObjectVTable(objectAddr, vtableAddr);
                    } else {
                        vtableAddr = vtableOrMarker;
                    }
                    VTable vtable =
                        Magic.toVTable(Magic.fromAddress(vtableAddr));
                    UIntPtr objectSize =
                        ObjectLayout.ObjectSize(objectAddr, vtable);
                    VTable.Assert(objectSize > 0);
                    if ((vtableOrMarker & 1) != 0) {
                        if (GenerationalCollector.IsLargeObjectSize
                            (objectSize)) {
                            // Don't move large objects
                            SkipDestinationAreas(ref destPage,
                                                 destCursor,
                                                 ref destLimit,
                                                 sourceCursor);
                            UIntPtr localDelta =
                                sourceCursor - destCursor;
                            deltaBytes -= localDelta;
                            if (deltaBytes == UIntPtr.Zero &&
                                runLength != UIntPtr.Zero) {
                                runLength += localDelta;
                            }
                            destCursor = sourceCursor;
                            UIntPtr objLimit = sourceCursor + objectSize;
                            UIntPtr pageEndAddr = PageTable.PagePad(objLimit);
                            objectSize = (pageEndAddr - sourceCursor);
                        } else if (destCursor + objectSize > destLimit) {
                            UIntPtr oldDestCursor = destCursor;
                            FindDestinationArea(ref destPage,
                                                ref destCursor,
                                                ref destLimit,
                                                objectSize,
                                                destGeneration);
                            VTable.Assert(destCursor <= sourceCursor);
                            VTable.Assert(destCursor + objectSize <=
                                          destLimit);
                            deltaBytes -= (destCursor - oldDestCursor);
                        } else if (vtable.baseAlignment > UIntPtr.Size) {
                            uint alignmentMask = vtable.baseAlignment - 1;
                            int offset = PreHeader.Size + UIntPtr.Size;
                            while (((destCursor+offset) & alignmentMask) != 0) {
                                destCursor += UIntPtr.Size;
                                deltaBytes -= UIntPtr.Size;
                                if (deltaBytes == UIntPtr.Zero &&
                                    runLength != UIntPtr.Zero) {
                                    runLength += UIntPtr.Size;
                                }
                            }
                        }
                        if (runLength == UIntPtr.Zero ||
                            deltaBytes != UIntPtr.Zero) {
                            if (runLength != UIntPtr.Zero) {
                                RegisterRelocationEnd(runLength);
                            }
                            RegisterRelocationStart(sourceCursor,
                                                    destCursor);
                            deltaBytes = UIntPtr.Zero;
                            runLength = UIntPtr.Zero;
                        }
                        UIntPtr newObjectAddr = destCursor + PreHeader.Size;
                        do {
                            UIntPtr *ptrAddr = (UIntPtr*) (vtableOrMarker-1);
                            vtableOrMarker = *ptrAddr;
                            *ptrAddr = newObjectAddr;
                        } while ((vtableOrMarker & 1) != 0);
                        destCursor += objectSize;
                        runLength += objectSize;
                    } else {
                        deltaBytes += objectSize;
                        if (runLength != UIntPtr.Zero) {
                            RegisterRelocationEnd(runLength);
                        }
                        runLength = UIntPtr.Zero;
                    }
                    sourceCursor += objectSize;
                }
            }
            if (runLength != UIntPtr.Zero) {
                RegisterRelocationEnd(runLength);
            }
            return destCursor;
        }

        private unsafe void SkipDestinationAreas(ref UIntPtr destPage,
                                                 UIntPtr destCursor,
                                                 ref UIntPtr destLimit,
                                                 UIntPtr sourceCursor)
        {
            UIntPtr cursorPage = PageTable.Page(destCursor);
            UIntPtr sourcePage = PageTable.Page(sourceCursor);
            if (cursorPage != sourcePage) {
                UIntPtr destPageLimit = PageTable.PagePad(destCursor);
                if (destPageLimit != destCursor) {
                    cursorPage++;
                }
                VTable.Assert(PageTable.PageAligned(destLimit));
                UIntPtr limitPage = PageTable.Page(destLimit);
                while (destPage < sourcePage) {
                    if (cursorPage < limitPage) {
                        this.RegisterSkippedPages(cursorPage, limitPage);
                    }
                    do {
                        destPage++;
                    } while (!IsMyZombiePage(destPage));
                    cursorPage = destPage;
                    do {
                        destPage++;
                    } while (IsMyZombiePage(destPage));
                    limitPage = destPage;
                }
                destLimit = PageTable.PageAddr(limitPage);
                VTable.Assert(destPage > sourcePage);
                VTable.Assert(cursorPage <= sourcePage);
                if (cursorPage < sourcePage) {
                    this.RegisterSkippedPages(cursorPage, sourcePage);
                    cursorPage = sourcePage;
                }
                InteriorPtrTable.ClearFirst(cursorPage, destPage);
                InteriorPtrTable.SetFirst(sourceCursor + PreHeader.Size);
                if (GC.remsetType == RemSetType.Cards) {
                     OffsetTable.ClearLast(PageTable.PageAddr(cursorPage),
                           PageTable.PageAddr(destPage)-1);
                }                                
            }
        }

        private unsafe void FindDestinationArea(ref UIntPtr destPage,
                                                ref UIntPtr destCursor,
                                                ref UIntPtr destLimit,
                                                UIntPtr objectSize,
                                                PageType destGeneration)
        {
            VTable.Assert(IsValidGeneration((int)destGeneration));

            UIntPtr cursorPage = PageTable.Page(destCursor);
            UIntPtr limitPage = PageTable.Page(destLimit);
            UIntPtr pageAddr = PageTable.PagePad(destCursor);
            UIntPtr testPage = limitPage;
            UIntPtr endTestPage = PageTable.PageCount(destCursor+objectSize);
            if (destCursor > UIntPtr.Zero &&
                IsMyZombiePage(PageTable.Page(destCursor-1))) {
                VTable.Assert(destPage == limitPage);
                while (IsMyZombiePage(testPage) ||
                       (testPage < endTestPage &&
                        (PageTable.IsUnusedPage(testPage)))) {
                    testPage++;
                }
                if (testPage >= endTestPage) {
                    // We can expand the current region
                    endTestPage = testPage;
                    VTable.Assert(PageTable.PageAligned(destLimit));
                    InteriorPtrTable.ClearFirst(limitPage, testPage);
                    if (GC.remsetType == RemSetType.Cards) {
                        OffsetTable.ClearLast(PageTable.PageAddr(limitPage),
                           PageTable.PageAddr(testPage)-1);
                    }              
                    while (limitPage != endTestPage) {
                        VTable.Assert(PageTable.IsUnusedPage(destPage));
                        do {
                            destPage++;
                        } while (destPage < endTestPage &&
                                 PageTable.IsUnusedPage(destPage));
                        bool fCleanPages = true;
                        bool status =
                            PageManager.TryReserveUnusedPages(null, limitPage,
                                                              destPage-limitPage,
                                                              nurseryGeneration,
                                                              ref fCleanPages);
                        VTable.Assert(status);
                        MakeZombiePages(limitPage, destPage - limitPage,
                                        destGeneration);
                        while (destPage < endTestPage &&
                               IsMyZombiePage(destPage)) {
                            destPage++;
                        }
                        limitPage = destPage;
                    }
                    destLimit = PageTable.PageAddr(limitPage);
                    return;
                }
            }
            if (destCursor != pageAddr) {
                cursorPage++;
            }
            if (cursorPage != limitPage) {
                this.RegisterSkippedPages(cursorPage, limitPage);
            }
            // Find new region big enough to contain object
            UIntPtr neededPages = PageTable.PageCount(objectSize);
            UIntPtr prefixPage;
            while (true) {
                do {
                    destPage++;
                } while (!IsMyZombiePage(destPage));
                cursorPage = destPage;
                prefixPage = cursorPage;
                do {
                    destPage++;
                } while (IsMyZombiePage(destPage));
                limitPage = destPage;
                if (neededPages <= limitPage - cursorPage) {
                    break;
                }
                // Check for following unused pages
                endTestPage = cursorPage + neededPages;
                VTable.Assert(endTestPage <= PageTable.pageTableCount);
                while (destPage < endTestPage &&
                       (PageTable.IsUnusedPage(destPage) ||
                        (IsMyZombiePage(destPage)))) {
                    destPage++;
                }
                if (destPage == endTestPage) {
                    break;
                }
                // Check for preceding unused pages
                if (destPage >= neededPages) {
                    endTestPage = destPage - neededPages;
                    prefixPage = cursorPage - 1;
                    while (prefixPage >= UIntPtr.Zero &&
                           PageTable.IsUnusedPage(prefixPage)) {
                        prefixPage--;
                    }
                    prefixPage++;
                    if (prefixPage == endTestPage) {
                        break;
                    }
                }
                // Register any skipped regions of pages
                this.RegisterSkippedPages(cursorPage, limitPage);
                while (limitPage < destPage) {
                    VTable.Assert(PageTable.IsUnusedPage(limitPage));
                    do {
                        limitPage++;
                    } while (limitPage < destPage &&
                             PageTable.IsUnusedPage(limitPage));
                    cursorPage = limitPage;
                    while (limitPage < destPage && IsMyZombiePage(limitPage)) {
                        limitPage++;
                    }
                    if (cursorPage != limitPage) {
                        this.RegisterSkippedPages(cursorPage, limitPage);
                    }
                }
            }
            // We found an area big enough.  Commit the pre- and
            // postfix areas of unused pages
            if (prefixPage != cursorPage) {
                bool fCleanPages = true;
                bool status =
                    PageManager.TryReserveUnusedPages(null, prefixPage,
                                                      cursorPage-prefixPage,
                                                      nurseryGeneration,
                                                      ref fCleanPages);
                VTable.Assert(status);
                MakeZombiePages(prefixPage, cursorPage - prefixPage,
                                destGeneration);
            }
            while (destPage != limitPage) {
                // Mark the region of unused pages as fromspace
                UIntPtr unusedPage = limitPage;
                VTable.Assert(PageTable.IsUnusedPage(unusedPage));
                do {
                    unusedPage++;
                } while (unusedPage < destPage &&
                         PageTable.IsUnusedPage(unusedPage));
                bool fCleanPages = true;
                bool status =
                    PageManager.TryReserveUnusedPages(null, limitPage,
                                                      unusedPage-limitPage,
                                                      nurseryGeneration,
                                                      ref fCleanPages);
                VTable.Assert(status);
                MakeZombiePages(limitPage, unusedPage - limitPage,
                                destGeneration);
                // Skip any sections of pages already marked as fromspace
                limitPage = unusedPage;
                while (limitPage < destPage && IsMyZombiePage(limitPage)) {
                    limitPage++;
                }
            }
            destCursor = PageTable.PageAddr(prefixPage);
            destLimit = PageTable.PageAddr(limitPage);
            // Take ownership of the new pages
            InteriorPtrTable.ClearFirst(prefixPage, limitPage);
            InteriorPtrTable.SetFirst(destCursor + PreHeader.Size);
            if (GC.remsetType == RemSetType.Cards) {
                  OffsetTable.ClearLast(PageTable.PageAddr(prefixPage),
                        PageTable.PageAddr(limitPage)-1);
             }                            
        }

        private void RegisterSkippedPages(UIntPtr startPage,
                                          UIntPtr limitPage)
        {
            this.skippedPageQueue.Write(startPage);
            this.skippedPageQueue.Write(limitPage);
        }

        private void RegisterRelocationStart(UIntPtr sourceAddress,
                                             UIntPtr destinationAddress)
        {
            this.relocationQueue.Write(sourceAddress);
            this.relocationQueue.Write(destinationAddress);
        }

        private void RegisterRelocationEnd(UIntPtr runLength)
        {
            this.relocationQueue.Write(runLength);
        }

        private unsafe void CompactHeapObjects(UIntPtr previousEnd) {
            while (!this.relocationQueue.IsEmpty) {
                UIntPtr sourceAddress = this.relocationQueue.Read();
                UIntPtr destinationAddress = this.relocationQueue.Read();
                UIntPtr runLength = this.relocationQueue.Read();
                if (previousEnd != destinationAddress) {
                    VTable.Assert(previousEnd < destinationAddress);
                    if (PageTable.Page(destinationAddress) !=
                        PageTable.Page(previousEnd+PreHeader.Size)) {
                        if (!PageTable.PageAligned(previousEnd)) {
                            UIntPtr pageLimit = PageTable.PagePad(previousEnd);
                            BumpAllocator.WriteUnusedMarker(previousEnd);
                            previousEnd += UIntPtr.Size;
                            Util.MemClear(previousEnd,
                                          pageLimit - previousEnd);
                        }
                        if (!PageTable.PageAligned(destinationAddress)) {
                            // This only happens before pinned objects and
                            // large objects
                            UIntPtr start =
                                PageTable.PageAlign(destinationAddress);
                            VTable.Assert(previousEnd <= start);
                            while (start < destinationAddress) {
                                Allocator.WriteAlignment(start);
                                start += UIntPtr.Size;
                            }
                        }
                        UIntPtr objAddr = destinationAddress + PreHeader.Size;
                        InteriorPtrTable.SetFirst(objAddr);
                    } else {
                        VTable.Assert(previousEnd < destinationAddress);
                        UIntPtr start = previousEnd;
                        while (start < destinationAddress) {
                            Allocator.WriteAlignment(start);
                            start += UIntPtr.Size;
                        }
                    }
                }
                Util.MemCopy(destinationAddress, sourceAddress, runLength);
                previousEnd = destinationAddress + runLength;
            }
            // Zero out the end of the allocation page
            if (!PageTable.PageAligned(previousEnd)) {
                UIntPtr pageLimit = PageTable.PagePad(previousEnd);
                Util.MemClear(previousEnd, pageLimit - previousEnd);
            }
            this.relocationQueue.Cleanup(true);
        }

        private void CompactPhaseCleanup(Thread currentThread,
                                         PageType generation,
                                         UIntPtr newLimitPtr)
        {
            VTable.Assert(IsValidGeneration((int)generation));

            registerThreadReferenceVisitor.Cleanup();
            // Free up skipped pages
            while (!this.skippedPageQueue.IsEmpty) {
                UIntPtr start = this.skippedPageQueue.Read();
                UIntPtr finish = this.skippedPageQueue.Read();
                InteriorPtrTable.ClearFirst(start, finish);
                PageManager.FreePageRange(start, finish);
                if (GC.remsetType == RemSetType.Cards) {
                     OffsetTable.ClearLast(PageTable.PageAddr(start),
                           PageTable.PageAddr(finish)-1);
                }                
            }
            this.skippedPageQueue.Cleanup(true);
            // Release the queue standby pages
            UnmanagedPageList.ReleaseStandbyPages();
            // Update the ownership information for the copied data
            PageType destGeneration =
                (generation == MAX_GENERATION) ?
                MAX_GENERATION :
                (PageType) (generation + 1);
            UIntPtr limitPage =
                PageTable.Page(PageTable.PagePad(newLimitPtr));
            for (UIntPtr i = UIntPtr.Zero; i < limitPage; i++) {
                if (IsMyZombiePage(i)) {
                    PageTable.SetType(i, (PageType)destGeneration);
                }
            }
        }

    }

}
