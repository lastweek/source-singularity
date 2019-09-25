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

#if SINGULARITY
    using Microsoft.Singularity;
#if SINGULARITY_PROCESS
    using Microsoft.Singularity.V1.Services;
    using Microsoft.Singularity.V1.Threads;
#else
    using Microsoft.Singularity.Memory;
#endif
#endif

    [NoCCtor]
    internal class MarkSweepCollector: StopTheWorldCollector
    {
#if OS_WINCE // || ISA_ARM
        private const uint InitialTrigger = (uint)(1 << 20);
        private const uint MinTrigger = (uint)(1 << 20);
        private const uint MaxTrigger = (uint)(1 << 22);
#else
        private const uint InitialTrigger = (uint)(1 << 24);
        private const uint MinTrigger = (uint)(1 << 24);
        private const uint MaxTrigger = (uint)(1 << 26);
#endif

        private static UIntPtr collectionTrigger;

        internal static MarkSweepCollector instance;

        // Visitor instances used for marking objects
        private static MarkReferenceVisitor markReferenceVisitor;
        private static MarkAndProcessReferenceVisitor markAndProcessReferenceVisitor;
        private static UpdateReferenceVisitor updateReferenceVisitor;
        private static ThreadMarkReferenceVisitor threadMarkReferenceVisitor;
        private static SweepVisitor sweepVisitor;

        private static int traceTime;
        private static int sweepTime;
        private static int numCollections;

        private MarkSweepCollector() {
        }

        public static new void Initialize() {
            StopTheWorldCollector.Initialize();
            SegregatedFreeList.Initialize();
            // instance = new MarkSweepCollector();
            MarkSweepCollector.instance = (MarkSweepCollector)
                BootstrapMemory.Allocate(typeof(MarkSweepCollector));
            // markReferenceVisitor = new MarkReferenceVisitor();
            markReferenceVisitor = (MarkReferenceVisitor)
                BootstrapMemory.Allocate(typeof(MarkReferenceVisitor));
            // markAndProcessReferenceVisitor = new MarkAndProcessReferenceVisitor();
            markAndProcessReferenceVisitor = (MarkAndProcessReferenceVisitor)
                BootstrapMemory.Allocate(typeof(MarkAndProcessReferenceVisitor));
            // updateReferenceVisitor = new UpdateReferenceVisitor();
            updateReferenceVisitor = (UpdateReferenceVisitor)
                BootstrapMemory.Allocate(typeof(UpdateReferenceVisitor));
            // threadMarkReferenceVisitor = new ThreadMarkReferenceVisitor();
            threadMarkReferenceVisitor = (ThreadMarkReferenceVisitor)
                BootstrapMemory.Allocate(typeof(ThreadMarkReferenceVisitor));
            // sweepVisitor = new SweepVisitor();
            sweepVisitor = (SweepVisitor)
                BootstrapMemory.Allocate(typeof(SweepVisitor));
            collectionTrigger = (UIntPtr) InitialTrigger;
        }

        // GCInterface methods
        internal override bool IsOnTheFlyCollector {
            get {
                return false;
            }
        }

        internal override void CollectStopped(int currentThreadIndex,
                                              int generation)
        {
#if SINGULARITY
#if DEBUG
    #if THREAD_TIME_ACCOUNTING
            UIntPtr preGcTotalBytes = SegregatedFreeList.TotalBytes;
    #endif
            DebugStub.WriteLine("~~~~~ Start MarkSweep Cleanup  [data={0:x8}, pid={1:x3}]",
                                __arglist(SegregatedFreeList.TotalBytes,
                                          PageTable.processTag >> 16));
#endif
#if SINGULARITY_KERNEL
    #if THREAD_TIME_ACCOUNTING
            TimeSpan ticks = Thread.CurrentThread.ExecutionTime;
            TimeSpan ticks2 = SystemClock.KernelUpTime;
    #else
            TimeSpan ticks = SystemClock.KernelUpTime;
    #endif
#elif SINGULARITY_PROCESS
    #if THREAD_TIME_ACCOUNTING
            TimeSpan ticks = ProcessService.GetThreadTime();
            TimeSpan ticks2 = ProcessService.GetUpTime();
    #else
            TimeSpan ticks = ProcessService.GetUpTime();
    #endif
#endif
#endif
            int before=0;
            if (VTable.enableGCTiming) {
                before=Environment.TickCount;
            }
            if (GC.IsProfiling) {
                GcProfiler.NotifyPreGC(MinGeneration);
                // non-generational collector, so pretend Gen0
                // Calls like ResurrectCandidates below can cause
                // allocations and thus, potentially, profiler
                // notifications.  However, at that time the heap is
                // damaged in the sense that VPtrs have bits OR-ed in
                // for object marking.  We do not want to accept
                // profiling during this window.
                //
                // There is no synchronization issue with setting this
                // flag because it will only be consulted by the
                // thread that sets and resets it.
                HeapDamaged = true;
            }
            // 1) Mark the live objects
            CollectorStatistics.Event(GCEvent.TraceStart);
#if !VC
            TryAllManager.PreGCHookTryAll();
#endif
            MultiUseWord.PreGCHook(false /* don't use shadows */);
            Finalizer.PrepareCollectFinalizers();
            int countThreads =
                CallStack.ScanStacks(threadMarkReferenceVisitor,
                                     threadMarkReferenceVisitor);
            Thread.VisitBootstrapData(markAndProcessReferenceVisitor);
#if SINGULARITY_KERNEL
            Kernel.VisitSpecialData(markAndProcessReferenceVisitor);
#endif
            MultiUseWord.VisitStrongRefs(markAndProcessReferenceVisitor,
                                         false /* Don't use shadows */);
#if !VC
            TryAllManager.VisitStrongRefs(markAndProcessReferenceVisitor);
#endif
            StaticData.ScanStaticData(markAndProcessReferenceVisitor);
            CollectorStatistics.Event(GCEvent.TraceSpecial);
            WeakReference.Process(updateReferenceVisitor, true, true);
            Finalizer.ResurrectCandidates(updateReferenceVisitor,
                                          markAndProcessReferenceVisitor, true);
            markReferenceVisitor.Cleanup();
            UnmanagedPageList.ReleaseStandbyPages();
            // 2) Sweep the garbage objects
            int afterTrace=0;
            if (VTable.enableGCTiming) {
                afterTrace=Environment.TickCount;
            }
            CollectorStatistics.Event(GCEvent.SweepStart, TotalMemory);
            WeakReference.Process(updateReferenceVisitor, true, false);
            MultiUseWord.VisitWeakRefs(updateReferenceVisitor,
                                       false /* Don't use shadows */);
#if !VC
            TryAllManager.VisitWeakRefs(updateReferenceVisitor);
#endif
            SegregatedFreeList.VisitAllObjects(sweepVisitor);
            SegregatedFreeList.RecycleGlobalPages();
            SegregatedFreeList.CommitFreedData();
            CollectorStatistics.Event(GCEvent.SweepSpecial);
            MultiUseWord.PostGCHook();
            if (GC.IsProfiling) {
                HeapDamaged = false;
                // Allocations may occur inside the PostGCHook.  Hopefully a
                // sufficiently limited quantity that we don't recursively
                // trigger a GC.
                GcProfiler.NotifyPostGC(ProfileRoots, ProfileObjects);
            }
            Finalizer.ReleaseCollectFinalizers();
#if !VC
            TryAllManager.PostGCHookTryAll();
#endif
            CollectorStatistics.Event(GCEvent.CollectionComplete,
                                      TotalMemory);
            if (VTable.enableGCTiming) {
                int after=Environment.TickCount;
                numCollections++;
                traceTime+=(afterTrace-before);
                sweepTime+=(after-afterTrace);
            }
            // 3) Determine a new collection trigger
            UIntPtr testTrigger = (UIntPtr) this.TotalMemory >> 2;
            UIntPtr minTrigger = (UIntPtr) MinTrigger;
            UIntPtr maxTrigger = (UIntPtr) MaxTrigger;
            collectionTrigger =
                (testTrigger > minTrigger) ?
                (testTrigger < maxTrigger ?
                 testTrigger : maxTrigger) : minTrigger;
#if SINGULARITY
#if SINGULARITY_KERNEL
    #if THREAD_TIME_ACCOUNTING
            int procId = Thread.CurrentProcess.ProcessId;
            ticks = Thread.CurrentThread.ExecutionTime - ticks;
            ticks2 = SystemClock.KernelUpTime - ticks2;
    #else
            ticks = SystemClock.KernelUpTime - ticks;
    #endif
            //Thread.CurrentProcess.SetGcPerformanceCounters(ticks, (long) SegregatedFreeList.TotalBytes);
#elif SINGULARITY_PROCESS
    #if THREAD_TIME_ACCOUNTING
            ushort procId = ProcessService.GetCurrentProcessId();
            ticks = ProcessService.GetThreadTime()  - ticks;
            ticks2 = ProcessService.GetUpTime() - ticks2;
    #else
            ticks = ProcessService.GetUpTime() - ticks;
    #endif
            //ProcessService.SetGcPerformanceCounters(ticks, (long) SegregatedFreeList.TotalBytes);
#endif
#if DEBUG
#if THREAD_TIME_ACCOUNTING
            DebugStub.WriteLine("~~~~~ Finish MarkSweep Cleanup [data={0:x8}, diff={7:x8} pid={1:x3}, ms(Thread)={2:d6}, ms(System)={3:d6}, thds={4}, procId={5}, tid={6}]",
                                __arglist(SegregatedFreeList.TotalBytes,
                                          PageTable.processTag >> 16,
                                          ticks.Milliseconds,
                                          ticks2.Milliseconds,
                                          countThreads,
                                          procId,
                                          Thread.GetCurrentThreadIndex(),
                                          preGcTotalBytes - SegregatedFreeList.TotalBytes
                                          ));
#else
            DebugStub.WriteLine("~~~~~ Finish MarkSweep Cleanup [data={0:x8}, pid={1:x3}, ms={2:d6}, thds={3}]",
                __arglist(SegregatedFreeList.TotalBytes,
                PageTable.processTag >> 16,
                ticks.Milliseconds,
                countThreads));
#endif
#endif
#endif
        }

        internal override int CollectionGeneration(int genRequest)
        {
            return MinGeneration;
        }

        [Inline]
        protected override void CreateObject(Object obj,
                                             VTable vtable,
                                             Thread currentThread)
        {
            base.CreateObject(obj, vtable, currentThread);
            ProfileAllocation(obj);
        }

        [Inline]
        internal override UIntPtr AllocateObjectMemory(UIntPtr numBytes,
                                                       uint alignment,
                                                       Thread currentThread)
        {
            UIntPtr resultAddr =
                SegregatedFreeList.AllocateFast(currentThread,
                                                numBytes, alignment);
            if (resultAddr == UIntPtr.Zero) {
                resultAddr = this.AllocateObjectMemorySlow(numBytes, alignment,
                                                           currentThread);
            }
            return resultAddr;
        }

        [NoInline]
        private UIntPtr AllocateObjectMemorySlow(UIntPtr numBytes,
                                                 uint alignment,
                                                 Thread currentThread)
        {
            if (NewBytesSinceGCExceeds(collectionTrigger) &&
                GC.allocationGCInhibitCount == 0) {
                //REVIEW: This actually happens after the trigger...
                GC.InvokeCollection(currentThread);
            }
            return SegregatedFreeList.AllocateSlow(currentThread,
                                                   numBytes, alignment);
        }

        internal override int GetGeneration(Object obj) {
            return MinGeneration;
        }

        internal override int MaxGeneration {
            get { return (int)PageType.Owner0; }
        }

        internal override int MinGeneration {
            get { return (int)PageType.Owner0; }
        }

        internal override long TotalMemory {
            get {
                return (long)SegregatedFreeList.TotalBytes;
#if false
                UIntPtr pageCount = UIntPtr.Zero;
                for (UIntPtr i=UIntPtr.Zero; i<PageTable.pageTableCount; i++) {
                    if (PageTable.IsGcPage(i) && PageTable.IsMyPage(i)) {
                        pageCount++;
                    }
                }
                return (long) PageTable.RegionSize(pageCount);
#endif
            }
        }

        internal override void EnableHeap()
        {
        }

        internal override void DestructHeap() {
            base.DestructHeap();
            if (VTable.enableFinalGCTiming) {
                VTable.DebugPrint("total trace time = ");
                VTable.DebugPrint((long) traceTime);
                VTable.DebugPrint("\n");
                VTable.DebugPrint("total stw time = ");
                VTable.DebugPrint((long) (traceTime+sweepTime));
                VTable.DebugPrint("\n");
                VTable.DebugPrint("total sweep time = ");
                VTable.DebugPrint((long) sweepTime);
                VTable.DebugPrint("\n");
                VTable.DebugPrint("num traces = ");
                VTable.DebugPrint((long) numCollections);
                VTable.DebugPrint("\n");
                VTable.DebugPrint("num stw = ");
                VTable.DebugPrint((long) numCollections);
                VTable.DebugPrint("\n");
                VTable.DebugPrint("num sweeps = ");
                VTable.DebugPrint((long) numCollections);
                VTable.DebugPrint("\n");
            }
            if (GC.IsProfiling) {
                GcProfiler.NotifyShutdown();
            }
        }

        internal override void VerifyHeap(bool beforeCollection) {
            Verifier.segregatedFreeListVerifier.VerifyHeap();
        }

        internal override UIntPtr FindObjectAddr(UIntPtr interiorPtr) {
            return SegregatedFreeList.Find(interiorPtr);
        }

        internal override
        void VisitObjects(ObjectLayout.ObjectVisitor objectVisitor,
                          UIntPtr lowAddr, UIntPtr highAddr)
        {
            VTable.Assert(PageTable.PageAligned(lowAddr));
            VTable.Assert(PageTable.PageAligned(highAddr));
            UIntPtr lowPage = PageTable.Page(lowAddr);
            UIntPtr highPage = PageTable.Page(highAddr);
            SegregatedFreeList.VisitObjects(lowPage, highPage, objectVisitor);
        }

        internal override void NewThreadNotification(Thread newThread,
                                                     bool initial)
        {
            base.NewThreadNotification(newThread, initial);
            SegregatedFreeList.NewThreadNotification(newThread, initial);
        }

        internal override void DeadThreadNotification(Thread deadThread)
        {
            SegregatedFreeList.DeadThreadNotification(deadThread);
            base.DeadThreadNotification(deadThread);
        }

        // This is a quick-and-dirty check of whether something is an object.
        // All objects have a vtable. A VTable is an object that itself has a
        // vtable.  All VTable objects have the same vtable, which we rely
        // upon for this fast check.  This predicate will gracefully fail in
        // corrupted memory situations where a real type check will cause a
        // catastrophic failure.
        private static bool IsPossiblyObject(Object obj)
        {
            // First, check for a null reference
            if (obj == null) { return false; }
            // Second, check for a null vtable
            VTable vtable = obj.GcUnmarkedVTable;
            if (vtable == null) { return false; }
            // Third, check for a null vtable of the vtable
            VTable vtableVtable = vtable.GcUnmarkedVTable;
            if (vtableVtable == null) { return false; }
            // Finally, rely on the invariant that all vtables have the
            // same vtable.
            return (vtableVtable == vtableVtable.GcUnmarkedVTable);
        }

        // Routines for updating pointers to new locations of marked objects
        // No objects are resurrected using this mechanism
        // As this is mark sweep the value does not need to be updated.
        private class UpdateReferenceVisitor: NonNullReferenceVisitor
        {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                // Ignore pointers out of our memory area
                if (PageTable.IsForeignAddr(addr)) {
                    return;
                }
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsGcPage(pageType)) {
                    VTable.Assert((PageTable.IsNonGcPage(pageType) &&
                                   PageTable.IsMyPage(page)) ||
                                  PageTable.IsStackPage(pageType));
                    return;
                }
                VTable.Assert(PageTable.IsMyPage(page));
                Object obj = Magic.fromAddress(addr);
                VTable.Assert(IsPossiblyObject(obj), "Bad Object/VTable");
                if (obj.GcMark() == UIntPtr.Zero) {
                    // The object was not live
                    *loc = UIntPtr.Zero;
                }
            }
        }

        private class MarkReferenceVisitor : NonNullReferenceVisitor
        {

            private static UIntPtrStack workList;

            [Inline]
            protected override unsafe
            void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
            {
                if (*location!=UIntPtr.Zero) {
                    this.Visit(location);
                }
            }

            [Inline]
            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                // Ignore pointers out of our memory area
                if (PageTable.IsForeignAddr(addr)) {
                    return;
                }
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsGcPage(pageType)) {
                    VTable.Assert((PageTable.IsNonGcPage(pageType) &&
                                   PageTable.IsMyPage(page)) ||
                                  PageTable.IsStackPage(pageType));
                    return;
                }
                VTable.Assert(PageTable.IsMyPage(page));
                Object obj = Magic.fromAddress(addr);
                VTable.Assert(IsPossiblyObject(obj), "Bad object/vtable");
                if (obj.GcMark((UIntPtr)1)) {
                    // We changed the color of the object, so we
                    // have to mark the objects reachable from the fields
                    workList.Write(addr);
                }
            }

            internal void ProcessScheduledObjects() {
                while (!workList.IsEmpty) {
                    UIntPtr addr = workList.Read();
                    Object obj = Magic.fromAddress(addr);
                    this.VisitReferenceFields(obj);
                }
            }

            internal void Cleanup() {
                VTable.Assert(workList.IsEmpty);
                workList.Cleanup(true);
            }

            [Inline]
            internal override UIntPtr VisitReferenceFields(Object obj)
            {
                return this.VisitReferenceFields(Magic.addressOf(obj),
                                                 obj.GcUnmarkedVTable);
            }

            [ManualRefCounts]
            [Inline]
            internal override UIntPtr VisitReferenceFields(UIntPtr objectBase,
                                                           VTable vtable)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, objectBase);
                return VisitReferenceFieldsTemplate(ref objDesc);
            }
        }

        private class MarkAndProcessReferenceVisitor : NonNullReferenceVisitor
        {
            [Inline]
            internal unsafe override void Visit(UIntPtr *loc) {
                markReferenceVisitor.Visit(loc);
                markReferenceVisitor.ProcessScheduledObjects();
            }

            [Inline]
            internal override UIntPtr VisitReferenceFields(Object obj)
            {
                return this.VisitReferenceFields(Magic.addressOf(obj),
                                                 obj.GcUnmarkedVTable);
            }
        }

        private class ThreadMarkReferenceVisitor : NonNullReferenceVisitor
        {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                // Ignore pointers out of our memory area
                if (PageTable.IsForeignAddr(addr)) {
                    return;
                }
                UIntPtr page = PageTable.Page(addr);
                if (!PageTable.IsMyGcPage(page)) {
                    PageType pageType = PageTable.Type(page);
#if SINGULARITY_PROCESS
                    // We have to allow reference pointers to the
                    // ThreadContext, which lives in the kernel space.
                    VTable.Assert((PageTable.IsNonGcPage(pageType) &&
                                   PageTable.IsMyPage(page)) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType) ||
                                  (PageTable.IsGcPage(pageType) &&
                                   PageTable.IsKernelPage(page)));
#else
                    VTable.Assert((PageTable.IsNonGcPage(pageType) &&
                                   PageTable.IsMyPage(page))||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType));
#endif
                    return;
                }
                UIntPtr objectAddr = SegregatedFreeList.Find(addr);
                markAndProcessReferenceVisitor.Visit(&objectAddr);
            }

        }

        private class SweepVisitor : SegregatedFreeList.ObjectVisitor
        {

            private SegregatedFreeList.TempList tempList;

            internal override void VisitSmall(Object obj, UIntPtr memAddr)
            {
                if (!obj.GcMark(UIntPtr.Zero)) {
                    // We did not change the color of the object back
                    // to unmarked, so we are responsible for freeing it.
                    tempList.Add(memAddr);
                }
            }

            internal override void VisitSmallPageEnd() {
                SegregatedFreeList.FreeSmallList(ref tempList);
            }

            internal override UIntPtr VisitLarge(Object obj)
            {
                UIntPtr objectSize =
                    ObjectLayout.ObjectSize(Magic.addressOf(obj),
                                            obj.GcUnmarkedVTable);
                if (!obj.GcMark(UIntPtr.Zero)) {
                    // We did not change the color of the object back
                    // to unmarked, so we are responsible for freeing it.
                    SegregatedFreeList.FreeLarge(obj);
                }
                // REVIEW: Should we return a real size here?
                return objectSize;
            }

        }

        private class VerifyVisitor : ObjectLayout.ObjectVisitor {

            internal static VerifyVisitor visitor = new VerifyVisitor();

            internal override UIntPtr Visit(Object obj) {
                UIntPtr size;
                if (obj.GcMark() != UIntPtr.Zero) {
                    // The object has the mark color, so it should only
                    // reference other objects with the mark color.
                    size = VerifyMarkVisitor.visitor.VisitReferenceFields(obj);
                } else {
                    size = ObjectLayout.Sizeof(obj);
                }
                return size;
            }

        }

        private class VerifyMarkVisitor : NonNullReferenceVisitor {

            internal static VerifyMarkVisitor visitor =new VerifyMarkVisitor();

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                // Ignore pointers out of our memory area
                if (PageTable.IsForeignAddr(addr)) {
                    return;
                }
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (PageTable.IsGcPage(pageType)) {
                    Object obj = Magic.fromAddress(addr);
                    VTable.Assert(obj.GcMark() != UIntPtr.Zero);
                    VTable.Assert(PageTable.IsMyPage(page));
                }
            }

        }

    }

}
