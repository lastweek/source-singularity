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
    using Microsoft.Singularity.V1.Services; // Used for timing, only
#elif SINGULARITY_KERNEL
    using Microsoft.Singularity.Scheduling;
#endif
#else
    using Microsoft.Win32;
#endif

    using MarkingPhase = CMSMarking.MarkingPhase;

    /// <summary>
    /// This class implements a semi-concurrent version of MarkSweep.
    ///
    /// The goal for this collector is to perform as much of the processing
    /// as possible during mutator time, and also have a fixed upper bound
    /// on pause times.
    ///
    /// Additionally, the collector will be required in the future to
    /// communicate with the scheduler to prevent real time applications
    /// from competing with the GC.
    ///
    ///
    /// TODO: BUGBUG: NEED TO REPLICATE THE ALLOCATION COLOR LOGIC TO THE
    ///         INLINED ALLOCATION SEQUENCE.
    /// </summary>

    [NoCCtor]
    internal class ConcurrentMSCollector: BaseCollector
    {

        internal static bool UseAnyThrottle { get { return true; } }
        internal static bool UseYieldThrottle { get { return UseAnyThrottle && false; } }
        internal static bool UseSleepThrottle { get { return UseAnyThrottle && true; } }
        internal static bool UseOverlappingPhases { get { return false; } }
        internal static bool UseSTWTracingPhase { get { return GC.enableSTWRetrace; } }

        private static MarkingPhase CurrentMarkingPhase {
            [NoStackLinkCheck]
            get { return CMSMarking.CurrentMarkingPhase; }
        }

        internal enum ReclamationPhase {
            Dummy,              // Not used!
            Idle,               // No reclamation is in progress
            Reclaiming,         // Reclamation is in progress
        }

        internal static ReclamationPhase CurrentReclamationPhase;

#if SINGULARITY
        private static TimeSpan infiniteWait;
        private static TimeSpan minimumWait;
#else
        private static int infiniteWait;
        private static int minimumWait;
#endif

        /// <summary>
        /// Current mark state. This is flipped between collections.
        /// </summary>
        internal static UIntPtr markedColor {
            get { return CMSMarking.markedColor; }
            set { CMSMarking.markedColor = value; }
        }
        internal static UIntPtr unmarkedColor {
            get { return CMSMarking.unmarkedColor; }
            set { CMSMarking.unmarkedColor = value; }
        }
        internal static UIntPtr reclamationColor;

        private const uint markOne = 1U;
        private const uint markTwo = 2U;
        private const uint markThree = 3U;

#if SINGULARITY
        //
        // Note: This is updated to allow a large SINGULARITY build to advance
        //       through starting all CPU's before triggering the first collection.
        //
        //       If we enter the marking phase while starting the second processor
        //       it will crash while trying to setup its processor context to point
        //       to the current thread which must be valid for the marking list.
        //
        private const int  minimumCollectionTrigger = (1 << 25); // 32 MB
#else
        private const int  minimumCollectionTrigger = (1 << 24); // 16 MB
#endif
        private const int  maximumCollectionTrigger = (1 << 26); // 64 MB

        /// <summary>
        /// Amount of memory to allocate between collections.
        /// BUGBUG: This heuristic is not very good for CMS.
        /// </summary>
        private static UIntPtr collectionTrigger;

        internal static ConcurrentMSCollector instance;

        // Pointer visitors used for marking, etc
        internal static MarkReferenceVisitor markReferenceVisitor;
        internal static UpdateReferenceVisitor updateReferenceVisitor;
        internal static NonNullReferenceVisitor stackMarkReferenceVisitor;
        internal static NonNullReferenceVisitor stackMarkPinnedReferenceVisitor;
        internal static UnmarkVisitor unmarkVisitor;

        // Object visitors used for sweeping, etc
        internal static SweepVisitor sweepVisitor;

        // What to do when we encounter a partially free page
        internal static
        SegregatedFreeList.PartialFreePageVisitor partialFreePageVisitor;

        // Which threads are in what marking stage?
        private static UIntPtr[] threadColor;

        // Threads waiting for a particular collection to finish
        private static int[] waitingThreads;
        private static int firstWaitingThread;
        private const int waitingThreadsNullValue = -1;
        private const int waitingThreadsUnusedValue = -2;

        private const uint noColor = 0xffffffff;

        // The threads that performs the collection work.  MUST MAKE
        // SURE THAT THESE ARE PINNED IN COCO.  Currently that's OK
        // because all threads are pinned, for other reasons.
        [NoBarriers]
        private static Thread markThread;
        [NoBarriers]
        private static Thread workerThread1;
        [NoBarriers]
        private static Thread workerThread2;

        private static ulong totalTraceTime;
        private static ulong totalSTWTraceTime;
        private static ulong totalSweepTime;
        private static ulong numTraces;
        private static ulong numSTWTraces;
        private static ulong numSweeps;

        private static AutoResetEvent sweepPhaseMutex;

        // A trivial handshake executes no code other than clearing the
        // GCRequest.  A trivial handshake's only purpose is to indicicate
        // that the mutator is not in the middle of a "complex" GC operation
        // such as a barrier operation or unlinking an element from a list.
        internal static bool TrivialHandshake;

        internal static bool IncludeMUWInHandshake;

        /// <summary>
        /// Does this collector compute a root set with threads running?
        /// </summary>
        internal override bool IsOnTheFlyCollector {
            get {
                return true;
            }
        }

        [NoBarriers]
        [PreInitRefCounts]
        internal static void InitializeAllButVisitors()
        {
            SegregatedFreeList.Initialize();
            unmarkedColor = (UIntPtr) markOne;
            markedColor = (UIntPtr) markTwo;
            reclamationColor = (UIntPtr) markThree;
            // threadColor = new UIntPtr[Thread.maxThreads];
            threadColor = (UIntPtr[])
                BootstrapMemory.Allocate(typeof(UIntPtr[]), Thread.maxThreads);
            for (int i = 0; i < threadColor.Length; i++) {
                threadColor[i] = (UIntPtr) noColor;
            }
            TrivialHandshake = true;
            collectionTrigger = (UIntPtr) minimumCollectionTrigger;
            IncludeMUWInHandshake = true;
            CMSMarking.currentMarkingPhase = (int) MarkingPhase.Idle;
            CurrentReclamationPhase = ReclamationPhase.Idle;
#if SINGULARITY
            infiniteWait = TimeSpan.Infinite;
            minimumWait = TimeSpan.FromMilliseconds(1);
#else
            infiniteWait = Timeout.Infinite;
            minimumWait = 1;
#endif
        }

        /// <summary>
        /// Initialise the collector and allow allocations to commence.
        /// </summary>
        [PreInitRefCounts]
        public static void Initialize() {
            InitializeAllButVisitors();
            // instance = new ConcurrentMSCollector();
            ConcurrentMSCollector.instance = (ConcurrentMSCollector)
                BootstrapMemory.Allocate(typeof(ConcurrentMSCollector));
            // markReferenceVisitor = new MarkReferenceVisitor();
            markReferenceVisitor = (MarkReferenceVisitor)
                BootstrapMemory.Allocate(typeof(MarkReferenceVisitor));
            // updateReferenceVisitor = new UpdateReferenceVisitor();
            updateReferenceVisitor = (UpdateReferenceVisitor)
                BootstrapMemory.Allocate(typeof(UpdateReferenceVisitor));
            // stackMarkReferenceVisitor = new StackMarkReferenceVisitor();
            stackMarkReferenceVisitor = (StackMarkReferenceVisitor)
                BootstrapMemory.Allocate(typeof(StackMarkReferenceVisitor));
            stackMarkPinnedReferenceVisitor = stackMarkReferenceVisitor;
            unmarkVisitor = (UnmarkVisitor)
                BootstrapMemory.Allocate(typeof(UnmarkVisitor));
            // sweepVisitor = new SweepVisitor();
            sweepVisitor = (SweepVisitor)
                BootstrapMemory.Allocate(typeof(SweepVisitor));
            // set the null partial free page visitor
            partialFreePageVisitor =
                SegregatedFreeList.nullPartialFreePageVisitor;
        }

        internal override void Collect(Thread currentThread, int generation)
        {
            try {
                if (!GC.IsUserCollectionRequest(generation) &&
                    Transitions.HasGCRequest(currentThread.threadIndex) &&
                    TrivialHandshake) {
                    // Someone asked for a handshake, and it is a trivial
                    // handshake, so there is no need to go through
                    // the overhead of saving and restoring the callee-save
                    // registers in CollectBodyTransition.
                    Transitions.ClearGCRequest(currentThread.threadIndex);
                    // BUGBUG: consider restoring the following
                    // markThread.SignalEvent();
                } else {
                    GC.CollectTransition(currentThread, generation);
                }
            } catch (Exception e) {
                VTable.DebugPrint("Garbage collection failed with exception");
                VTable.DebugPrint(e.GetType().Name);
                VTable.DebugBreak();
            }
        }

        /// <summary>
        /// Perform a collection. Depending on the current phase of collection
        /// this method will either:
        ///
        ///     1. Start a new collection and schedule the mark thread
        ///     2. Notice that a collection is underway and exit
        ///     3. Clean up after a collection
        ///
        /// BUGBUG: The interaction between the collector needs work!
        /// </summary>
        internal override void CollectStoppable(int currentThreadIndex,
                                                int generation)
        {
            if (!GC.IsUserCollectionRequest(generation) &&
                Transitions.HasGCRequest(currentThreadIndex)) {
                // We are GC safe, so we may do this
                Transitions.TakeDormantControlNoGC(currentThreadIndex);
                if (Transitions.TakeGCControl(currentThreadIndex)) {
                    if (UseSTWTracingPhase &&
                        CurrentMarkingPhase == MarkingPhase.StopTheWorld) {
                        Thread.SignalGCEvent(markThread.threadIndex);
                    } else {
                        MutatorHandshake(currentThreadIndex);
                        Transitions.ReleaseGCControl(currentThreadIndex);
                        // BUGBUG: consider restoring the following
                        // markThread.SignalEvent();
                    }
                }
                Transitions.TakeMutatorControlNoGC(currentThreadIndex);
            } else if (GC.IsRealCollectionRequest(generation)) {
                if (generation >= 0) {
                    AddThreadToWaitList(currentThreadIndex);
                }
                AddCollectionRequest();
                if (generation >= 0) {
                    Thread currentThread =
                        Thread.threadTable[currentThreadIndex];
                    while (ThreadIsWaiting(currentThreadIndex)) {
                        // NOTE: if there was a GC request and this was a
                        // user-requested collection, then the stack scanning
                        // will happen in here.
                        // NOTE: there is no code in this loop that could
                        // cause a signal on an event to be consumed.
                        currentThread.WaitForEvent(infiniteWait);
                    }
                }
            }
        }

        internal override void CheckForNeededGCWork(Thread currentThread) {
            if (Transitions.HasGCRequest(currentThread.threadIndex)) {
                GC.InvokeCollection(currentThread);
            }
        }

        internal static void CollectorHandshake(Thread collectorThread)
        {
            Transitions.MakeGCRequests(collectorThread.threadIndex);
            // Handshake with all the (other) threads.
            for(int i=0; i < Thread.threadTable.Length; i++) {
#if SINGULARITY_KERNEL
                if (Scheduler.IsIdleThread(i)) {
                    continue;
                }
#endif
                // Is there an unscanned thread here?
                while (Transitions.HasGCRequest(i)) {
                    if (Transitions.TakeGCControl(i)) {
                        MutatorHandshake(i);
                        Transitions.ReleaseGCControl(i);
                    } else if (Thread.threadTable[i] == null) {
                        // The thread must have terminated but the
                        // state hasn't yet changed to DormantState.
                        break;
                    } else {
                        // NOTE: there is no code in this loop that could
                        // cause a signal on an event to be consumed without
                        // being putting back.
                        collectorThread.WaitForEvent(minimumWait);
                    }
                }
            }

            if (ConcurrentMSCollector.IncludeMUWInHandshake &&
                !ConcurrentMSCollector.TrivialHandshake &&
                !UseSTWTracingPhase) {
                MultiUseWord.CollectFromPreviousCollections(false);
            }
        }

        private static void MutatorHandshake(int threadIndex)
        {
#if SINGULARITY_KERNEL
            Microsoft.Singularity.Processor currentProcessor =
                Microsoft.Singularity.Processor.CurrentProcessor;
            if (currentProcessor.InInterruptContext) {
                Tracing.Log(Tracing.Fatal, "Attempt to perform a collector handshake from an interrupt context!");
                VTable.DebugPrint("Attempt to perform a collector handshake from withing an interrupt context");
                VTable.DebugBreak();
            }
#endif
            if (!ConcurrentMSCollector.TrivialHandshake) {
                Thread thread = Thread.threadTable[threadIndex];
                if (thread != null) {
                    ScanThreadRoots(thread);
                    if (IncludeMUWInHandshake && !UseSTWTracingPhase) {
                        MultiUseWord.CollectFromThread(thread);
                    }
                }
            }
        }

        private static void ScanThreadRoots(Thread thread) {
            long start = CollectorStatistics.PerformanceCounter;
            CollectorStatistics.Event(GCEvent.StackScanStart,
                                      thread.threadIndex);
            CallStack.ScanStack(thread, stackMarkReferenceVisitor,
                                stackMarkPinnedReferenceVisitor);
            threadColor[thread.threadIndex] = markedColor;
            // Report the pause
            long pause =
                CollectorStatistics.PerformanceCounter - start;
            CollectorStatistics.Event(GCEvent.StackScanComplete,
                                      pause);
        }

        internal static bool terminateCollectorThreads;

        // REVIEW: merge this with terminateCollectorThreads, maybe
        internal static bool killCollectorThreads; /* non-Singularity thread killage */

        internal static void TraceThreadNotification() {
            terminateCollectorThreads = true;
            GC.Collect();
        }

        /// <summary>
        /// This method is run by the collector threads.
        /// </summary>
        private static void CollectionTask() {
            try {
                CollectionLoop();
            } catch (Exception e) {
                VTable.DebugPrint("Collection task failed with exception ");
                VTable.DebugPrint(e.GetType().Name);
                VTable.DebugBreak();
            }
        }

        private static void CollectionLoop() {
#if !SINGULARITY
            if (fDebug) {
                VTable.DebugPrint("cms thread = ");
                VTable.DebugPrint((ulong)Win32Native.GetCurrentThreadId());
                VTable.DebugPrint("\n");
            }
#endif

            Thread currentThread = Thread.CurrentThread;
#if SINGULARITY_PROCESS
            currentThread.MakeServiceThread(new Thread.StopServiceNotice(TraceThreadNotification));
#endif
            while (!terminateCollectorThreads && !killCollectorThreads) {
                // Wait to be told to start working.
                while (!TakeChargeOfTraceRequest() && !killCollectorThreads) {
                    // NOTE: there is no code in this loop that could
                    // cause a signal on an event to be consumed.
                    currentThread.WaitForEvent(infiniteWait);
                }
                if (killCollectorThreads) {
                    break;
                }
                StartGCCycle();
                instance.PreTraceHook();
#if SINGULARITY
                DebugStub.WriteLine("~~~~~ Start Concurrent Marking  [data={0:x8}, pid={1:x3}]",
                                    __arglist(SegregatedFreeList.TotalBytes,
                                              PageTable.processTag >> 16));
#endif
                if (fDebug) {
                    VTable.DebugPrint("~~~~~ Start Concurrent Marking\n");
                }
                int startTicks = Environment.TickCount;
                if (GC.IsProfiling) {
                    GcProfiler.NotifyPreGC(instance.MinGeneration);
                }
                markThread = currentThread;
                advanceMarkColors();
                MarkReferenceVisitor.markThread = currentThread;
                // Construct the root set.
                CollectorStatistics.Event(GCEvent.ComputeRootSet);
                StartRootMarkingPhase();
                // Start the process of recycling pages
                partialFreePageVisitor.Start();
                SegregatedFreeList
                    .RecycleGlobalPagesPhase1(partialFreePageVisitor);
                // One handshake to ensure that everyone starts snooping
                CollectorHandshake(currentThread);
                // Complete the process of recycling pages
                SegregatedFreeList
                    .RecycleGlobalPagesPhase2(partialFreePageVisitor);
                partialFreePageVisitor.Finish();
                // Another handshake to ensure that all updates started by
                // other threads prior to their handshake are done and
                // snooping will affect all new updates.
                CollectorHandshake(currentThread);
                // A third handshake to get the threads to process their
                // own roots.  The collector thread needs to scan its
                // roots, too.
                ConcurrentMSCollector.TrivialHandshake = false;
                CollectorHandshake(currentThread);
                // In order to scan the call stack of the current thread,
                // we need a TransitionRecord for the thread.  At this
                // point we don't have one, so we have to go through
                // CollectBodyTransition to get one.
                Transitions.MakeGCRequest(currentThread.threadIndex);
                GC.InvokeCollection(currentThread);
                ConcurrentMSCollector.TrivialHandshake = true;
                Finalizer.PrepareCollectFinalizers();
                Thread.VisitBootstrapData(markReferenceVisitor);
#if SINGULARITY_KERNEL
                Kernel.VisitSpecialData(markReferenceVisitor);
#endif
                MultiUseWord.VisitStrongRefs(markReferenceVisitor,
                                             false /* Don't use shadows */);
#if !VC
                TryAllManager.VisitStrongRefs(markReferenceVisitor);
#endif
                instance.PostRootScanHook();
                StaticData.ScanStaticData(markReferenceVisitor);
                CollectorStatistics.Event(GCEvent.RootSetComputed);
                int waitingThreadList = StealWaitingThreadsList();
                // We are now in the concurrent tracing phase.
                ResetCollectorRequests();
                StartTracingPhase();
                markReferenceVisitor.Init();
                CollectorStatistics.Event(GCEvent.TraceStart,
                                          ReservedMemory);
                // Trace live objects from the root set.
                markReferenceVisitor.ProcessGrayObjects();
                if (killCollectorThreads) {
                    break;
                }
                // If we want to use a STW phase to redo the tracing (for
                // measurement purposes, most likely), now is the time to
                // do so.
                if (UseSTWTracingPhase) {
                    int preSTWTrace = Environment.TickCount;
                    StartSTWPhase();
                    bool oldTrivialHandshake = TrivialHandshake;
                    TrivialHandshake = false;
                    BaseCollector.AllThreadRendezvous(markThread.threadIndex);
                    TrivialHandshake = oldTrivialHandshake;
                    STWInitialize();
                    STWScanStacks(stackMarkReferenceVisitor,
                                  stackMarkPinnedReferenceVisitor);
                    Finalizer.PrepareCollectFinalizers();
                    Thread.VisitBootstrapData(markReferenceVisitor);
#if SINGULARITY_KERNEL
                    Kernel.VisitSpecialData(markReferenceVisitor);
#endif
                    MultiUseWord.VisitStrongRefs(markReferenceVisitor,
                                                 false /* Don't use shadows */);
#if !VC
                    TryAllManager.VisitStrongRefs(markReferenceVisitor);
#endif
                    StaticData.ScanStaticData(markReferenceVisitor);
                    markReferenceVisitor.Init();
                    markReferenceVisitor.ProcessGrayObjects();
                    BaseCollector.AllThreadRelease(markThread.threadIndex);
                    FinishSTWPhase();
                    int postSTWTrace = Environment.TickCount;
                    totalSTWTraceTime += (ulong)(postSTWTrace-preSTWTrace);
                    numSTWTraces ++;
                }
                CollectorStatistics.Event(GCEvent.TraceSpecial);
                // Mark weak references that do not track resurrection as dead.
                WeakReference.Process(updateReferenceVisitor, true, true);
                // Resurrect any finalization candidates.
                Finalizer.ResurrectCandidates(updateReferenceVisitor,
                                              markReferenceVisitor, true);
                // Complete closure from finalized objects.
                markReferenceVisitor.ProcessGrayObjects();
                if (killCollectorThreads) {
                    break;
                }
                // Mark appropriate weak references as dead
                WeakReference.Process(updateReferenceVisitor, true, false);
                MultiUseWord.VisitWeakRefs(updateReferenceVisitor,
                                           false /* Don't use shadows */);
#if !VC
                TryAllManager.VisitWeakRefs(updateReferenceVisitor);
#endif
                MultiUseWord.PostGCHook();
                // Reset thread queues.  They should all be empty.
                markReferenceVisitor.Cleanup();
                int middleTicks = Environment.TickCount;
                totalTraceTime += (ulong)(middleTicks - startTicks);
                numTraces ++;
#if SINGULARITY
                DebugStub.WriteLine("~~~~~ Finish Concurrent Marking [data={0:x8}, pid={1:x3} ms={2:d6}]",
                                    __arglist(SegregatedFreeList.TotalBytes,
                                              PageTable.processTag >> 16,
                                              middleTicks - startTicks));
#endif
                if (fDebug) {
                    VTable.DebugPrint("~~~~~ Finish Concurrent Marking\n");
                }
                instance.PostTraceHook();
                markThread = nextWorkerThread(currentThread);
                sweepPhaseMutex.WaitOne();
                try {
                    reclamationColor = unmarkedColor;
                    FinishTracingPhase();
                    SatisfyCollectorRequest(); // May start another trace phase
                    // Sweep garbage objects
                    StartReclamationPhase();
#if SINGULARITY
                    DebugStub.WriteLine("~~~~~ Start Concurrent Reclamation  [data={0:x8}, pid={1:x3}]",
                                        __arglist(SegregatedFreeList.TotalBytes,
                                                  PageTable.processTag >> 16));
#endif
                    if (fDebug) {
                        VTable.DebugPrint("~~~~~ Start Concurrent Reclamation\n");
                    }
                    CollectorStatistics.Event(GCEvent.SweepStart,
                                              ReservedMemory);
                    instance.PreSweepHook();
                    Sweep();
                    if (killCollectorThreads) {
                        break;
                    }
                    instance.PostSweepHook();
                    // Clean up after the collection
                    CollectorStatistics.Event(GCEvent.SweepSpecial,
                                              ReservedMemory);
                    Finalizer.ReleaseCollectFinalizers();
                    if (GC.IsProfiling) {
                        // Allocations may occur inside the PostGCHook.  Hopefully a
                        // sufficiently limited quantity that we don't recursively
                        // trigger a GC.
                        GcProfiler.NotifyPostGC(ProfileRoots, ProfileObjects);
                    }
                    CollectorStatistics.Event(GCEvent.SweepPreCommit,
                                              ReservedMemory);
                    // Commit accounting changes
                    CommitSweep();
                    CollectorStatistics.Event(GCEvent.CollectionComplete,
                                              ReservedMemory);
                    // Determine a new collection trigger
                    UIntPtr testTrigger = (UIntPtr) ReservedMemory >> 2;
                    UIntPtr minTrigger = (UIntPtr) minimumCollectionTrigger;
                    UIntPtr maxTrigger = (UIntPtr) maximumCollectionTrigger;
                    collectionTrigger =
                        (testTrigger > minTrigger) ?
                        (testTrigger < maxTrigger ?
                         testTrigger : maxTrigger) : minTrigger;
                    // Finish up and wake up any GC requesting threads.
                    SignalWaitingThreads(waitingThreadList);
                    FinishReclamationPhase();
                } finally {
                    sweepPhaseMutex.Set();
                }
                instance.PostReclamationHook();
                int endTicks = Environment.TickCount;
                totalSweepTime += (ulong)(endTicks - middleTicks);
                numSweeps ++;
#if SINGULARITY
                DebugStub.WriteLine("~~~~~ Finish Concurrent Reclamation [data={0:x8}, pid={1:x3} ms={2:d6}]",
                                    __arglist(ReservedMemory,
                                              PageTable.processTag >> 16,
                                              endTicks - middleTicks));
#endif
                if (fDebug) {
                    VTable.DebugPrint("~~~~~ Finish Concurrent Reclamation\n");
                }
                if (VTable.enableDumpMemStats) {
                    VTable.DebugPrint("Heap mem usage: {0:x8}\n",
                                      __arglist(ReservedMemory));
                }
            }
        }

        private static void STWInitialize()
        {
            for (int i = 0; i < Thread.threadTable.Length; i++) {
                Thread t = Thread.threadTable[i];
                if (t != null) {
                    ThreadHeaderQueue.Reset(t);
                }
            }
            SegregatedFreeList.VisitAllObjects(unmarkVisitor);
        }

        private static
        void STWScanStacks(NonNullReferenceVisitor VisitThreadReference,
                           NonNullReferenceVisitor VisitPinnedReference)
        {
            for (int i = 0; i < Thread.threadTable.Length; i++) {
                Thread t = Thread.threadTable[i];
                if (t != null) {
                    CallStack.ScanStack(t, VisitThreadReference,
                                        VisitPinnedReference);
                    if (IncludeMUWInHandshake) {
                        MultiUseWord.CollectFromThread(t);
                    }
                }
            }
            if (IncludeMUWInHandshake) {
                MultiUseWord.CollectFromPreviousCollections(false);
            }
        }

        internal virtual void PreTraceHook()
        {
        }

        internal virtual void PostRootScanHook()
        {
        }

        internal virtual void PostTraceHook()
        {
        }

        internal virtual void PostReclamationHook()
        {
        }

        internal virtual void PreSweepHook()
        {
        }

        internal virtual void PostSweepHook()
        {
        }

        /// <summary>
        /// Allocate memory for a new object, potentially triggering a
        /// collection.
        /// </summary>
        [Inline]
        internal override UIntPtr AllocateObjectMemory(UIntPtr numBytes,
                                                       uint alignment,
                                                       Thread currentThread)
        {
            UIntPtr resultAddr =
                SegregatedFreeList.AllocateFast(currentThread,
                                                numBytes, alignment);
            if (resultAddr == UIntPtr.Zero) {
                resultAddr = AllocateObjectMemorySlow(numBytes, alignment,
                                                      currentThread);
            }
            return resultAddr;
        }

        [NoInline]
        internal virtual UIntPtr AllocateObjectMemorySlow(UIntPtr numBytes,
                                                          uint alignment,
                                                          Thread currentThread)
        {
            if (Transitions.HasGCRequest(currentThread.threadIndex)) {
                GC.InvokeCollection(currentThread);
            } else if (NewBytesSinceGCExceeds(collectionTrigger) &&
                       GC.allocationGCInhibitCount == 0) {
                if (CurrentMarkingPhase == MarkingPhase.Idle) {
                    GC.InvokeCollection(currentThread);
                } else if (currentThread!=workerThread1 &&
                           currentThread!=workerThread2 &&
                           NewBytesSinceGCExceeds(collectionTrigger<<1)) {
                    // Slow down the allocating thread a bit
                    if (UseSleepThrottle &&
                        (NewBytesSinceGCExceeds((collectionTrigger<<3)+
                                                (collectionTrigger<<2)) ||
                         TotalMemory > (1<<30)+(1<<29))) {
                        // Context switches didn't help, so let's try
                        // suspending ourselves for a bit.
                        Thread.Sleep(1);
                    } else if (UseYieldThrottle) {
                        // If there are more threads than processors,
                        // forcing a context switch should slow down
                        // the mutator thread.
                        Thread.Yield();
                    }
                }
            }
            return SegregatedFreeList.AllocateSlow(currentThread,
                                                   numBytes, alignment);
        }

        [NoInline]
        [CalledRarely]
        protected void MarkOnAlloc(Thread currentThread,
                                   Object obj)
        {
            ThreadHeaderQueue.PushPrivateObject(currentThread,
                                                obj, markedColor);
        }

        [Inline]
        protected override void CreateObject(Object obj, VTable vtable,
                                             Thread currentThread)
        {
            // We expect the color to be assigned before the vtable field
            // is initialized.  This ensures that every real object has a
            // valid color.
            UIntPtr markBits = threadColor[currentThread.threadIndex];
            ThreadHeaderQueue.SetGcMark(obj, markBits);
            // The vtable field must be initialized before the object is
            // inserted into a list of objects to be scanned.
            base.CreateObject(obj, vtable, currentThread);
            // If necessary, mark the object for future scanning
            if (CurrentMarkingPhase == MarkingPhase.ComputingRoots) {
                MarkOnAlloc(currentThread, obj);
            }

            ProfileAllocation(obj);
        }

        /// <summary>
        /// Return the generation for an object. We only have one
        /// generation, so we always return generation zero.
        /// </summary>
        internal override int GetGeneration(Object obj) {
            Verifier.genericObjectVisitor.Visit(obj);
            return MinGeneration;
        }

        /// <summary>
        /// The maximum generation. For MarkSweep this is generation zero.
        /// </summary>
        internal override int MaxGeneration {
            get { return (int)PageType.Owner0; }
        }

        /// <summary>
        /// The minimum generation. For MarkSweep this is generation zero.
        /// </summary>
        internal override int MinGeneration {
            get { return (int)PageType.Owner0; }
        }

        /// <summary>
        /// This returns the total amount of memory that is allocated within
        /// the collected heap.
        /// </summary>
        internal override long TotalMemory {
            get {
                return ReservedMemory;
            }
        }

        private static long ReservedMemory {
            get {
                return (long)(SegregatedFreeList.TotalPages*PageTable.PageSize);
            }
        }

        internal static int GetEnvironmentValue(String name, int defaultValue)
        {
            String valueString = null;
#if !SINGULARITY
            valueString = Environment.GetEnvironmentVariable(name);
#endif
            if (valueString == null) {
                return defaultValue;
            } else {
                return Int32.Parse(valueString);
            }
        }

        internal override void EnableHeap() {
            // waitingThreads = new int[Thread.maxThreads]
            waitingThreads = new int[Thread.maxThreads];
            for (int i = 0; i < waitingThreads.Length; i++) {
                waitingThreads[i] = waitingThreadsUnusedValue;
            }
            firstWaitingThread = -1;
            // Construct the collector thread(s)
#if SINGULARITY_KERNEL
            workerThread1 =
                Thread.CreateThread(Process.kernelProcess,
                                    new ThreadStart(CollectionTask));
            if (UseOverlappingPhases) {
                workerThread2 =
                    Thread.CreateThread(Process.kernelProcess,
                                        new ThreadStart(CollectionTask));
            }
#else
            workerThread1 = new Thread(new ThreadStart(CollectionTask));
            if (UseOverlappingPhases) {
                workerThread2 = new Thread(new ThreadStart(CollectionTask));
            }
#endif
            workerThread1.Start();
            if (UseOverlappingPhases) {
                workerThread2.Start();
            }
            markThread = workerThread1;
            sweepPhaseMutex = new AutoResetEvent(true);
        }

        internal override void Shutdown()
        {
            if (GC.IsProfiling) {
                GcProfiler.NotifyShutdown();
            }
            killCollectorThreads = true;
            workerThread1.SignalEvent();
            if (workerThread2!=null) {
                workerThread2.SignalEvent();
            }
            workerThread1.Join();
            if (workerThread2!=null) {
                workerThread2.Join();
            }
        }

        /// <summary>
        /// Destroy the heap. Nothing to do here.
        /// </summary>
        internal override void DestructHeap()
        {
            base.DestructHeap();
            if (VTable.enableFinalGCTiming) {
                VTable.DebugPrint("total trace time = ");
                VTable.DebugPrint((long) totalTraceTime);
                VTable.DebugPrint("\n");
                VTable.DebugPrint("total sweep time = ");
                VTable.DebugPrint((long) totalSweepTime);
                VTable.DebugPrint("\n");
                VTable.DebugPrint("num traces = ");
                VTable.DebugPrint((long) numTraces);
                VTable.DebugPrint("\n");
                VTable.DebugPrint("num sweeps = ");
                VTable.DebugPrint((long) numSweeps);
                VTable.DebugPrint("\n");
            }
        }

        /// <summary>
        /// Verify the heap.
        /// </summary>
        internal override void VerifyHeap(bool beforeCollection) {
            SegregatedFreeList.VisitAllObjects(VerifyVisitor.visitor);
            Verifier.segregatedFreeListVerifier.VerifyHeap();
        }

        private static char ToHexDigit(int number, int position) {
            int digit = (number >> (position * 4)) & 0xf;
            return (char) (digit + ((digit <= 9) ? '0' : ('A' - 10)));
        }
        private static int flag; // = 0;
        private static void DebugTrace(String text, int threadIndex) {
            while (Interlocked.CompareExchange(ref flag, 1, 0) != 0) { }
            VTable.DebugPrint(text+" "+
                              ToHexDigit(threadIndex, 2)+
                              ToHexDigit(threadIndex, 1)+
                              ToHexDigit(threadIndex, 0)+
                              "\n");
            Interlocked.Exchange(ref flag, 0);
        }

        /// Routines to keep track of requests for collection work

        private static int collectorStack; // 0:idle, 1:work, 2+:work+pending

        internal static void AddCollectionRequest() {
            int stackHeight = Interlocked.Increment(ref collectorStack);
            VTable.Assert(stackHeight > 0);
            if (stackHeight == 1) {
                MakeTraceRequest();
            }
        }

        private static void ResetCollectorRequests() {
            Interlocked.Exchange(ref collectorStack, 1);
        }

        private static void SatisfyCollectorRequest() {
            int stackHeight = Interlocked.Decrement(ref collectorStack);
            VTable.Assert(stackHeight >= 0);
            if (stackHeight > 0 ) {
                MakeTraceRequest();
            }
        }

        /// Routines to keep track of threads that must be notified when
        /// a collection has been completed.

        private static void AddThreadToWaitList(int threadIndex) {
            int listHead = firstWaitingThread;
            waitingThreads[threadIndex] = listHead;
            while (Interlocked.CompareExchange(ref firstWaitingThread,
                                               threadIndex, listHead) !=
                   listHead) {
                listHead = firstWaitingThread;
                waitingThreads[threadIndex] = listHead;
            }
        }

        private static bool ThreadIsWaiting(int threadIndex) {
            return (waitingThreads[threadIndex] != waitingThreadsUnusedValue);
        }

        private static int StealWaitingThreadsList() {
            return Interlocked.Exchange(ref firstWaitingThread,
                                        waitingThreadsNullValue);
        }

        private static void SignalWaitingThreads(int listHead) {
            while (listHead != waitingThreadsNullValue) {
                int threadIndex = listHead;
                listHead = waitingThreads[threadIndex];
                waitingThreads[threadIndex] = waitingThreadsUnusedValue;
                Thread.threadTable[threadIndex].SignalEvent();
            }
        }

        /// Routines to control the commencement of the tracing phase

        private static void MakeTraceRequest() {
            MarkingPhase oldPhase = (MarkingPhase)
                Interlocked.Exchange(ref CMSMarking.currentMarkingPhase,
                                     (int) MarkingPhase.Requested);
            VTable.Assert(oldPhase == MarkingPhase.Idle);
            markThread.SignalEvent();
        }

        private static bool TakeChargeOfTraceRequest() {
            MarkingPhase oldPhase = (MarkingPhase)
                Interlocked.CompareExchange(ref CMSMarking.currentMarkingPhase,
                                            (int) MarkingPhase.Preparing,
                                            (int) MarkingPhase.Requested);
            return (oldPhase == MarkingPhase.Requested);
        }

        // Routines to keep track of what phases the collector threads are in.

        private static void StartRootMarkingPhase() {
            CMSMarking.referenceCheckIsFast = false;
            MarkingPhase oldPhase = (MarkingPhase)
                Interlocked.Exchange(ref CMSMarking.currentMarkingPhase,
                                     (int) MarkingPhase.ComputingRoots);
            VTable.Assert(oldPhase == MarkingPhase.Preparing);
        }

        private static void StartTracingPhase() {
            MarkingPhase oldPhase = (MarkingPhase)
                Interlocked.Exchange(ref CMSMarking.currentMarkingPhase,
                                     (int) MarkingPhase.Tracing);
            VTable.Assert(oldPhase == MarkingPhase.ComputingRoots);
        }

        private static void StartSTWPhase() {
            MarkingPhase oldPhase = (MarkingPhase)
                Interlocked.Exchange(ref CMSMarking.currentMarkingPhase,
                                     (int) MarkingPhase.StopTheWorld);
            VTable.Assert(oldPhase == MarkingPhase.Tracing);
        }

        private static void FinishSTWPhase() {
            MarkingPhase oldPhase = (MarkingPhase)
                Interlocked.Exchange(ref CMSMarking.currentMarkingPhase,
                                     (int) MarkingPhase.Tracing);
            VTable.Assert(oldPhase == MarkingPhase.StopTheWorld);
        }

        private static void FinishTracingPhase() {
            MarkingPhase oldPhase = (MarkingPhase)
                Interlocked.Exchange(ref CMSMarking.currentMarkingPhase,
                                     (int) MarkingPhase.Idle);
            VTable.Assert(oldPhase == MarkingPhase.Tracing);
            CMSMarking.referenceCheckIsFast = true;
        }

        private static void StartReclamationPhase() {
            CurrentReclamationPhase = ReclamationPhase.Reclaiming;
        }

        private static void FinishReclamationPhase() {
            CurrentReclamationPhase = ReclamationPhase.Idle;
        }

        // Routines to manage marking colors

        private static void advanceMarkColors()
        {
            unmarkedColor = markedColor;
            markedColor = nextColor(markedColor);
        }

        private static UIntPtr nextColor(UIntPtr originalColor)
        {
            switch ((uint) originalColor) {
              case markOne: return (UIntPtr) markTwo;
              case markTwo: return (UIntPtr) markThree;
              case markThree: return (UIntPtr) markOne;
              default: throw new Exception("nextColor failure!");
            }
        }

        private static Thread nextWorkerThread(Thread currentThread) {
            if (UseOverlappingPhases) {
                return ((currentThread == workerThread1) ?
                        workerThread2 :
                        workerThread1);
            } else {
                return currentThread;
            }
        }

        /// <summary>
        /// Walk the allocation structures and reclaim any free cells.
        /// </summary>
        [NoInline]
        private static void Sweep() {
            SegregatedFreeList.VisitAllObjects(sweepVisitor);
        }

        /// <summary>
        /// Update alloc heap to account for data just freed.
        /// </summary>
        private static void CommitSweep() {
            SegregatedFreeList.CommitFreedData();
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
            VTable vtable = obj.vtable;
            if (vtable == null) { return false; }
            // Third, check for a null vtable of the vtable
            VTable vtableVtable = vtable.vtable;
            if (vtableVtable == null) { return false; }
            // Finally, rely on the invariant that all vtables have the
            // same vtable.
            return (vtableVtable == vtableVtable.vtable);
        }

        /// <summary>
        /// Routines for updating pointers to new locations of marked objects
        /// No objects are resurrected using this mechanism.
        /// As this is mark sweep the value does not need to be updated.
        /// </summary>
        internal class UpdateReferenceVisitor: MutableReferenceVisitor
        {

            internal virtual UIntPtr ForwardIfNecessary(UIntPtr addr)
            {
                return addr;
            }

            internal unsafe override void Visit(UIntPtr *loc) {
                while (true) {
                    UIntPtr foundAddr = *loc;
                    // Ignore pointers out of our memory area
                    if (foundAddr == UIntPtr.Zero ||
                        PageTable.IsForeignAddr(foundAddr)) {
                        return;
                    }
                    UIntPtr page = PageTable.Page(foundAddr);
                    PageType pageType = PageTable.Type(page);
                    if (!PageTable.IsGcPage(pageType)) {
                        VTable.Assert((PageTable.IsNonGcPage(pageType) &&
                                       PageTable.IsMyPage(page)) ||
                                      PageTable.IsStackPage(pageType),
                                      "update.visit invalid page");
                        return;
                    }
                    VTable.Assert(PageTable.IsMyPage(page));
                    UIntPtr forwardedAddr = ForwardIfNecessary(foundAddr);
                    Object obj = Magic.fromAddress(forwardedAddr);
                    VTable.Assert(IsPossiblyObject(obj),
                                  "update visit: bad object/vtable");
                    if (ThreadHeaderQueue.GcMark(obj) == unmarkedColor) {
                        // The object is not live
                        *loc = UIntPtr.Zero;
                        return;
                    }
                    // The object is alive, install forwarded value,
                    // if necessary.
                    if (foundAddr == forwardedAddr ||
                        (Interlocked.CompareExchange(loc, forwardedAddr,
                                                     foundAddr)
                         == foundAddr)) {
                        return;
                    }
                }
            }
        }

        /// <summary>
        /// Select the generation to collect (always generation 0)
        /// </summary>
        internal override int CollectionGeneration(int genRequest) {
            return MinGeneration;
        }

        /// <summary>
        /// This visitor is the core of the tracing functionality.
        /// It builds up a buffer of references (the root set), and
        /// then at a later point the tracing thread processes these
        /// buffers.
        /// </summary>
        internal class MarkReferenceVisitor : MutableReferenceVisitor
        {
            [NoBarriers]
            internal static Thread markThread;

            [Inline]
            protected override unsafe
            void Filter(UIntPtr *location, ref ObjectDescriptor objDesc)
            {
                this.Visit(location);
            }

            [Inline]
            internal override unsafe void Visit(UIntPtr *location)
            {
                this.VisitValueMaybeNull(*location);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            [Inline]
            internal override UIntPtr VisitReferenceFields(Object obj)
            {
                return this.VisitReferenceFields(Magic.addressOf(obj),
                                                 obj.vtable);
            }

            // This method simply forces the compiler to generate a copy
            // of VisitReferenceFieldsTemplate in this class.
            [ManualRefCounts]
            [Inline]
            internal override
            UIntPtr VisitReferenceFields(UIntPtr objectBase, VTable vtable)
            {
                ObjectDescriptor objDesc =
                    new ObjectDescriptor(vtable, objectBase);
                return VisitReferenceFieldsTemplate(ref objDesc);
            }

            [Inline]
            internal void VisitValueNonNull(UIntPtr addr)
            {
                // that's a slow assertion to make!
                //VTable.Assert(Thread.CurrentThread == markThread);
                VisitValueNonNull(addr, markThread);
            }

            [Inline]
            internal void VisitValueMaybeNull(UIntPtr addr)
            {
                // that's a slow assertion to make!
                //VTable.Assert(Thread.CurrentThread == markThread);
                VisitValueMaybeNull(addr, markThread);
            }

            [Inline]
            internal void VisitValueAnyThreadMaybeNull(UIntPtr addr)
            {
                VisitValueMaybeNull(addr, Thread.CurrentThread);
            }

            [Inline]
            internal void VisitValueMaybeNull(UIntPtr addr, Thread currentThread)
            {
                // Ignore null pointers
                if (addr == UIntPtr.Zero) {
                    return;
                }
                VisitValueNonNull(addr, currentThread);
            }

            [Inline]
            internal void VisitValueNonNull(UIntPtr addr, Thread currentThread)
            {
                // Ignore pointers to strange memory areas
                if (PageTable.IsForeignAddr(addr)) {
                    return;
                }
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsGcPage(pageType)) {
                    VTable.Assert((PageTable.IsNonGcPage(pageType) &&
                                   PageTable.IsMyPage(page)) ||
                                  PageTable.IsStackPage(pageType),
                                  "value.visit invalid page");
                    return;
                }
                VTable.Assert(PageTable.IsMyPage(page));
                Object obj = Magic.fromAddress(addr);
                VTable.Assert(IsPossiblyObject(obj),
                              "mark visit: bad object/vtable");
                CMSMarking.MarkObject(addr, currentThread);
            }

            /// <summary>
            /// Process all marked objects from queues stored in
            /// thread objects.
            /// </summary>
            internal virtual void ProcessGrayObjects()
            {
                ThreadHeaderQueue.LocalList workList =
                    new ThreadHeaderQueue.LocalList();
                while (!killCollectorThreads && AcquireWork(ref workList)) {
                    ProcessMyGrayObjects(ref workList);
                }
            }

            [NoBarriers]
            internal virtual
            void ProcessMyGrayObjects(ref ThreadHeaderQueue.LocalList workList)
            {
                while (!killCollectorThreads && !workList.IsEmpty()) {
                    // Pop the next value
                    Object obj = workList.Pop(markedColor);
                    // Visit Fields
                    this.VisitReferenceFields(obj);
                }
            }

            /// <summary>
            /// Look through other threads and see if any have some values on
            /// their queues that we can acquire.
            /// </summary>
            private bool AcquireWork(ref ThreadHeaderQueue.LocalList workList)
            {
                bool foundWork = false;
                UIntPtr stealColor = (UIntPtr) markedColor;
                do {
                    ThreadHeaderQueue.transferAttempt = false;
                    Thread[] threadTable = Thread.threadTable;
                    // Attempt to acquire work from live threads
                    for (int i = 0; i < threadTable.Length; i++) {
                        Thread thread = threadTable[i];
                        if (thread != null &&
                            workList.StealFrom(thread, stealColor)) {
                            foundWork = true;
                        }
                    }
                } while (!foundWork && ThreadHeaderQueue.transferAttempt);
                return foundWork;
            }

            internal virtual void Init()
            {
            }

            /// <summary>
            /// Clean up after processing all queues. This involves calling
            /// reset on each thread's queue.
            /// </summary>
            internal virtual void Cleanup()
            {
                Thread[] threadTable = Thread.threadTable;
                for (int i = 0; i < threadTable.Length; i++) {
                    Thread t = threadTable[i];
                    if (t != null) {
                        VTable.Assert(ThreadHeaderQueue.IsEmpty(t));
                        ThreadHeaderQueue.Reset(t);
                    }
                }
            }

        }

        /// <summary>
        /// This class maps an interior pointer back to the containing object
        /// pointer and then passes it on to the object marking visitor.
        /// </summary>
        internal class StackMarkReferenceVisitor : NonNullReferenceVisitor
        {

            internal unsafe virtual void ProcessObjectPtr(UIntPtr objectPtr,
                                                          UIntPtr *loc,
                                                          UIntPtr addr)
            {
                markReferenceVisitor.VisitValueAnyThreadMaybeNull(objectPtr);
            }

            /// <summary>
            /// Visit an interior pointer stored in loc.
            /// </summary>
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
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType),
                                  "interior.visit invalid page");
                    return;
                }
                UIntPtr objectPtr = SegregatedFreeList.Find(addr);
                VTable.Assert(IsPossiblyObject(Magic.fromAddress(objectPtr)),
                              "stack visit: bad object/vtable");
                ProcessObjectPtr(objectPtr, loc, addr);
            }

        }

        /// <summary>
        /// This class is used to visit every object in the heap
        /// replacing markedColor with unmarkedColor.  It is used
        /// only in the StopTheWorld phase of the collector.
        /// </summary>
        internal class UnmarkVisitor : SegregatedFreeList.ObjectVisitor
        {
            internal override void VisitSmall(Object obj, UIntPtr memAddr)
            {
                if (ThreadHeaderQueue.GcMark(obj) == markedColor) {
                    ThreadHeaderQueue.SetGcMark(obj, unmarkedColor);
                }
            }

            internal override UIntPtr VisitLarge(Object obj)
            {
                if (ThreadHeaderQueue.GcMark(obj) == markedColor) {
                    ThreadHeaderQueue.SetGcMark(obj, unmarkedColor);
                }
                return ObjectLayout.Sizeof(obj);
            }
        }

        /// <summary>
        /// This class is used to visit every object, determine if it
        /// is marked and free it if not.
        /// </summary>
        internal class SweepVisitor : SegregatedFreeList.ObjectVisitor
        {

            private SegregatedFreeList.TempList tempList;

            internal override void VisitSmall(Object obj, UIntPtr memAddr)
            {
                if (ThreadHeaderQueue.GcMark(obj) == reclamationColor) {
                    // Not marked.
                    tempList.Add(memAddr);
                }
            }

            internal override void VisitSmallPageEnd() {
                SegregatedFreeList.FreeSmallList(ref tempList);
            }

            internal override UIntPtr VisitLarge(Object obj)
            {
                UIntPtr objectSize = ObjectLayout.Sizeof(obj);
                if (ThreadHeaderQueue.GcMark(obj) == reclamationColor) {
                    // Not marked.
                    SegregatedFreeList.FreeLarge(obj);
                }
                return objectSize;
            }

            internal override bool Continue {
                get {
                    return !killCollectorThreads;
                }
            }
        }

        /// <summary>
        /// Find the object address for a given interior pointer.
        /// </summary>
        internal override UIntPtr FindObjectAddr(UIntPtr interiorPtr) {
            return SegregatedFreeList.Find(interiorPtr);
        }

        /// <summary>
        /// Visit all objects in the heap with a specified visitor.
        /// </summary>
        internal override
        void VisitObjects(ObjectLayout.ObjectVisitor objectVisitor,
                          UIntPtr lowAddr, UIntPtr highAddr)
        {
            VTable.Assert(PageTable.PageAligned(lowAddr),
                          "low not page aligned");
            VTable.Assert(PageTable.PageAligned(highAddr),
                          "high not page aligned");
            UIntPtr lowPage = PageTable.Page(lowAddr);
            UIntPtr highPage = PageTable.Page(highAddr);
            SegregatedFreeList.VisitObjects(lowPage, highPage, objectVisitor);
        }

        /// <summary>
        /// A new thread has been created, set any allocator/collector state.
        /// </summary>
        internal override void NewThreadNotification(Thread newThread,
                                                     bool initial)
        {
            base.NewThreadNotification(newThread, initial);
            threadColor[newThread.threadIndex] = markedColor;
            ThreadHeaderQueue.Reset(newThread);
            SegregatedFreeList.NewThreadNotification(newThread, initial);
            if (CurrentMarkingPhase == MarkingPhase.ComputingRoots) {
                Transitions.MakeGCRequest(newThread.threadIndex);
            }
        }

        internal override void DeadThreadNotification(Thread deadThread)
        {
            MultiUseWord.CollectFromThread(deadThread);
            SegregatedFreeList.DeadThreadNotification(deadThread);
            ThreadHeaderQueue.DeadThreadNotification(deadThread, markedColor);
            threadColor[deadThread.threadIndex] = (UIntPtr) noColor;
            base.DeadThreadNotification(deadThread);
        }

        internal override void ThreadStartNotification(int currentThreadIndex)
        {
            base.ThreadStartNotification(currentThreadIndex);
            threadColor[currentThreadIndex] = markedColor;
            if (CurrentMarkingPhase == MarkingPhase.ComputingRoots) {
                Transitions.MakeGCRequest(currentThreadIndex);
            }
        }

        internal override void ThreadDormantGCNotification(int threadIndex) {
            // We could scan our own stack, but instead we try to get
            // some work done while the Trace thread scans our stack.
            if (UseSTWTracingPhase &&
                CurrentMarkingPhase == MarkingPhase.StopTheWorld) {
                Thread.SignalGCEvent(markThread.threadIndex);
            }
            base.ThreadDormantGCNotification(threadIndex);
        }

        /// <summary>
        /// This class is used to verify that there are no dangling pointers.
        /// </summary>
        private class VerifyVisitor : SegregatedFreeList.ObjectVisitor
        {

            internal static VerifyVisitor visitor = new VerifyVisitor();

            internal override void VisitSmall(Object obj, UIntPtr memAddr) {
                if (ThreadHeaderQueue.GcMark(obj) == markedColor) {
                    VerifyMarkVisitor.visitor.VisitReferenceFields(obj);
                } else {
                    VTable.Assert(ThreadHeaderQueue.GcMark(obj) ==
                                  unmarkedColor);
                }
            }

            internal override UIntPtr VisitLarge(Object obj) {
                UIntPtr size;
                if (ThreadHeaderQueue.GcMark(obj) == markedColor) {
                    // The object has the mark color, so it should only
                    // reference other objects with the mark color.
                    size = VerifyMarkVisitor.visitor.VisitReferenceFields(obj);
                } else {
                    VTable.Assert(ThreadHeaderQueue.GcMark(obj) ==
                                  unmarkedColor);
                    size = ObjectLayout.Sizeof(obj);
                }
                return size;
            }

        }

        /// <summary>
        /// This class is used to check that all the pointers within a marked
        /// object point into other marked objects.
        /// </summary>
        private class VerifyMarkVisitor : MutableReferenceVisitor
        {

            internal static VerifyMarkVisitor visitor
                = new VerifyMarkVisitor();

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                if (PageTable.IsGcPage(page)) {
                    Object obj = Magic.fromAddress(addr);
                    VTable.Assert(ThreadHeaderQueue.GcMark(obj) == markedColor,
                                  "dangling pointer!");
                }
            }

        }

        /// <summary>
        /// This method loops through all non-null threads and asserts that
        /// no thread has any work on its marking queue.
        /// </summary>
        private static void VerifyEmptyQueues() {
            Thread[] threadTable = Thread.threadTable;
            for (int i = 0; i < threadTable.Length; i++) {
                Thread t = threadTable[i];
                if (t != null) {
                    VTable.Assert(ThreadHeaderQueue.IsEmpty(t),
                                  "Non-empty Queue!");
                }
            }
        }

        private static void VerifyResetQueues() {
            Thread[] threadTable = Thread.threadTable;
            for (int i = 0; i < threadTable.Length; i++) {
                Thread t = threadTable[i];
                if (t != null) {
                    VTable.Assert(ThreadHeaderQueue.IsReset(t),
                                  "Non-reset queue");
                }
            }
        }

        /// <summary>
        /// This method walks through all objects in the heap to ensure
        /// that no objects have values in their queue header field
        /// </summary>
        private static void VerifyQueueHeaders() {
            SegregatedFreeList.VisitAllObjects(VerifyHeaderVisitor.visitor);
        }

        /// <summary>
        /// This visitor trivially asserts that the objects queue header
        /// field is zero.
        /// </summary>
        private class VerifyHeaderVisitor : SegregatedFreeList.ObjectVisitor
        {

            internal static VerifyHeaderVisitor visitor
                = new VerifyHeaderVisitor();

            /// <summary>
            /// Visit small objects, checking queue header.
            /// </summary>
            internal unsafe override void VisitSmall(Object obj,
                                                     UIntPtr memAddr)
            {
                VTable.Deny(ThreadHeaderQueue.IsInQueue(obj),
                            "Object in ThreadHeaderQueue");
            }

            internal override UIntPtr VisitLarge(Object obj) {
                VTable.Deny(ThreadHeaderQueue.IsInQueue(obj),
                            "Object in ThreadHeaderQueue");
                return ObjectLayout.Sizeof(obj);
            }

        }

        private static bool fDebug { get { return false; } }
        private static bool fDebugPhasing { get { return false; } }
    }

}
