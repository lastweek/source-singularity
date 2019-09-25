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

    using System.Threading;
    using System.Runtime.CompilerServices;

#if SINGULARITY
  using Microsoft.Singularity;
  using Microsoft.Singularity.Isal;
#if SINGULARITY_KERNEL
  using Microsoft.Singularity.Scheduling;
#else
  using Microsoft.Singularity.V1.Services;
#endif

    [CLSCompliant(false)]
    public enum GarbageCollectorEvent : ushort
    {
        StartStopTheWorld = 1,
        EndStopTheWorld = 2,
        StartCollection = 3,
        EndCollection = 4,
    }
#endif

    /// <summary>
    /// Identifies the current collection phase
    /// </summary>
    internal enum StopTheWorldPhase {
        Dummy,              // Not used!
        Idle,               // No collection is taking place
        Synchronizing,      // Attempting to stop the world
        SingleThreaded,     // Stop-the-world phase
    }

    [NoCCtor]
    internal class StopTheWorldGCData
    {
        internal static int collectorThreadIndex;

        /// <summary>
        /// The current state of the collector.
        /// </summary>
        internal static volatile StopTheWorldPhase CurrentPhase;
    }

    [NoCCtor]
    internal abstract class StopTheWorldCollector : BaseCollector
    {
        protected static int collectorThreadIndex {
            get { return StopTheWorldGCData.collectorThreadIndex; }
            set { StopTheWorldGCData.collectorThreadIndex = value; }
        }

        protected static StopTheWorldPhase CurrentPhase {
            get { return StopTheWorldGCData.CurrentPhase; }
            set { StopTheWorldGCData.CurrentPhase = value; }
        }

        [PreInitRefCounts]
        internal static void Initialize() {
            collectorThreadIndex = -1;
            CurrentPhase = StopTheWorldPhase.Idle;
        }

        internal override void EnableHeap() {
            // Make sure that we have initialized everything we need to
            // perform the thread rendez-vous before we start the first
            // collection cycle.
            int currentThreadIndex = Thread.GetCurrentThreadIndex();
            Thread.SignalGCEvent(currentThreadIndex);
            Thread.WaitForGCEvent(currentThreadIndex);
        }

        internal override void Collect(Thread currentThread, int generation)
        {
            try {
                GC.CollectTransition(currentThread, generation);
            } catch (Exception e) {
                VTable.DebugPrint("Garbage collection failed with exception");
                VTable.DebugPrint(e.GetType().Name);
                VTable.DebugBreak();
            }
        }

        internal abstract void CollectStopped(int currentThreadIndex,
                                              int generation);

        // Implementation of GCInterface
        internal override bool IsOnTheFlyCollector {
            get {
                return false;
            }
        }

        internal override void CollectStoppable(int currentThreadIndex,
                                                int generation)
        {
            int foundIndex =
                Interlocked.CompareExchange(ref StopTheWorldGCData.collectorThreadIndex,
                                            currentThreadIndex, -1);
            if (foundIndex < 0) {
                // We are the designated collector thread
                PerformCollection(currentThreadIndex, generation);
            } else {
                Transitions.TakeDormantControlNoGC(currentThreadIndex);
                if (Transitions.TakeGCControl(currentThreadIndex)) {
                    // The 'foundIndex' thread may have completed its
                    // collection and another thread may have started
                    // another collection after we read
                    // 'collectorThreadIndex'.  The collector thread may
                    // have decided to wait for us before we entered
                    // DormantState, so we have to read
                    // 'collectorThreadIndex' again.
                    foundIndex = collectorThreadIndex;
                    if (foundIndex >= 0) {
                        Thread.SignalGCEvent(foundIndex);
                    }
                }
                Transitions.TakeMutatorControlNoGC(currentThreadIndex);
            }
        }

        private void PerformCollection(int currentThreadIndex,
                                       int generation)
        {
            // Clear the GCRequest bit (if necessary) before doing
            // anything that could cause a state transition.
            if (Transitions.HasGCRequest(currentThreadIndex)) {
                Transitions.ClearGCRequest(currentThreadIndex);
            }
            int startTicks = 0;
            bool enableGCTiming = VTable.enableGCTiming;
            if (enableGCTiming || VTable.enableFinalGCTiming) {
                VTable.enableGCTiming = false;
                startTicks = Environment.TickCount;
                if (enableGCTiming) {
                    VTable.DebugPrint("[GC start: {0} bytes]\n",
                                      __arglist(TotalMemory));
                }
            }
#if SINGULARITY
            Tracing.Log(Tracing.Debug,"GC start");
#endif
            CollectorStatistics.Event(GCEvent.StopTheWorld);
            CurrentPhase = StopTheWorldPhase.Synchronizing;
            StopTheWorld();
            CurrentPhase = StopTheWorldPhase.SingleThreaded;
            StartGCCycle();
#if SINGULARITY
            long preGcMemoryUsage = GC.GetTotalMemory(false);
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
#endif  //singularity
#if SINGULARITY_KERNEL
            bool iflag = Processor.DisableInterrupts();

            // Disable interrupts on other CPU's
            MpExecution.StopProcessorsForGC();
#endif
#if SINGULARITY
            ulong beg = Isa.GetCycleCount();
#endif
            // Preparation
            GC.allocationGCInhibitCount++;
            // Verify the heap before GC
            if (VTable.enableGCVerify) {
                this.VerifyHeap(true);
            }
            // Invoke the chosen collector
#if SINGULARITY
            Monitoring.Log(Monitoring.Provider.GC,
                           (ushort)GarbageCollectorEvent.StartCollection);
#endif
            this.CollectStopped(collectorThreadIndex, generation);
#if SINGULARITY
            Monitoring.Log(Monitoring.Provider.GC,
                           (ushort)GarbageCollectorEvent.EndCollection);
#endif
            // Verify the heap after GC
            if (VTable.enableGCVerify) {
                this.VerifyHeap(false);
            }
            if (VTable.enableGCAccounting) {
                MemoryAccounting.Report(GC.gcType);
            }
            // Cleanup
            CollectorStatistics.Event(GCEvent.ResumeTheWorld);
            GC.allocationGCInhibitCount--;
            CurrentPhase = StopTheWorldPhase.Idle;
#if SINGULARITY
            long postGcMemoryUsage = GC.GetTotalMemory(false);
#endif
            if (enableGCTiming || VTable.enableFinalGCTiming) {
                int elapsedTicks = Environment.TickCount - startTicks;
                BaseCollector.RegisterPause(elapsedTicks);
                if (enableGCTiming) {
                    VTable.DebugPrint("[GC end  : {0} bytes, {1} ms]\n",
                                      __arglist(TotalMemory, elapsedTicks));
                    VTable.enableGCTiming = true;
                }
            }
            if (VTable.enableGCProfiling) {
                ulong totalMemory = (ulong)GC.GetTotalMemory(false);
                this.RegisterHeapSize(totalMemory);
            }
            ResumeTheWorld();
            collectorThreadIndex = -1;
#if SINGULARITY
            Tracing.Log(Tracing.Debug,"GC stop");
            long pagesCollected = preGcMemoryUsage - postGcMemoryUsage;
#if SINGULARITY_KERNEL
#if THREAD_TIME_ACCOUNTING
            int procId = Thread.CurrentProcess.ProcessId;
            ticks = Thread.CurrentThread.ExecutionTime - ticks;
            ticks2 = SystemClock.KernelUpTime - ticks2;
            Process.kernelProcess.SetGcPerformanceCounters(ticks, (long) pagesCollected);
#else
            ticks = SystemClock.KernelUpTime - ticks;
#endif
            Thread.CurrentProcess.SetGcPerformanceCounters(ticks, (long) pagesCollected);
#elif SINGULARITY_PROCESS
#if THREAD_TIME_ACCOUNTING
            ushort procId = ProcessService.GetCurrentProcessId();
            ticks = ProcessService.GetThreadTime()  - ticks;
            ticks2 = ProcessService.GetUpTime() - ticks2;
#else
            ticks = ProcessService.GetUpTime() - ticks;
#endif
            ProcessService.SetGcPerformanceCounters(ticks, (long) pagesCollected);
#endif

#if DEBUG
#if THREAD_TIME_ACCOUNTING
            DebugStub.WriteLine("~~~~~ StopTheWorld [collected pages={0:x8}, pid={1:x3}, ms(Thread)={2:d6}, ms(System)={3:d6}, procId={4}, tid={5}]",
                                __arglist(pagesCollected,
                                          PageTable.processTag >> 16,
                                          ticks.Milliseconds,
                                          ticks2.Milliseconds,
                                          procId,
                                          Thread.GetCurrentThreadIndex()
                                          ));
#endif
#endif
#endif

#if SINGULARITY
            DebugStub.AddToPerfCounter(GC.perfCounter, Isa.GetCycleCount() - beg);
#endif
#if SINGULARITY_KERNEL
            // Resume interrupts on other CPU's
            MpExecution.ResumeProcessorsAfterGC();

            Processor.RestoreInterrupts(iflag);
#endif
        }

        internal override void CheckForNeededGCWork(Thread currentThread) {
            while (CurrentPhase == StopTheWorldPhase.Synchronizing &&
                   currentThread.threadIndex != collectorThreadIndex) {
                GC.InvokeCollection(currentThread);
            }
        }

        internal override void NewThreadNotification(Thread newThread,
                                                     bool initial)
        {
            base.NewThreadNotification(newThread, initial);
            if (CurrentPhase == StopTheWorldPhase.Synchronizing) {
                Transitions.MakeGCRequest(newThread.threadIndex);
            }
        }

        internal override void DeadThreadNotification(Thread deadThread)
        {
            MultiUseWord.CollectFromThread(deadThread);
            base.DeadThreadNotification(deadThread);
        }

        internal override void ThreadDormantGCNotification(int threadIndex) {
            int ctid = collectorThreadIndex;
            if (ctid >= 0) {
                Thread.SignalGCEvent(ctid);
            }
            base.ThreadDormantGCNotification(threadIndex);
        }

        internal virtual void StopTheWorld() {
#if SINGULARITY
            //DebugStub.WriteLine("~~~~~ StopTheWorld()");
            Monitoring.Log(Monitoring.Provider.GC,
                           (ushort)GarbageCollectorEvent.StartStopTheWorld);
#if SINGULARITY_KERNEL
            TimeSpan ticks = SystemClock.KernelUpTime;
#elif SINGULARITY_PROCESS
            TimeSpan ticks = ProcessService.GetUpTime();
#endif
#endif
            VTable.Assert(Thread.GetCurrentThreadIndex() ==
                          collectorThreadIndex);
            BaseCollector.AllThreadRendezvous(collectorThreadIndex);
#if SINGULARITY
#if SINGULARITY_KERNEL
            ticks = SystemClock.KernelUpTime - ticks;
#elif SINGULARITY_PROCESS
            ticks = ProcessService.GetUpTime() - ticks;
#endif
            Monitoring.Log(Monitoring.Provider.GC,
                           (ushort)GarbageCollectorEvent.EndStopTheWorld);
#endif
        }

        internal virtual void ResumeTheWorld() {
            VTable.Assert(Thread.GetCurrentThreadIndex() ==
                          collectorThreadIndex);
            BaseCollector.AllThreadRelease(collectorThreadIndex);
        }

    }

}
