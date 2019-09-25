//------------------------------------------------------------------------------
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Description: $filename$
//
//          Minimal round-robin style without priorities scheduler.
//
//          AffinityScheduler favors thread that have recently become unblocked
//          and tries to avoid reading the clock or reseting the timer as
//          much as possible.
//
//          The minimal scheduler maintains two queues of threads that can
//          be scheduled.  The unblockedThreads queue contains threads which
//          have become unblocked during this scheduling quantum; mostly,
//          these are threads that were unblocked by the running thread.
//          The runnableThreads queue contains all other threads that are
//          currently runnable.  If the current thread blocks, AffinityScheduler
//          will schedule threads from the unblockedThread queue, without
//          reseting the timer.  When the timer finaly fires, AffinityScheduler
//          moves all unblockedThreads to the end of the runnableThreads
//          queue and schedules the next runnableThread.
//------------------------------------------------------------------------------

using System;
using System.Collections;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Bartok.Options;

using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Scheduling;

namespace Microsoft.Singularity.Scheduling
{
    ///
    /// <summary>
    /// Summary description for AffinityScheduler.
    /// </summary>
    ///
    [NoCCtor]
    [CLSCompliant(false)]
    public class AffinityScheduler : Scheduler
    {
        public AffinityScheduler()
        {
        }

        ///
        /// <summary>
        ///     Initialize min scheduler
        /// </summary>
        ///
        public override void Initialize() {

            // HACK use 30ms for now to give time for debug output.
            // If busy, don't run for more than 10ms on same task.
            TimeSpan minSlice = TimeSpan.FromMilliseconds(10);

            schedulers = new BaseScheduler [Processor.processorTable.Length];

            // Create the idle threads and put them on the idleThreads loop.
            for (int i = 0; i < Processor.processorTable.Length; i++) {

                // Create scheduler
                schedulers[i] = BaseSchedulerManager.CreateScheduler(minSlice, i);
            }

            // Wait until first dispatcher will call into the scheduler
            numberOfActiveDispatchers = 0;
        }

        ///
        /// <summary>
        ///     Finalize scheduler object
        /// </summary>
        ///
        public override void Finalize()
        {
        }

        ///
        /// <summary>
        ///     Notify scheduler about new dispatcher
        /// </summary>
        ///
        public override void OnDispatcherInitialize(int dispatcherId)
        {
            // Increment number of active dispatchers
            int dispatchers = Interlocked.Increment (ref numberOfActiveDispatchers);

            // Check if a now we really MP enabled
            if (dispatchers == Processor.ExpectedProcessors) {
                isMPEnabled = true;
            }
        }

        ///
        /// <summary>
        ///     Attach thread to scheduler: thread specific initializtion
        /// </summary>
        ///
        /// <param name="thread">Thread to attach </param>
        /// <param name="constructorCalled">Have we called thread constructor </param>
        ///
        public override void OnThreadStateInitialize(Thread thread, bool constructorCalled)
        {
            // Only initialize thread-local state!  No locks held and interrupts on.
        }

        ///
        /// <summary>
        ///     Start thread - put a thread on unblocked queue so it can be run
        /// </summary>
        ///
        /// <param name="thread">Thread to start </param>
        ///
        public override void OnThreadStart(Thread thread)
        {
            // TODO: this needs to check whether the processor is running yet.
            int threadID = thread.GetThreadId();
            // NOTE Affinity may be legally set to any int. NoAffinity(-1) is special.
            // All other ints must be converted to a legal index into the processor table
            int initial = thread.Affinity == Thread.NoAffinity
                ? threadID
                : Math.Abs(thread.Affinity);
            int cpu = isMPEnabled ? initial % numberOfActiveDispatchers : 0;
            thread.Affinity = cpu;
            schedulers[cpu].OnThreadStart(thread);
        }

        ///
        /// <summary>
        ///     Block thread - put a thread on block queue and retrieve next thread to run
        /// </summary>
        ///
        /// <param name="thread">Thread that blocks </param>
        /// <param name="stop">Amount of time for the thread to be blocked</param>
        ///
        public override void OnThreadBlocked(Thread thread, SchedulerTime stop)
        {
            schedulers[thread.Affinity].OnThreadBlocked(thread, stop);
        }

        ///
        /// <summary>
        ///     Unblock thread - resume thread by putting it on unblock queue. This method
        ///  can be invoked by threads running on other processors
        /// </summary>
        ///
        /// <param name="thread">Thread to resume </param>
        ///
        [NoHeapAllocation]
        public override void OnThreadUnblocked(Thread thread)
        {
            schedulers[thread.Affinity].OnThreadUnblocked(thread);
        }

        ///
        /// <summary>
        ///     Yield thread - suspend thread based on time slice
        /// </summary>
        ///
        /// <param name="thread">Thread that is yielding </param>
        ///
        [NoHeapAllocation]
        public override void OnThreadYield(Thread thread)
        {
            schedulers[thread.Affinity].OnThreadYield(thread);
        }

        ///
        /// <summary>
        ///     Stop thread execution
        /// </summary>
        ///
        /// <param name="thread">Thread that is stopping </param>
        ///
        public override void OnThreadStop(Thread thread)
        {
            schedulers[thread.Affinity].OnThreadStop(thread);
        }

        ///
        /// <summary>
        ///     Increment frozen counter
        /// </summary>
        ///
        /// <param name="thread">Thread for which to increment freeze counter </param>
        ///
        public override void OnThreadFreezeIncrement(Thread thread)
        {
            schedulers[thread.Affinity].OnThreadFreezeIncrement(thread);
        }

        ///
        /// <summary>
        ///     Decrement frozen counter
        /// </summary>
        ///
        /// <param name="thread">Thread for which to update freeze counter </param>
        ///
        public override void OnThreadFreezeDecrement(Thread thread)
        {
            schedulers[thread.Affinity].OnThreadFreezeDecrement(thread);
        }

        ///
        /// <summary>
        ///    Dispatch timer interrupt
        /// </summary>
        ///
        /// <param name = "affinity">Processor affinity</param>
        /// <param name = "now">Current time</param>
        /// <param name ="deferredWakeupQueue">
        ///     Queue used to put threads to be waken up. Latter on dispatcher will add threads
        ///     to scheduler's runnable queue
        /// </param>
        ///
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override TimeSpan OnTimerInterrupt(int affinity, SchedulerTime now)
        {
            return schedulers[affinity].OnTimerInterrupt(affinity, now);
        }

        ///
        /// <summary>
        ///     Add thread to runnable queue.  This methods is called by dispatcher at the
        /// point when both dispatcher lock and interrupts are disabled
        /// </summary>
        ///
        /// <param name="thread">Thread to add to runnable queue </param>
        /// <param name="hint">Place to where enqueue thread in a runnable queue</param>
        ///
        [Inline]
        [NoHeapAllocation]
        public override void AddRunnableThread(Thread thread)
        {
            schedulers[thread.Affinity].AddRunnableThread(thread);
        }

        ///
        /// <summary>
        ///     Run scheduling policy to decide the next thread to run
        /// </summary>
        ///
        /// <param name="schedulerAffinity">The affinity of the scheduler</param>
        /// <param name="runningThreadAffinity">The running thread returned should be
        ///     set to this affinity. It's same as schedulerAffinity except during
        ///     thread migration
        /// </param>
        /// <param name="currentThread">the thread currently running</param>
        /// <param name="schedulerAction">thread state to change to for the current thread</param>
        /// <param name="currentTime">Current system time</param>
        ///
        [NoHeapAllocation]
        public override Thread RunPolicy(
            int             schedulerAffinity,
            int             runningThreadAffinity,
            Thread          currentThread,
            ThreadState     schedulerAction,
            SchedulerTime   currentTime)
        {
            // Assert preconditions: current thread can be either NULL or its base scheduler
            // should be the same as specified by affinity
            VTable.Assert(currentThread == null ||
                          currentThread.Affinity == schedulerAffinity);

            // Use affinity to derive actual scheduler
            return schedulers[schedulerAffinity].RunPolicy(
                schedulerAffinity,
                runningThreadAffinity,
                currentThread,
                schedulerAction,
                currentTime);
        }

        ///
        /// <summary>
        ///     Suspend thread and wait until it is suspended.
        /// </summary>
        ///
        /// <param name="thread">Thread to suspend </param>
        ///
        [NoHeapAllocation]
        public override void Suspend(Thread thread)
        {
            schedulers[thread.Affinity].Suspend(thread);
        }

        ///
        /// <summary>
        ///     Resume thread from being suspended
        /// </summary>
        ///
        /// <param name="thread">Thread to resume </param>
        ///
        [NoHeapAllocation]
        public override void Resume(Thread thread)
        {
            schedulers[thread.Affinity].Resume(thread);
        }

        ///
        /// <summary>
        ///     Retrieve scheduler lock - used by dispatcher to protect scheduler state
        /// </summary>
        ///
        /// <param name="affinity">Affinity of dispatcher making actual call</param>
        ///
        [CLSCompliant(false)]
        [NoHeapAllocation]
        internal override SchedulerLock RetrieveSchedulerLock(int affinity)
        {
            // Use the our defualt scheder's to return
            return schedulers[affinity].MyLock;
        }

        /// <summary>An array of schedulers</summary>
        private static BaseScheduler []     schedulers;

        /// <summary> A number of active dispatchers </summary>
        private static int                  numberOfActiveDispatchers;

        /// <summary> Flag showing whether multi processing is enabled </summary>
        private static bool                 isMPEnabled;
    }

}

