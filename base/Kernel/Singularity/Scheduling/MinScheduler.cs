//------------------------------------------------------------------------------
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Description: MinScheduler.cs
//
//  Minimal round-robin style without priorities scheduler.
//
//  MinScheduler favors thread that have recently become unblocked
//  and tries to avoid reading the clock or reseting the timer as
//  much as possible.
//
//  The minimal scheduler maintains two queues of threads that can
//  be scheduled.  The unblockedThreads queue contains threads which
//  have become unblocked during this scheduling quantum; mostly,
//  these are threads that were unblocked by the running thread.
//  The runnableThreads queue contains all other threads that are
//  currently runnable.  If the current thread blocks, MinScheduler
//  will schedule threads from the unblockedThread queue, without
//  reseting the timer.  When the timer finally fires, MinScheduler
//  moves all unblockedThreads to the end of the runnableThreads
//  queue and schedules the next runnableThread.
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
    /// <summary>
    /// Summary description for MinScheduler.
    /// </summary>
    [NoCCtor]
    [CLSCompliant(false)]
    public class MinScheduler : Scheduler
    {
        ///
        /// <summary>
        /// Constructor for MinScheduler object
        /// </summary>
        ///
        public MinScheduler()
        {
            // If busy, don't run for more than 10ms on same task.
            minSlice = TimeSpan.FromMilliseconds(10);

            // Note that we have made the idleSlice small always.
            // This is necessary in the MP case - otherwise a
            // CPU seeing no work will go to sleep for a month and
            // there is no mechanism to be woken when another CPU
            // has excess work.  (This support should be added
            // eventually if we intend to use this scheduler.)
            idleSlice = TimeSpan.FromMilliseconds(100);

            affinity = 0;

            // Create a scheduler lock
            this.runnableLock = new SchedulerLock();

            // Initialize timer's spinlock
            this.timerLock = new SpinLock(SpinLock.Types.Timer);
        }

        /// <summary>
        /// Initialize min scheduler
        /// </summary>
        ///
        public override void Initialize()
        {
        }

        /// <summary>
        /// Finalize scheduler object
        /// </summary>
        ///
        public override void Finalize()
        {
        }

        ///
        /// <summary>
        /// Notify scheduler about new dispatcher
        /// </summary>
        ///
        public override void OnDispatcherInitialize(int dispatcherId)
        {
            // Min scheduler doesn't care about multiple dispatchers
        }

        /// <summary>
        /// Attach thread to scheduler: thread specific initializtion
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
        /// Retrieve scheduler lock - used by dispatcher to protect scheduler state
        /// </summary>
        ///
        /// <param name="affinity">Affinity of dispatcher making actual call</param>
        ///
        [CLSCompliant(false)]
        [NoHeapAllocation]
        internal override SchedulerLock RetrieveSchedulerLock(int affinity)
        {
            // Return our default scheduler
            return MyLock;
        }

        ///
        /// <summary>
        /// Run scheduling policy. This method is called by dispatcher when both interrupts
        /// disabled and disptach lock is acquired. As long as multiple dispatchers don't have access
        /// to the this method no protection is required.
        /// </summary>
        ///
        /// <param name="affinity">Set the returned running thread to this affinity.</param>
        /// <param name="currentThread">the thread currently running</param>
        /// <param name="schedulerAction">thread state to change to for the current thread</param>
        /// <param name="currentTime">Current system time</param>
        ///
        [NoHeapAllocation]
        public override Thread RunPolicy(
            int             affinity,
            Thread          currentThread,
            ThreadState     schedulerAction,
            SchedulerTime   currentTime)
        {
            Thread                      threadToReturn = null;
            ThreadState                 newState = ThreadState.Undefined;
            ThreadEntry                 entry = null;

            // Put current thread on a runnable queue only if it is currently in a running state
            if (currentThread != null) {

                // At this point current threads state has to be
                // running - when running derived scheduler state we will deduce new state
                // but until then it has to be running
                VTable.Assert(currentThread.ThreadState == ThreadState.Running);

                // If scheduler action is running make it runnable to have proper state transition
                // Currently we disallow to go from running to running
                if (schedulerAction == ThreadState.Running) {
                    schedulerAction = ThreadState.Runnable;
                }

                // Change current's thread new scheudler state
                newState = currentThread.ChangeSchedulerState(schedulerAction);

                // If new state is runnable add it to runnable queue
                if (newState == ThreadState.Runnable) {
                    // REVIEW: Should we make sure the thread is enqueue already?

                    // Indicate that thread has been marked as runnable
                    this.runnableThreads.EnqueueTail(currentThread.schedulerEntry);
                }
            }

            // Derived state of entry on the runnable queue can be either suspended or runnable.
            // Consequently first we remove an entry from the queue. If it is runnable,
            // we will be able to convert it to running, If it is suspended,
            // we will convert its real state to suspended. The first thread that marks the entry
            // unsuspended will be responsible for putting it on back on a runnable queue.

            // Check the unblocked queue first.
            while ((entry = this.unblockedThreads.DequeueHead()) != null) {

                // At this point thread direct state can be only runnable...
                VTable.Assert(entry.Thread.IsRunnable);

                // Attempt to make thread running
                newState = entry.Thread.ChangeSchedulerState(ThreadState.Running);

                // Get of the loop if we marked one of the entries as running
                if (newState == ThreadState.Running) {
                    break;
                }

                // If the thread is suspended, then look for another.
                VTable.Assert(newState == ThreadState.Suspended);
            }

            // If no recently unblocked threads, then check the runnable queue.
            if (entry == null) {
                while ((entry = this.runnableThreads.DequeueHead()) != null) {

                    // At this point thread direct state can be only runnable...
                    VTable.Assert(entry.Thread.IsRunnable);

                    // Attempt to make thread running
                    newState = entry.Thread.ChangeSchedulerState(ThreadState.Running);

                    // Get of the loop if we marked one of the entries as running
                    if (newState == ThreadState.Running) {
                        break;
                    }

                    // If the thread is suspended, then look for another.
                    VTable.Assert(newState == ThreadState.Suspended);
                }
            }

            // We got an entry from the runnable queue that we can actually run.
            if (entry != null) {

                // Thread must realy by in the running state.
                VTable.Assert(newState == ThreadState.Running);

                // Initialize thread we about to return.
                threadToReturn = entry.Thread;
                threadToReturn.Affinity = affinity;
            }

            return threadToReturn;
        }

        ///
        /// <summary>
        /// Add thread to runnable queue.  This method is called by dispatcher at the
        /// point when both dispatcher lock and interrupts are disabled
        /// </summary>
        ///
        /// <param name="thread">Thread to add to runnable queue </param>
        ///
        [Inline]
        [NoHeapAllocation]
        public override void AddRunnableThread(Thread thread)
        {
            ThreadState newState;

            // Change thread's state to runnable: Runpolicy will decide latter on
            // if it can actually run the thread
            newState = thread.ChangeSchedulerState(ThreadState.Runnable);

            // Add thread to runnable queue only if new state is runnable
            if (newState == ThreadState.Runnable) {
                // While we adding a thread to runnable queue someone could have called freeze on
                // it again - RunPolicy will notice it and remove thread from runnable queue appropriatly

                this.unblockedThreads.EnqueueTail(thread.schedulerEntry);
            }
        }

        ///
        /// <summary>
        /// Start thread - put a thread on dispatcher's runnable queue so it can be run
        /// </summary>
        ///
        /// <param name="thread">Thread to start </param>
        ///
        [NoHeapAllocation]
        public override void OnThreadStart(Thread thread)
        {
            // Initialize thread's affinity
            thread.Affinity = (int)ProcessorDispatcher.Affinity.All;

            // Enqueue thread into dispatcher.
            ProcessorDispatcher.AddRunnableThread(thread);
       }

        ///
        /// <summary>
        /// Block thread -process thread blocking including putting it on a timer queue if
        /// timeout is specified.
        /// </summary>
        ///
        /// <param name="thread">Thread that blocks </param>
        /// <param name="stop">Amount of time for the thread to be blocked</param>
        ///
        [NoHeapAllocation]
        public override void OnThreadBlocked(Thread thread, SchedulerTime stop)
        {
            // Assert preconditions
            VTable.Assert(thread == Thread.CurrentThread);

            if (stop != SchedulerTime.MaxValue) {
                // Enqueue timer so that if it expires we will notice it right a way
                EnqueueTimer(thread, stop);
            }

            // Thread is blocked now - indicate this to dispatcher. Dispatcher will make
            // make sure that thread's scheduler is aware of the blockage
            ProcessorDispatcher.SwitchContext(ThreadState.Blocked);

            // We just got unblocked and happilly running. We need to remove ourselves
            // from the timer queue if we are unblocked by signal rather than by timeout
            if (thread.UnblockedBy != WaitHandle.WaitTimeout) {
                // One of our buddies unblocked us - remove the time out. Before we can
                // actually assert that we were indeed unblocked by someone.
                VTable.Assert(thread.UnblockedBy != WaitHandle.UninitWait);

                // Remove a timer from the timer queue and happilly continue!
                RemoveTimer(thread);
            }
        }

        ///
        /// <summary>
        /// Unblock thread - resume thread by putting it on the dispatcher runnable  queue.
        /// This method can be invoked by threads running on other processors
        /// </summary>
        ///
        /// <param name="thread">Thread to resume </param>
        ///
        [NoHeapAllocation]
        public override void OnThreadUnblocked(Thread thread)
        {
            // Only call this method if thread is Indeed blocked
            VTable.Assert(thread.IsBlocked);

            // Thread is ready to run: Add it to dispatcher
            ProcessorDispatcher.AddRunnableThread(thread);
        }

        ///
        /// <summary>
        /// Yield thread - suspend thread based on time slice
        /// </summary>
        ///
        /// <param name="thread">Thread that is yielding </param>
        ///
        [NoHeapAllocation]
        public override void OnThreadYield(Thread thread)
        {
            // Perform a context switch: If thread is runnable it will be put on a runnable queue
            // by dispatcher.
            ProcessorDispatcher.SwitchContext(ThreadState.Running);
        }

        ///
        /// <summary>
        /// Stop thread execution
        /// </summary>
        ///
        /// <param name="thread">Thread that is stopping </param>
        ///
        [NoHeapAllocation]
        public override void OnThreadStop(Thread thread)
        {
            // Perform a context switch: If thread is stopped it will be cleaned up, otherwise
            // it is suspended and will be cleaned up latter
            ProcessorDispatcher.SwitchContext(ThreadState.Stopped);
        }

        ///
        /// <summary>
        /// Increment frozen counter
        /// </summary>
        ///
        /// <param name="thread">Thread for which to increment freeze counter </param>
        ///
        [NoHeapAllocation]
        public override void OnThreadFreezeIncrement(Thread thread)
        {
            // Update threads: Freeze count
            thread.IncrementFreezeCounter();
        }

        ///
        /// <summary>
        /// Decrement frozen counter
        /// </summary>
        ///
        /// <param name="thread">Thread for which to update freeze counter </param>
        ///
        [NoHeapAllocation]
        public override void OnThreadFreezeDecrement(Thread thread)
        {
            bool shouldPutThreadOnRunnableQueue = false;

            // Assert preconditions
            DebugStub.Assert(thread.FreezeCount > 0);

            // Update threads: Freeze count
            if (thread.DecrementFreezeCounter(ref shouldPutThreadOnRunnableQueue) == 0 &&
                shouldPutThreadOnRunnableQueue) {

                // Thread became runnable - add it to runnable queue
                ProcessorDispatcher.AddRunnableThread(thread);
            }
        }

        ///
        /// <summary>
        /// Suspend thread and wait until it is suspended.
        /// </summary>
        ///
        /// <param name="thread">Thread to suspend </param>
        ///
        [NoHeapAllocation]
        public override void Suspend(Thread thread)
        {
            // Assert preconditions: We can't call suspend on ourselves
            VTable.Assert(thread != Thread.CurrentThread);

            // Increment freeze counter and then spin wait until thread will become suspended
            OnThreadFreezeIncrement(thread);

            // Wait until thread is capable of running
            while (thread.IsRunning || thread.IsRunnable) {
                Thread.SpinWait(100);
            }
        }

        ///
        /// <summary>
        /// Resume thread from being suspended
        /// </summary>
        ///
        /// <param name="thread">Thread to resume </param>
        ///
        [NoHeapAllocation]
        public override void Resume(Thread thread)
        {
            // Increment freeze counter and then spin wait until thread will becom suspended
            OnThreadFreezeDecrement(thread);
        }

        ///
        /// <summary>
        /// Dispatch timer interrupt. This method is called by dispather when interrupts are
        /// disabled.
        /// </summary>
        ///
        /// <param name = "affinity">Processor affinity</param>
        /// <param name = "now">Current time</param>
        ///
        [CLSCompliant(false)]
        [NoHeapAllocation]
        [HalLock]
        public override TimeSpan OnTimerInterrupt(int affinity, SchedulerTime now)
        {
            ThreadEntry     entry;
            TimeSpan        delta;

            // Assert pre conditions
            DebugStub.Assert(this.minSlice.Ticks != 0);
            DebugStub.Assert(this.idleSlice.Ticks != 0);

            // For now interrupts should be disabled when this method is called
            VTable.Assert(Processor.InterruptsDisabled());

            // Move all of the unblockedThreads to the runnable queue.
            while ((entry = this.unblockedThreads.DequeueHead()) != null) {
                this.runnableThreads.EnqueueTail(entry);
            }

            // Acquire timer lock
            timerLock.Acquire();

             // Unblock any threads whose timers have elapsed.
            while ((entry = this.timerThreads.Head) != null &&
                   entry.Thread.BlockedUntil <= now) {

                // Remove thread from the timer queue: There shouldn't be race with RemoveTimer
                // call since we are protected by a timer queue's lock
                this.timerThreads.Remove(entry);

                // Indicate to the thread that its wait completed with timeout
                if (entry.Thread.Unblock(WaitHandle.WaitTimeout) == WaitHandle.WaitTimeout) {
                    // Only if we have unblocked thread and it was already in blocked state
                    // put it on a dispatcher deferred wake up queue: otherwise scheduler will notice
                    // expiration itself and put the thread on a runnable queue. For more info
                    // see RunPolicy
                    if (entry.Thread.ShouldCallSchedulerUnBlock(WaitHandle.WaitTimeout)) {

                        // Change thread's state to runnable: Runpolicy will decide latter on
                        // if it can actually run the thread
                        entry.Thread.ChangeSchedulerState(ThreadState.Runnable);

                        // Place thread at the tail of the unblocked queue
                        this.unblockedThreads.EnqueueTail(entry);
                    }
                }
            }

            // Adjust the timeout so that we wake up sooner if
            // there is a thread waiting on a timer.
            if (!this.timerThreads.IsEmpty() &&
                this.timerThreads.Head.Thread.blockedUntil < (now + this.minSlice)) {
                this.nextTimer = this.timerThreads.Head.Thread.blockedUntil;
            }
            else {
                this.nextTimer = now + this.idleSlice;
            }

            // Remember new alarm we are to set
            delta = this.nextTimer - now;

            // We are done: Don't forget to release timer lock:
            timerLock.Release();

            return delta;
        }

        ///
        /// <summary>
        /// Remove a timer from timer queue: if thread is still on a timer queue. Need to
        /// disable interrupts before acquire timer lock - dispatcher always calls into timer
        /// with interrupts disable. If we don't disable interrupts we will get into possible deadlock
        /// with dispatcher
        /// </summary>
        ///
        [CLSCompliant(false)]
        [NoHeapAllocation]
        [HalLock]
        private void RemoveTimer(Thread thread)
        {
            // For now disable interrupts and acquire scheduler lock
            bool    shouldEnable = Processor.DisableInterrupts();

            // Acquire timer lock
            timerLock.Acquire();

            if (thread.timerEntry.queue != null) {
                this.timerThreads.Remove(thread.timerEntry);
            }

            // Release timer lock
            timerLock.Release();

            // Reenable interrupts
            Processor.RestoreInterrupts(shouldEnable);
        }

        ///
        /// <summary>
        /// Park blocking thread in a timer queue with a given time out. Need to
        /// disable interrupts before acquiring timer lock - dispatcher always calls into timer
        /// with interrupts disable. If we don't disable interrupts we will get into deadlock
        /// </summary>
        ///
        /// <param name="thread">Thread to block</param>
        /// <param name="stop">Period of time for a thread to wait before timeout</param>
        ///
        [NoHeapAllocation]
        [HalLock]
        private void EnqueueTimer(Thread thread, SchedulerTime stop)
        {
            // For now disable interrupts and acquire scheduler lock...
            bool                shouldEnable = Processor.DisableInterrupts();
            int                 unblockedBy;
            SchedulerTime       now = SchedulerTime.Now;
            TimeSpan            delta = stop - now;

            //Acquire scheduler lock:
            this.timerLock.Acquire();

            // Find out if we need to update alarm.
            bool shouldChangeAlarm = ((this.timerThreads.Head == null) ||
                                      (this.timerThreads.Head.Thread.blockedUntil > stop));

            // If new wait already expired just try to fail it right a way. Alarm upate
            // indicates that only this new wait can be retired
            if (shouldChangeAlarm && stop <= now) {

                unblockedBy = thread.Unblock(WaitHandle.WaitTimeout);

                // We no longer should be changing alarm
                shouldChangeAlarm = false;

                // if we unblocked by timer or by someone else we don't have to anything -
                // OnThreadBlock will adjust thread's state accordingly. For more info see
                // OnThreadBlock, Dispatcher.ContextSwitch and RunPolicy
            }
            else {
                // Enqueue thread in the right place
                ThreadEntry entry = this.timerThreads.Head;

                while (entry != null && entry.Thread.blockedUntil <= stop) {
                    // Loop until we find the first thread with a later stop.
                    entry = entry.Next;
                }

                // Store thread's block until information
                thread.blockedUntil = stop;

                // Found the right place go ahead and put the thread into the queue
                this.timerThreads.InsertBefore(entry, thread.timerEntry);
            }

            // Before we let others to party on a timer check if timer has to be reset:
            // and if so rember it and reset once we release the lock
            if (shouldChangeAlarm && this.nextTimer > stop) {
                this.nextTimer = stop;
            }
            else {
                shouldChangeAlarm = false;
            }

            // Release timer lock
            this.timerLock.Release();

            // If we are required to set a time on dispatcher, do it outside of
            // spinlock since nobody is currently can be running on our processor
            // since we have interrupts disabled.
            if (shouldChangeAlarm) {
                Processor.CurrentProcessor.SetNextTimerInterrupt(delta);
            }

            // Re-enable interrupts
            Processor.RestoreInterrupts(shouldEnable);
        }

        ///
        /// <summary>
        /// Property to get to the scheduler runnable queue lock
        /// </summary>
        ///
        internal SchedulerLock MyLock
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.runnableLock;
            }
        }

        ///
        /// <summary>
        /// Get the affinity of this base scheduler
        /// </summary>
        ///
        internal int Affinity
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.affinity;
            }
        }

        /// <summary> A spinlock protecting state of the timer queue </summary>
        private SchedulerLock           runnableLock;

        /// <summary> A spinlock protecting state of the timer queue </summary>
        private SpinLock                timerLock;

        /// <summary> List of recently runnable, but unscheduled threads. </summary>
        private ThreadQueue             unblockedThreads = new ThreadQueue();

        /// <summary> List of runnable, but unscheduled threads. </summary>
        private ThreadQueue             runnableThreads = new ThreadQueue();

        /// <summary> List of blocked threads, sorted by wait time. </summary>
        private ThreadQueue             timerThreads = new ThreadQueue();

        /// <summary> Scheduler affinity </summary>
        private readonly int            affinity;

        /// <summary> List of frozen threads (unsorted) </summary>
        private SchedulerTime           nextTimer;

        /// <summary> Idle thread </summary>
        private Thread                  idleThread;

        /// <summary> Run time slice </summary>
        private TimeSpan                minSlice;

        /// <summary> Run time for idle slice </summary>
        private TimeSpan                idleSlice;

        /// <summary> Check if need to process interprocess interrupt </summary>
        private bool                    isIpiNeeded;
    }
}
