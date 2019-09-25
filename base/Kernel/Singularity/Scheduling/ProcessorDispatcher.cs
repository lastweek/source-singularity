//------------------------------------------------------------------------------
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  This file contains an implementation of processor dispatcher. There is one processor
//  Dispatcher per processor
//------------------------------------------------------------------------------

#if DEBUG
#define SHOW_TWIDDLE
#endif

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.GCs;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity.Scheduling
{
    ///
    /// <summary>
    /// A Processor Dispatcher is responsible for handling processor runnable queue,
    /// timer and i/o interrupts as well as forwarding a dispatching event to a proper scheduler
    /// if required
    ///
    /// </summary>
    ///
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from halidt.asm")]
    public class ProcessorDispatcher
    {

        ///
        /// <summary>
        /// Initialize processor dispatcher
        /// </summary>
        ///
        /// <param name="schedulerToUse">Scheduler to use</param>
        ///
        [NoHeapAllocation]
        public static void StaticInitialize(Scheduler schedulerToUse)
        {
            // Initialize scheduler
            scheduler = schedulerToUse;
        }

        ///
        /// <summary>
        ///   Constructor
        /// </summary>
        ///
        internal ProcessorDispatcher()
        {
            this.id = Interlocked.Increment(ref numberOfDispatchers) - 1;

#if SHOW_TWIDDLE
            this.color = (ushort)((this.id == 0) ? 0x3a00 : 0x2a00);
#endif

            // Create stopped thread queue for processing stopped thread
            this.stoppedThreadQueue = new ThreadQueue(null);

            // Create scavanged thread queue for processing stopped thread that ready to be cleaned up
            this.scavengerThreadQueue = new ThreadQueue(null);
        }

        ///
        /// <summary>
        /// First part of the initialization of processor dispatcher
        /// </summary>
        ///
        /// <param name="myProcessor">Processor dispatcher belongs to</param>
        ///
        public void Initialize(Processor myProcessor)
        {
            // TODO: This is the wrong place for this.
            InitializeTwiddle();

            // Mark this dispatcher as active
            this.isDispatcherInUse = true;

             // Initalize procssor
            this.myProcessor = myProcessor;

            // Create an idle thread for this processor
            this.idleThread = Thread.CreateIdleThread(this.myProcessor);

            // Create a scavenger thread
            this.scavengerThread = Thread.CreateIdleThread(this.myProcessor);

            // Notify scheduler about new dispatcher
            scheduler.OnDispatcherInitialize(myProcessor.Id);
        }

        ///
        /// <summary>
        /// Finalize method
        /// </summary>
        ///
        public void Finalize()
        {
        }

        ///
        /// <summary>
        /// Check if thread index maps to idle thread
        /// </summary>
        ///
        /// <param name="threadIndex">Thread index to check if it is actually idle or not</param>
        ///
        [Inline]
        [NoHeapAllocation]
        public static bool IsIdleThread(int threadIndex) {

            // Map index to thread
            Thread thread = Thread.threadTable[threadIndex];

            // Check if thread is indeed idle thread
            return IsIdleThread(thread);
        }

        ///
        /// <summary>
        /// Check if thread is an idle thread
        /// </summary>
        ///
        /// <param name="thread">Thread to check if it is idle</param>
        ///
        [Inline]
        [NoHeapAllocation]
        internal static bool IsIdleThread(Thread thread)
        {
            return (thread != null) ? thread.IsIdle : false;
        }

        ///
        /// <summary>
        /// Check if thread is an idle thread
        /// </summary>
        ///
        /// <param name="thread">Thread to check if it is idle</param>
        ///
        [Inline]
        [NoHeapAllocation]
        internal bool IsMyIdleThread(Thread thread)
        {
            return thread == this.idleThread;
        }

        ///
        /// <summary>
        /// Check if thread is one of a dispatcher's threads
        /// </summary>
        ///
        /// <param name="thread">Thread to check if it is idle</param>
        ///
        [Inline]
        [NoHeapAllocation]
        internal bool IsOneOfMyDispatcherThreads(Thread thread)
        {
            return thread == this.scavengerThread || thread == this.idleThread;
        }

        ///
        /// <summary>
        /// Handle I/O interrupt and perform context switch if required
        /// </summary>
        ///
        [NoHeapAllocation]
        public void HandleIOReschedule()
        {
            Thread          currentThread = Processor.GetCurrentThread();
            SchedulerTime   currentTime = SchedulerTime.Now;

            // Validate preconditions
            ValidateInvariantsOnInterruptEnter(currentThread);

            // Let scheduler decide if we should run different thread
            RunScheduler(currentThread, ThreadState.Running, currentTime);

            // Validate post conditions
            ValidateInvariantsOnInterruptExit();
        }

        ///
        /// <summary>
        /// Handle timer interrupt and perform context switch if required
        /// </summary>
        ///
        /// <preconditions>
        /// Interrupts disabled
        /// Thread is not running from processor point of view
        /// </preconditions>
        ///
        [NoHeapAllocation]
        public void HandlePreemptionReschedule(HalTimer timer)
        {
            Thread          currentThread = Thread.CurrentThread;
            SchedulerTime   currentTime = SchedulerTime.Now;

            // Validate preconditions
            ValidateInvariantsOnInterruptEnter(currentThread);

            // Twiddle the thread spinner.
            Twiddle();

            // Process timer interrupt
            if (isDispatcherInUse) {
                TimeSpan delta = timer.MaxInterruptInterval;

                if (!isActingForEntireSystem) {
                    // This is the normal case, the processor is in use, notify
                    // the scheduler about timer interrupt on this processor
                    delta = NotifyTimerInterrupt(myProcessor.Id, currentTime);
                }
                else {
                    // This happens only during system shutdown where the boot processor
                    // simulates all processors, we need to notify scheduler about the
                    // timer interrupt on all virtual processors.
                    for (int id = 0; id < Processor.processorTable.Length; id++) {
                        TimeSpan next = NotifyTimerInterrupt(id, currentTime);
                        if (delta > next) {
                            delta = next;
                        }
                    }
                }

                TimeSpan start = delta;
                if (delta < timer.MinInterruptInterval) {
                    delta = timer.MinInterruptInterval;
                }
                if (delta > timer.MaxInterruptInterval) {
                    delta = timer.MaxInterruptInterval;
                }
#if false
                DebugStub.WriteLine("-- NextTimer(delta={0}, start={1} [min={2},max={3})",
                                    __arglist(delta.Ticks,
                                              start.Ticks,
                                              timer.MinInterruptInterval.Ticks,
                                              timer.MaxInterruptInterval.Ticks));
#endif
                timer.SetNextInterrupt(delta);
            }

            // Let scheduler decide if we should run different thread
            RunScheduler(currentThread, ThreadState.Running, currentTime);

            // Validate post conditions
            ValidateInvariantsOnInterruptExit();
        }

        ///
        /// <summary>
        /// Actual implementation of notifying the scheduler about the timer interrupt
        /// </summary>
        ///
        /// <param name="processorId">Id of the processor, correspond to affinity of the threads.
        /// Note during system shutdown this is virtualized.</param>
        ///
        [NoHeapAllocation]
        private TimeSpan NotifyTimerInterrupt(int processorId, SchedulerTime now)
        {
            // We need to acquire scheduler lock
            SchedulerLock schedulerLock = scheduler.RetrieveSchedulerLock(processorId);
            schedulerLock.Acquire();

            // No need to acquire scheduler lock - timer has its own lock
            TimeSpan delta = scheduler.OnTimerInterrupt(processorId, now);

            // We are done with this scheduler release its lock
            schedulerLock.Release();
            return delta;
        }

        ///
        /// <summary>
        /// Add runnable thread to runnable queue
        /// </summary>
        ///
        /// <param name="threadToAdd">Thread to add to runnable queue</param>
        ///
        /// <remark>
        /// During this operation we have to keep interrupts disabled even though we might
        /// be adding a thread to different dispatcher - the problem is if we enable interrupts we
        /// might get reschedule to the dispatcher which lock we currently holding  - that will
        /// cause definite deadlock
        /// </remark>
        ///
        [NoHeapAllocation]
        public static void AddRunnableThread(Thread threadToAdd)
        {
            // At this point we need to disable interrupts and acquire dispatcher lock:
            bool                    shouldEnable = Processor.DisableInterrupts();
            ProcessorDispatcher     dispatcher = Processor.CurrentProcessor.Dispatcher;
            Thread                  currentThread = Thread.CurrentThread;
            int                     affinity;
            int                     dispatcherIdxToActivate;
            Scheduler               scheduler = Kernel.TheScheduler;
            SchedulerLock           schedulerLock =
                                            scheduler.RetrieveSchedulerLock(threadToAdd.Affinity);

            // Validate pre conditions
            dispatcher.ValidateInvariantsOnAddRunnableThreadEnter(currentThread, threadToAdd);

            // Acquire scheduler lock
            schedulerLock.Acquire(currentThread);

            // We will use thread's affinity to find dispatcher to signal
            affinity = threadToAdd.Affinity;

            // We have protected runnable queue - now we need to call back into scheduler
            // to add thread to runnable queue
            scheduler.AddRunnableThread(threadToAdd);

            // Release scheduler lock
            schedulerLock.Release(currentThread);

            // Make sure that appropriate dispatchers are active
            if (affinity == (int)Affinity.All) {
                // Calculate next dispatcher to activate
                dispatcherIdxToActivate = GetNextDispatcherToActivate();
            }
            else {
                dispatcherIdxToActivate = affinity;
            }

            // If we are running on a dispatcher we have been asked to activate don't do anything
            if (dispatcherIdxToActivate != dispatcher.myProcessor.Id) {
                ProcessorDispatcher dispatcherToActivate =
                    Processor.processorTable[dispatcherIdxToActivate].Dispatcher;
                // During MP boot there could be race condition where the dispatcher is
                // not initialized. Activate it only if it's initialized.
                if (dispatcherToActivate != null) {
                    // During MP system shutdown, if the dispatcher is not in use, then
                    // activate the boot processor instead
                    if (dispatcherToActivate.isDispatcherInUse) {
                        dispatcherToActivate.ActivateDispatcher();
                    }
                    else {
                        Processor.processorTable[0].Dispatcher.ActivateDispatcher();
                    }
                }
            }

            // Validate post conditions: For now we can't call method when current thread is
            // the same as thread to add: It is possible that they are the same only when
            // the method is called from processor shutdown.
            if (currentThread != threadToAdd) {
                dispatcher.ValidateInvariantsOnAddRunnableThreadExit(currentThread, threadToAdd);
            }

            // Reenable interrupts
            Processor.RestoreInterrupts(shouldEnable);
        }

        ///
        /// <summary>
        /// Switch to the new thread context.
        /// </summary>
        ///
        [NoHeapAllocation]
        public static void SwitchContext(ThreadState schedulerAction)
        {
            // At this point we need to disable interrupts and acquire dispatcher lock:
            bool shouldEnable = Processor.DisableInterrupts();

            ProcessorDispatcher     dispatcher = Processor.CurrentProcessor.Dispatcher;

            // Retrieve current thread
            Thread currentThread = Thread.CurrentThread;

            // Validate pre conditions
            dispatcher.ValidateInvariantsOnSwitchContexEnter(currentThread);

            // We have protected runnable queue - now we need to call back into scheduler
            // Let scheduler decide if we should run different thread
            dispatcher.RunScheduler(currentThread, schedulerAction, SchedulerTime.MinValue);

            // STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP!
            // DON'T TRY TO ACCESS DISPATCHERS AT THIS POINTER - WE CAN BE RETURNING
            // ON DIFFERENT. DISPATCHER LOCKS SHOULD BE RELEASED BY NOW!

            // Validate post conditions
            Processor.CurrentProcessor.Dispatcher.ValidateInvariantsOnSwitchContextExit();

            Processor.RestoreInterrupts(shouldEnable);
        }

        ///
        /// <summary>
        /// Shutdown this processor as part of system shutdown. All running and runnable
        /// threads on this processor will be run on the boot processor after this.
        ///
        /// This must NOT be called on the boot processor.
        ///
        /// To avoid race conditions, the shutdown was done by letting the boot processor
        /// work with the scheduler to run all runnable threads on the system. The scheduler
        /// doesn't have any knowledge of the shutdown, ProcessorDispatcher takes care of all
        /// the necessary plumbing.
        ///
        /// See also comments on data members: isDispatcherInUse and isActingForEntireSystem.
        /// </summary>
        ///
        /// <param name="currentThread">Thread currently running </param>
        ///
        /// <remarks>This method should be called with interrupt disabled</remarks>
        ///
        [NoHeapAllocation]
        public void OnProcessorShutdown(Thread currentThread)
        {
            Scheduler   scheduler;

            // Validate preconditions
            ValidateInvariantsOnInterruptEnter(currentThread);

            // This method must not be called by the boot processor
            VTable.Assert(myProcessor.Id != 0);

            // Turn off this processor dispatcher. Once isDispatcherInUse is false,
            // all interrupts and SwitchContext calls will go directly to idle loop
            // and halt the processor
            this.isDispatcherInUse = false;

            // Add the current running thread to its scheduler's runnable queue,
            // do so only if it's not idle or scavenger thread
            if (!IsOneOfMyDispatcherThreads(currentThread)) {
                AddRunnableThread(currentThread);
            }

            // Decrement the number of active dispatchers
            int currentNumberOfDispatchers = Interlocked.Decrement(ref numberOfDispatchers);

            if (currentNumberOfDispatchers == 1) {
                // If there is only a single dispatcher activate, let the boot processor know
                // that it should now act for the entire system.
                Processor.processorTable[0].Dispatcher.isActingForEntireSystem = true;

                // The boot processor may be halted, if so wake it up.
                Processor.processorTable[0].Dispatcher.ActivateDispatcher();
            }
        }

        ///
        /// <summary>
        /// Retrieve Kernel scheduler
        /// </summary>
        ///
        public Processor Processor
        {
            [NoHeapAllocation]
            get
            {
                return this.myProcessor;
            }
        }


        ///
        /// <summary>
        /// Add threadToAdd to its scheduler's runnable queue if it's in the right state.
        /// It's possible that the thread is ready to be blocked, in which case this
        /// function call will change the thread's state to blocked and it will not be
        /// added to the runnable queue.
        /// </summary>
        ///
        /// <param name="threadToAdd">Thread to add to runnable queue</param>
        /// <param name="schedulerAction">The state of the thread</param>
        ///
        [NoHeapAllocation]
        private static void AddRunnableThreadIfRunnable(
            Thread          threadToAdd,
            ThreadState     schedulerAction)
        {
            ThreadState newState = ThreadState.Undefined;

            if (threadToAdd.ChangeSchedulerState(schedulerAction) == ThreadState.Runnable) {
                AddRunnableThread(threadToAdd);
            }
        }

        ///
        /// <summary>
        /// Run the scheduler to find a thread to run.
        /// </summary>
        ///
        /// <param name="schedulerThread">Thread that was previously running</param>
        /// <param name="schedulerAction">Whether the previously running thread is blocked</param>
        /// <param name="currentTime">Current wall clock time</param>.
        /// <returns> The thread to run next, null if there is no thread to run</returns>
        ///
        [NoHeapAllocation]
        private Thread FindSchedulerThreadToRun(
            Thread          schedulerThread,
            ThreadState     schedulerAction,
            SchedulerTime   currentTime)
        {
            Thread      threadSwitchTo = null;

            // Assert preconditions: At this point dispatcher has to be in use otherwise we in trouble
            VTable.Assert(this.isDispatcherInUse);

            // We need to consider if we are acting on behalf of all processors, so that in the process
            // of being shutdown we don't starve other schedulers
            if (!this.isActingForEntireSystem) {
                // We are running normally just try to find a thread to run
                threadSwitchTo = FindSchedulerThreadToRunInternal(
                    schedulerThread,
                    schedulerAction,
                    myProcessor.Id,
                    currentTime);
            }
            else {
                // This happens only during system shutdown where the boot processor needs
                // to simulates all processors. We need to walk all virtual processors
                // in round robin fashion to find a thread to run. Once the next thread is
                // found, this function returns, and our virtual processor position is kept
                // in nextVirtualProcessorId.
                for (int i = 0; i < Processor.processorTable.Length; i++) {
                    // simulate next processor, wrap around if we walk across the boundary
                    nextVirtualProcessorId++;
                    if (nextVirtualProcessorId == Processor.processorTable.Length) {
                        nextVirtualProcessorId = 0;
                    }

                    // Now call FindSchedulerThreadToRunInternal to find a thread to run for
                    // the virtual processor. Note that we can must pass in the current
                    // running thread exactly once.
                    Thread threadToPassIn = i == 0 ? schedulerThread : null;
                    if (threadToPassIn != null) {
                        threadToPassIn.Affinity = nextVirtualProcessorId;
                    }
                    threadSwitchTo = FindSchedulerThreadToRunInternal(
                        threadToPassIn,
                        schedulerAction,
                        nextVirtualProcessorId,
                        currentTime);

                    if (threadSwitchTo != null) {
                        break;
                    }
                }
            }

            return threadSwitchTo;
        }

        ///
        /// <summary>
        /// Actual implementation to run the scheduler to find a thread to run.
        /// </summary>
        ///
        /// <param name="schedulerThread">Thread that was previously running</param>
        /// <param name="schedulerAction">Whether the previously running thread is blocked</param>
        /// <param name="processorId">Id of the processor, correspond to affinity of the threads.
        /// Note during system shutdown this is virtualized.</param>
        /// <param name="currentTime">Current wall clock time</param>.
        /// <returns> The thread to run next, null if there is no thread to run</returns>
        ///
        [NoHeapAllocation]
        private Thread FindSchedulerThreadToRunInternal(
            Thread          schedulerThread,
            ThreadState     schedulerAction,
            int             processorId,
            SchedulerTime   currentTime)
        {
            Thread              threadSwitchTo = null;

            // Get to the scheduler lock and save it in dispatcher  - we will be releasing it
            // latter on as a part of context switch -
            SchedulerLock schedulerLock = scheduler.RetrieveSchedulerLock(processorId);

            // currentThread can be null so use implicit version to lock dispatcher
            schedulerLock.Acquire();

            // Run Scheduling policy
            threadSwitchTo = scheduler.RunPolicy(
                processorId,
                schedulerThread,
                schedulerAction,
                currentTime);

            // We are done working with this scheduler
            schedulerLock.Release();

            return threadSwitchTo;
        }

        ///
        /// <summary>
        /// Run schedulers Helper method finds actual threads to run
        /// </summary>
        ///
        /// <param name="schedulerThread">If currentThread is idle or scavenger, then
        /// schedulerThread is null, otherwise it's same as currentThread</param>
        /// <param name="schedulerAction">State of the currentThread</param>
        /// <param name="currentTime">Current wall clock time</param>.
        ///
        [NoHeapAllocation]
        private Thread ChooseThreadOrScavengerToRun(
            Thread          schedulerThread,
            ThreadState     schedulerAction,
            SchedulerTime   currentTime)
        {
           Thread       threadSwitchTo = null;

           // Assert preconditions
           VTable.Assert(this.isDispatcherInUse);

            // Run scheduling policies and find thread to run
            // Do so only if the dispatcher is in use
            do {

                // Run the scavenger if the stopped queue isn't empty.
                if (!this.stoppedThreadQueue.IsEmpty()) {
                    threadSwitchTo = this.scavengerThread;
                }
                else {
                    // Find a thread from schedulers to run
                    threadSwitchTo = FindSchedulerThreadToRun(schedulerThread,
                                                              schedulerAction,
                                                              currentTime);

                    // We no longer need current scheduler's thread
                    schedulerThread = null;

                    // If we found a thread to run we still need to check if we
                    // need to stop it right a way
                    if (threadSwitchTo != null) {

                        // Check if thread has to be stopped then stop it and get another one
                        if (!threadSwitchTo.ShouldStop()) {
                            // We found thread for running
                            break;
                        }
                        else {
                            // Enqueue stopped thread
                            EnqueueStoppedThread(threadSwitchTo);

                            // Need to retry once more
                            threadSwitchTo = null;
                        }
                    }
                    else {
                        // Well we don't have any thread to run just quit
                        break;
                    }
                }
            } while (threadSwitchTo == null);

            return threadSwitchTo;
        }

        ///
        /// <summary>
        /// Run scheduler and retrieve a thread to run
        /// </summary>
        ///
        /// <param name="currentThread">The current running thread</param>
        /// <param name="schedulerAction">State of the currentThread</param>
        /// <param name="currentTime">Current wall clock time</param>.
        ///
        [NoHeapAllocation]
        private void RunScheduler(
            Thread          currentThread,
            ThreadState     schedulerAction,
            SchedulerTime   currentTime)
        {
            Thread threadSwitchTo = null;

            // Check if we are currently running idle thread
            Thread schedulerThread
                = IsOneOfMyDispatcherThreads(currentThread) ? null : currentThread;

            // At this point current thread shouldn't be inside of context swictch - we don't allow
            // reentrancy and dispatcher has to be in use
            VTable.Assert(!currentThread.IsInsideOfContextSwitch());
            VTable.Assert(this.isDispatcherInUse);

            // Before we proceed any further mark a thread as to be inside of context switch
            // When calling into the scheduler it is possible that it will put current thread into
            // runnable queue so that other dispatcher can pick it up. By marking the thread
            // we avoid possible race condition
            currentThread.TurnOnInsideOfContextSwitch();

            // Check if we should stop current thread
            if (schedulerThread != null &&
                (schedulerAction == ThreadState.Stopped || schedulerThread.ShouldStop())) {

                // Enqueue stopped thread
                EnqueueStoppedThread(schedulerThread);

                // We no longer need current thread
                schedulerThread = null;

                //Don't forget to mark state
                schedulerAction = ThreadState.Stopped;
            }

            // Run scheduler until we either have a thread to run, or choose
            // scavenger thread or go idle
            do {
                // Mark ourselves active before we try to find a thread
                this.MarkActive();

                // Run scheduling policies to find out thread to run
                threadSwitchTo = ChooseThreadOrScavengerToRun(schedulerThread,
                                                              schedulerAction,
                                                              currentTime);

                // We can no longer use schedulerThread
                schedulerThread = null;

                // If we found a thread to run do special work to accomdate scavenger thread
                if (threadSwitchTo != null) {

                    // If we are about to run scavenger try to transfer stopped threads
                    if (threadSwitchTo == this.scavengerThread) {

                        // Transfer threads only if scavenger is done with a previous set of stopped
                        // threads - it is no longer running. Otherwise we in danger of scavenger being
                        // context switched out and its list being in inconsistent state
                        if (!this.isScavengerRunning) {

                            // Stopped thread queue can't be empty
                            VTable.Assert (!this.stoppedThreadQueue.IsEmpty());

                            // Transfer queue of stopped threads
                            this.stoppedThreadQueue.DequeueAll(this.scavengerThreadQueue);
                            this.stoppedThreadQueueLength = 0;
                        }

                        // Don't forget to indicate that scavenger thread is active
                        this.isScavengerRunning = true;
                    }
                }
                else {
                    // Try to mark ourselves idle if we fail we have to retry
                    // run scheduler: one of the scheudulers now has a thread
                    // to run
                    if (this.TryMarkIdle()) {
                        // No choice left now but the idle thread
                        threadSwitchTo = idleThread;
                    }
                }
            } while(threadSwitchTo == null);

            // Update the twiddle display.
#if SHOW_TWIDDLE
            if (threadSwitchTo != idleThread) {
                DisplayThread(color, threadSwitchTo.threadIndex);
            }
            Twiddle();
#endif

            // Perform context switch: Thread contex swich releases dispatcher lock
            SwitchThreadContextInternal(currentThread, threadSwitchTo);

           // STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP!
           // DON'T TRY TO ACCESS THIS POINTER - WE CAN BE RETURNING ON DIFFERENT
           // DISPATCHER. DISPATCHER LOCKS SHOULD BE RELEASED BY NOW!
        }

        ///
        /// <summary>
        /// Switch to the new thread context.  This works differently depending on
        /// whether we are in interrupt mode or not.
        /// </summary>
        ///
        /// <param name="currentThread">Thread we are currently executing on</param>
        /// <param name="threadSwitchTo">Thread switch to</param>
        ///
        [NoHeapAllocation]
        private void SwitchThreadContextInternal(Thread currentThread, Thread threadSwitchTo)
        {
            // Assert preconditions: currentThread and thread on the processor should be the same
            VTable.Assert(currentThread == Thread.CurrentThread);

            // If current thread is not the same as we are switching to: Proceed with the context
            // switch.
            if (threadSwitchTo != currentThread) {

                // Update statistic
                UpdateStats (currentThread, threadSwitchTo);

                // Bind dispatcher to thread and thread to dispatcher
                this.runningThread = threadSwitchTo;
                threadSwitchTo.Dispatcher = this;

                if (currentThread.context.IsRunning()) {

                    // We are running outside of interrupt context.  We cannot mark current thread
                    // as exited context switch because we are still inside of context switch
                    // SwitchTo will mark thread as outside of context switch

                    // Life is good ...
                    SwitchTo(threadSwitchTo);

                    // STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP! STOP!
                    // DON'T ADD ANY CODE HERE, AS WE COULD BE RETURNING ON DIFFERENT DISPATCHER
                    return;
                }
                else {

                    // Move over to the new thread context

                    TransferToThreadContext(ref currentThread.context,
                                            ref threadSwitchTo.context);

                }
            }
            else {

                // If we are switching to the same thread don't forget to turn off inside of context
                // switch bit
                currentThread.TurnOffInsideOfContextSwitch();
            }

            // Assert post conditions: current thread of the processor shouldn't be inside of context switch...
            VTable.Assert(!threadSwitchTo.IsInsideOfContextSwitch());
        }

        ///
        /// <summary>
        /// Transfer control from the current to a new thread context, obeying the
        /// synchronization requirements
        /// </summary>
        ///
        [NoHeapAllocation]
        internal unsafe static void TransferToThreadContext(ref ThreadContext from,
                                                            ref ThreadContext to)
        {
            // NOTE: As soon as we call TurnOffInsideOfContextSwitch,
            // we will have no valid current thread to point to; the old thread may
            // be scheduled on another processor, and the new thread may not be ready to run yet.

            // As a stopgap, we set the current target thread record to be the cpu's boot thread
            // record.  This will at least ensure that stack limit checks work.  Note
            // that we are still in a dangerous situation because of many places in the code
            // where it casts the Isal.ThreadRecord to a ThreadContext, which will not be valid.
            Isa.SetCurrentThread(ref Isa.GetCurrentCpu()->bootThread);

            // Mark current thread that it is ready to be picked up for
            // running
            from.thread.TurnOffInsideOfContextSwitch();

            // Wait until our thread is ready to be swapped in
            to.thread.WaitUntilReadyForContextSwitch();

            // Set the current thread to our new context
            Isa.SetCurrentThread(ref to.threadRecord);
        }

        ///
        /// <summary>
        /// Switch processor to this thread
        /// </summary>
        ///
        [NoHeapAllocation]
        private void SwitchTo(Thread threadSwitchTo)
        {
            Thread  currentThread = Thread.CurrentThread;
            bool    needGC;

            // Upate processor statistics
            Processor.CurrentProcessor.NumContextSwitches++;

            Monitoring.Log(Monitoring.Provider.Thread,
                           (ushort)ThreadEvent.SwitchTo, 0,
                           (uint)threadSwitchTo.context.threadIndex, 0, 0, 0, 0);

            unsafe {
                needGC = Transitions.InMutatorState(Processor.GetCurrentThreadContext());
            }

            if (needGC)
            {
                Processor.SwitchToThreadContext(ref currentThread.context,
                                                ref threadSwitchTo.context);
            }
            else
            {
                Processor.SwitchToThreadContextNoGC(ref threadSwitchTo.context);
            }
        }

        ///
        /// <summary>
        /// Try to mark dispather as idle we only can do it if we still in context switch state
        /// </summary>
        ///
        [NoHeapAllocation]
        public bool TryMarkIdle()
        {
            // Assert preconditions:
            VTable.Assert(this == Processor.CurrentProcessor.Dispatcher);

            return (int)State.Active ==
                                    Interlocked.CompareExchange (ref this.currentState,
                                              (int)State.Idle,
                                              (int)State.Active);
        }

        ///
        /// <summary>
        /// Mark dispather as active - should be always called from the thread running on
        /// dispatcher
        /// </summary>
        ///
        [NoHeapAllocation]
        public int MarkActive()
        {
            return (int)Interlocked.Exchange(ref this.currentState,
                                                (int)State.Active);
        }


        ///
        /// <summary>
        /// Try to mark dispatcher as active with request - should be always called from the thread running on
        /// dispatcher
        /// </summary>
        ///
        [NoHeapAllocation]
        public int MarkActiveWithRequest()
        {
            return  Interlocked.Exchange(ref this.currentState,
                                        (int)State.ActiveWithRequests);
        }

        ///
        /// <summary>
        /// Calculate next disaptcher to activate
        /// </summary>
        ///
        [NoHeapAllocation]
        public static int GetNextDispatcherToActivate()
        {
            int     newIdx;
            int     oldIdx;

            do {
                 oldIdx = nextDispatcherToActivate;
                 newIdx = oldIdx;

                 if (++newIdx == numberOfDispatchers) {
                    newIdx = 0;
                 }
                // Activate disaptcher first
            } while ( oldIdx != Interlocked.CompareExchange(ref nextDispatcherToActivate,
                                                            newIdx,
                                                            oldIdx));
            return newIdx;
        }

        ///
        /// <summary>
        /// Activate disaptcher - if it is idle send IPI
        /// </summary>
        ///
        [NoHeapAllocation]
        private void ActivateDispatcher()
        {
            // We only want to send IPI if previous dispatcher's state is idle
            if (MarkActiveWithRequest() == (int)State.Idle) {
                this.myProcessor.ActivateDispatcher();
            }
        }

        ///
        /// <summary>
        /// Ilde thread loop
        /// </summary>
        ///
        [NoHeapAllocation]
        public static void IdleThreadLoop()
        {
            while (true) {
                // Check for a debug break.
                bool iflag = Processor.DisableInterrupts();
                try {
                    Processor.CurrentProcessor.NextSampleIsIdle();

                    // Check if we need to break into debugger
                    if (DebugStub.PollForBreak()) {
                        DebugStub.Print("Debugger breakin.\n");
                        DebugStub.Break();
                    }
                }
                finally {
                    //Kernel.Waypoint(114);
                    Processor.RestoreInterrupts(iflag);
                }

                // Halt processor until is interrupted
                Processor processor = Processor.CurrentProcessor;
                uint statusQuo = processor.NumInterrupts;
                while (processor.NumInterrupts == statusQuo) {
                    // HaltUntilInterrupt may be a nop
                    Processor.HaltUntilInterrupt();
                }
            }
        }

        ///
        /// <summary>
        /// Scavenger thread loop
        /// </summary>
        ///
        public static void ScavengerThreadLoop()
        {
            ThreadEntry             threadEntry;
            ProcessorDispatcher     dispatcher = Processor.CurrentProcessor.Dispatcher;

            while (true) {

                // For now disable interrupts: Service thread has a lock that might
                // be problematic...
                bool iflag = Processor.DisableInterrupts();

                // Now just go through all threads and service their stop request
                while ((threadEntry = dispatcher.scavengerThreadQueue.DequeueHead()) != null) {

                    // It is possible that stopping thread is still in a process of running - wait
                    // until it stops--ready for context switch--and then stop it
                    threadEntry.Thread.WaitUntilReadyForContextSwitch();

                    // Process stopped call and go to the next one
                    ThreadLocalServiceRequest.ThreadStopped(threadEntry.Thread);

                    // Poll for possible debug break:
                    if (DebugStub.PollForBreak()) {
                        DebugStub.Print("Debugger breakin.\n");
                        DebugStub.Break();
                    }
                }

                // Reenable interrupts
                Processor.RestoreInterrupts(iflag);

                // We are done in this round.  Let's see if there is more we have to do: we will be
                // rescheduled by dispather if there is nobody to run and there are more threads
                // to clean up
                dispatcher.isScavengerRunning = false;

                SwitchContext(ThreadState.Running);
            }
        }

        ///
        /// <summary>
        /// Enqueue stopped thread
        /// </summary>
        ///
        [NoHeapAllocation]
        private void EnqueueStoppedThread(Thread currentThread)
        {
            // Change current state to stopped state
            currentThread.ChangeSchedulerState(ThreadState.Stopped);

             // At this point thread can't be on any queue
             VTable.Assert(!currentThread.schedulerEntry.Enqueued);

             // Put it on a stopped queue
             this.stoppedThreadQueue.EnqueueHead(currentThread.schedulerEntry);

             // Update queue length
             this.stoppedThreadQueueLength++;
        }

        ///
        /// <summary>
        /// Validated common invariants that should hold true for every entry point
        /// to dispatcher, except for addrunnable thred
        /// </summary>
        ///
        /// <param name="currentThread">Thread dispatcher is currently bound to"</param>
        ///
        [NoHeapAllocation]
        private void ValidateCommonInvariantsOnEnter(Thread currentThread)
        {
            // Validate processor invariants

            // Interrupts have to be disabled
            VTable.Assert(Processor.InterruptsDisabled());

            // Validate dispatcher invariants

            // Thread should belong to this dispatcher or if thread is a main kernel thread it can be null
            VTable.Assert(currentThread.Dispatcher == this ||
                          currentThread.Dispatcher == null);

            // Validate thread invariants:

            // Thread can't be inside of context switch:
            VTable.Assert(!currentThread.IsInsideOfContextSwitch());
        }

        ///
        /// <summary>
        /// Validated common invariant that should hold true for every exit point
        /// from dispatcher, except for addrunnable thred
        /// </summary>
        ///
        /// <param name="currentThread">Thread dispatcher is currently bound to"</param>
        ///
        [NoHeapAllocation]
        private void ValidateCommonInvariantsOnExit(Thread currentThread)
        {
            // Validate processor invariants

            // Interrupts have to be disabled
            VTable.Assert(Processor.InterruptsDisabled());

            // Validate dispatcher invariants

            // Thread should belong to this dispatcher or if thread is a first thread it might not
            // be bound to dispatcher even after interrupt, this can happen when after interrupt
            // thread picks up itself.
            VTable.Assert(currentThread.Dispatcher == this ||
                        currentThread.Dispatcher == null);

            // Validate thread invariants:

            // Thread can't be inside of context switch:
            VTable.Assert(!currentThread.IsInsideOfContextSwitch());
        }

        ///
        /// <summary>
        /// Validate invariants that should hold true for every entry point
        /// to dispatcher on interrupt
        /// </summary>
        ///
        /// <param name="currentThread">Thread dispatcher is currently bound to"</param>
        ///
        [NoHeapAllocation]
        private void ValidateInvariantsOnInterruptEnter(Thread currentThread)
        {
            // Validate common invariants
            ValidateCommonInvariantsOnEnter(currentThread);

            // Validate processor invariants

            // We should be on interrupt stack
            VTable.Assert(Isa.IsRunningOnInterruptStack);

            // Processor should be inside of interrupt context
            VTable.Assert(Processor.InInterruptContext);

            // Validate threads invariants

            // Thread's context can't be running from thread's context point of view
            VTable.Assert(!currentThread.context.IsRunning());
        }

        ///
        /// <summary>
        /// Validate invariants that should hold true for every exit point
        /// from dispatcher's interrupt handler
        /// </summary>
        ///
        [NoHeapAllocation]
        private void ValidateInvariantsOnInterruptExit()
        {
            Thread  currentThread = Thread.CurrentThread;

            // Validate common invariants
            ValidateCommonInvariantsOnExit(currentThread);

            // Validate processor invariants

            // We should be on interrupt stack
            VTable.Assert(Isa.IsRunningOnInterruptStack);

            // Processor should be inside of interrupt context
            VTable.Assert(Processor.InInterruptContext);

            // Validate threads invariants

            // Thread's context can't be running from thread's context point of view
            VTable.Assert(!currentThread.context.IsRunning());
        }


        ///
        /// <summary>
        /// Validate invariants that should hold true for entry point
        /// to dispatcher through SwitchContext call
        /// </summary>
        ///
        /// <param name="currentThread">Thread dispatcher is currently bound to"</param>
        ///
        [NoHeapAllocation]
        private void ValidateInvariantsOnSwitchContexEnter(Thread currentThread)
        {
            // Validate common invariants
            ValidateCommonInvariantsOnEnter(currentThread);

            // Thread's context should be running from thread's context point of view
            VTable.Assert(currentThread.context.IsRunning());
        }

        ///
        /// <summary>
        /// Validate invariants that should hold true for exit point
        /// from dispatcher's SwitchContext call
        /// </summary>
        ///
        [NoHeapAllocation]
        private void ValidateInvariantsOnSwitchContextExit()
        {
            Thread currentThread = Thread.CurrentThread;

           // Validate common invariants
            ValidateCommonInvariantsOnExit(currentThread);

            // Thread's context should be running from thread's context point of view
            VTable.Assert(currentThread.context.IsRunning());
        }

        ///
        /// <summary>
        /// Validate invariants that should hold true for entry point
        /// to dispatcher through AddRunnableThread call
        /// </summary>
        ///
        /// <param name="currentThread">Thread dispatcher is currently bound to"</param>
        ///
        [NoHeapAllocation]
        private void ValidateInvariantsOnAddRunnableThreadEnter(
            Thread  currentThread,
            Thread  newThread)
        {
            // Validate processor invariants:

            // Interrupts have to be disabled
            VTable.Assert(Processor.InterruptsDisabled());

            // Validate dispatcher invariants

            // Thread should belong to this dispatcher or if thread is a kernel thread it can be null
            VTable.Assert(currentThread.Dispatcher == this ||
                        currentThread.Dispatcher == null);

            // Validate thread invariants:

            // Threads can't be inside of context switch:
            VTable.Assert(!currentThread.IsInsideOfContextSwitch());

            // New thread can't be a dispatcher thread
            VTable.Assert(!IsIdleThread(newThread));
        }

        ///
        /// <summary>
        /// Validate invariants that should hold true for entry point
        /// from dispatcher's AddRunnableThread call. At this point we can't make any
        /// assumptions about new thread
        /// </summary>
        ///
        /// <param name="currentThread">Thread dispatcher is currently bound to"</param>
        ///
        [NoHeapAllocation]
        private void ValidateInvariantsOnAddRunnableThreadExit(
            Thread  currentThread,
            Thread  newThread)
        {

            // Interrupts have to be disabled
            VTable.Assert(Processor.InterruptsDisabled());

            // Validate dispatcher invariants

            // Thread should belong to this dispatcher or if thread is a main kernel thread it can be null
            VTable.Assert(currentThread.Dispatcher == this ||
                        currentThread.Dispatcher == null);

            // Validate thread invariants:

            // Current thread can't be inside of context switch
            VTable.Assert(!currentThread.IsInsideOfContextSwitch());

        }

        ///
        /// <summary>
        /// Assert that we are running on the processor we are thinking we are running on
        /// </summary>
        ///
        [Conditional("DEBUG")]
        [NoHeapAllocation]
        public void AssertCurrentProcessor(int cpu)
        {
            VTable.Assert(Processor.GetCurrentProcessorId() == cpu);
        }

        ///
        /// <summary>
        /// Record debugging event
        /// </summary>
        ///
        /// <param name="currentThread">Current thread</param>
        /// <param name="threadSwitchTo">Thread we are switchint to</param>
        ///
        [Inline]
        [NoHeapAllocation]
        private void UpdateStats(Thread currentThread, Thread threadSwitchTo)
        {
#if THREAD_TIME_ACCOUNTING

                ulong now_a = this.mProcessor.CycleCount;

                currentThread.context.executionTime += now_a -
                  currentThread.context.lastExecutionTimeUpdate;

                threadSwitchTo.context.lastExecutionTimeUpdate = now_a;
#endif
        }

        private static unsafe void InitializeTwiddle()
        {
#if SHOW_TWIDDLE
            if (Platform.ThePlatform.TwiddleSpinBase != 0) {
                // [pbar] Scheduler visualization hack
                // we use unsafe access to minimize the scheduler overhead.
                screenMem = IoMemory.MapPhysicalMemory(0xb8000, 80*50*2, true, true);
                screenPos = 0;
                screenPtr = (ushort *)screenMem.VirtualAddress;
                tpos = 0;
            }
#endif
        }

        [Inline]
        [NoHeapAllocation]
        private static unsafe void DisplayThread(ushort color, int id)
        {
#if SHOW_TWIDDLE
            if (screenPtr != null) {
                screenPtr[screenPos] = (ushort)(color | ('@' + id));
                screenPos = (screenPos + 1) % 80;
            }
#endif
        }

        [Inline]
        [NoHeapAllocation]
        private static unsafe void Twiddle()
        {
#if SHOW_TWIDDLE
            if (screenPtr != null) {
                ushort twiddle;
                switch (tpos) {
                    default:
                    case 0: twiddle = '|'; break;
                    case 1: twiddle = '/'; break;
                    case 2: twiddle = '-'; break;
                    case 3: twiddle = '\\'; break;
                }
                screenPtr[screenPos] = (ushort)(0xe000 | twiddle);
                tpos = ++tpos & 3;
            }
#endif
        }

        ///
        /// <summary>
        /// Affinity consts states
        /// </summary>
        ///
        internal enum Affinity
        {
            All = -1
        }

        ///
        /// <summary>
        /// Dispatcher State
        /// </summary>
        ///
        private enum State
        {
            Halted,
            Idle,
            ActiveWithRequests,
            Active
        };

        /// <summary>
        /// True if the processor is in use, including halted during idle.
        /// False only if the processor is down during system shutdown.
        /// </summary>
        private bool                        isDispatcherInUse;

        /// <summary>
        /// True only on boot processor during shutdown when all other processors are down
        /// </summary>
        private bool                        isActingForEntireSystem;

        /// <summary>
        /// Only used when isActingForEntireSystem is true, the next processorId to simulate
        /// </summary>
        private int                         nextVirtualProcessorId;

        /// <summary>Number of dispatchers in the system</summary>
        private static int                  numberOfDispatchers = 0;

        /// <summary> Next dispatcher to activate </summary>
        private static int                  nextDispatcherToActivate;

        /// <summary>Threre is a single dispatch lock per processor dispatcher</summary>
        private static Scheduler            scheduler;

        /// <summary>Dispatcher Id</summary>
        private int                         id;

        /// <summary> Processor object to which dispatcher is bound </summary>
        private Processor                   myProcessor;

        /// <summary> Thread queue is used to collect stopped threads </summary>
        private ThreadQueue                 stoppedThreadQueue;

        /// <summary>Length of the stopped thread queue</summary>
        private int                         stoppedThreadQueueLength = 0;

        /// <summary>Length of the stopped thread queue</summary>
        private const int                   maxStoppedThreadQueueLength = 64;

        /// <summary> Thread queue is used to scavanged stopped threads </summary>
        private ThreadQueue                 scavengerThreadQueue;

        /// <summary> A pool of idle thread used by dispatcher </summary>
        private Thread                      idleThread;

        /// <summary> A dispatcher helper thread that is performing scavanging and other types of work </summary>
        private Thread                      scavengerThread;

        /// <summary> A current thread currently running on the processor </summary>
        private Thread                      runningThread;

        /// <summary> State of the dispatcher - (idle, halted, running) </summary>
        private int                         currentState = (int) State.Active;

        /// <summary> State of scavenger thread </summary>
        private bool                        isScavengerRunning;

#if SHOW_TWIDDLE
        //; <summary> Memory Interface to allocate physical memory<summary>
        private static IoMemory             screenMem;

        /// <summary> Possition twiddle on the screen</summary>
        private static int                  screenPos;

        /// <summary>Virtual address of the screen memory</summary>
        private static unsafe ushort *      screenPtr;

        /// <summary> Current possition inside of array</summary>
        private static int                  tpos;

        private ushort                      color;
#endif

    }
}
