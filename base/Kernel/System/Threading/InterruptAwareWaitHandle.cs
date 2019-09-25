// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;
using Microsoft.Singularity.Scheduling;

namespace System.Threading
{
    ///
    /// <summary>
    /// Base class for all interrupt aware synchronization objects
    ///
    /// This class is interrupt aware: interrupts are disabled during the period when the
    /// spin lock is held.
    /// </summary>
    ///
    [NoCCtor]
    [CLSCompliant(false)]
    public abstract class InterruptAwareWaitHandle : WaitHandleBase
    {
        ///
        /// <summary>
        /// Constructor
        /// </summary>
        ///
        /// <param name="initialState">Initial state of an handle </param>
        /// <param name="signalStateAfterImediateWait">
        ///    Value represents a state of a handle when wait satisfied right a way
        /// </param>
        /// <param name="spinLockType">The spin lock type of the wait handle</param>
        ///
        protected InterruptAwareWaitHandle(
            SignalState     initialState,
            SignalState     signalStateAfterImediateWait,
            SpinLock.Types  spinLockType)
            : base(initialState, signalStateAfterImediateWait)
        {
            this.singleHandle = new InterruptAwareWaitHandle[1] { this };
            // Initialize waithandle spinlock
            this.myLock = new SpinLock(spinLockType);
        }

        ///
        /// <summary>
        /// Signal wait handle by waking up a single waiter or if there are no waiters
        /// set handle to specified stated.
        /// </summary>
        ///
        /// <param name="signalStateIfNoWaiters">
        /// Set the wait handle into specified state if no waiters present
        /// </param>
        ///
        [NoHeapAllocation]
        protected void InterruptAwareSignalOne(SignalState signalStateIfNoWaiters)
        {
            // Disable interrupt
            bool interruptFlag = Processor.DisableInterrupts();

            // Single a waiting thread and put it in the deferredWakeupQueue
            ThreadQueueStruct deferredWakeupQueue = SignalOneWithNoWakeup(signalStateIfNoWaiters);

            // Restore interrupt if necessary
            Processor.RestoreInterrupts(interruptFlag);

            // Wakeup a waiter if we need to
            WakeupOneWaiter(deferredWakeupQueue);
        }

        ///
        /// <summary>
        /// Associate a thread with wait handles if one of the waits satisfied return
        /// waithandle id - actual unblocker. if none of the states satisfied return UninitWait
        /// indicating that thread has to proceede with blocking
        /// </summary>
        ///
        private static int InterruptAwarePreWaitAnyInternal(
            Thread currentThread,
            WaitHandleBase[] waitHandles,
            ThreadEntry[] entries,
            int waitHandlesCount)
        {
            // Disable interrupt
            bool interruptFlag = Processor.DisableInterrupts();

            int unblockedBy = PreWaitAnyInternal(
                currentThread,
                waitHandles,
                entries,
                waitHandlesCount);

            // Restore interrupt
            Processor.RestoreInterrupts(interruptFlag);

            return unblockedBy;
        }

        ///
        /// <summary>
        /// Post wait is to disassociate thread from all handlers
        /// </summary>
        ///
        protected static void InterruptAwarePostWaitAnyInternal(
            Thread currentThread,
            WaitHandleBase[] waitHandles,
            ThreadEntry[] entries,
            int waitHandlesCount)
        {
            // Disable interrupt
            bool interruptFlag = Processor.DisableInterrupts();

            PostWaitAnyInternal(currentThread, waitHandles, entries, waitHandlesCount);

            // Restore interrupt
            Processor.RestoreInterrupts(interruptFlag);
        }

        ///
        /// <summary>
        /// Wait on a set of handles until one of them becomes signaled with a specified time out.
        ///
        /// !!! If you change this method, please review WaitHandle.WaitAny()
        /// and see if the changes need to be propagated there.
        /// </summary>
        ///
        public void InterruptAwareWaitOne()
        {
            // Retrieve current thread information
            Thread currentThread = Thread.CurrentThread;
            Thread target = null;
            int unblockedBy;
            ThreadEntry[] entries = currentThread.GetWaitEntries(1);

            // Before we attempting to enqueue ourselves into the wait queues make sure
            // we disable abort
            currentThread.DelayStop(true);

            // Perepare for a wait - enqueue ourselves into every wait handle
            unblockedBy = InterruptAwarePreWaitAnyInternal(currentThread, singleHandle, entries, 1);

            // If we are in the process of blocking: Block
            if (UninitWait == unblockedBy) {
                // Allow thread to be aborted at this point
                currentThread.DelayStop(false);

                // Write out log record
                Monitoring.Log(Monitoring.Provider.Thread,
                                   (ushort)ThreadEvent.WaitAny, 0, 0, 0,
                                   (uint)currentThread.threadIndex, 0, 0);


                // Let scheduler know that we are blocking
                Kernel.TheScheduler.OnThreadBlocked(currentThread, SchedulerTime.MaxValue);

                // Our thread is about to run so we can disassociate it from wait handles
                InterruptAwarePostWaitAnyInternal(currentThread, singleHandle, entries, 1);

                // Thread has the unblocked information
                unblockedBy = currentThread.UnblockedBy;
            }

            // Assert post condition: since there is no timeout, and we are waiting
            // on a single handle, the unblockedBy must be 0
            VTable.Assert(unblockedBy == 0);

            // Complete wait
            CompleteWait(currentThread);

            // When we were signalged delay abort has been set - now we can turn it off
            // For mutex complete wait will add delay abort. It will remain on until
            // mutex is released
            currentThread.DelayStop(false);

            // Make sure that we pay attention to abort
            currentThread.ProcessAbortIfRequired();
        }

        /// <summary>
        /// This field is an array of length 1 containing 'this'.
        /// It is used to avoid allocation when calling WaitAny from WaitOne.
        /// </summary>
        private InterruptAwareWaitHandle[] singleHandle;
    }
}
