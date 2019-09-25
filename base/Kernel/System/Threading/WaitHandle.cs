// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

using System;
using System.Threading;
using System.Runtime.CompilerServices;
using System.Collections;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Scheduling;

namespace System.Threading
{
    ///
    /// <summary>
    /// Base class for all synchronization objects such as events and mutex
    /// </summary>
    ///
    [NoCCtor]
    [CLSCompliant(false)]
    public abstract class WaitHandle : WaitHandleBase
    {
        ///
        /// <summary>
        /// Constructor
        /// </summary>
        ///
        /// <param name="initialState">Initial state of an handle </param>
        /// <param name="signalStateAfterImediateWait">
        ///  Value represents a state of a handle when wait satisfied right a way
        /// </param>
        /// <param name="spinLockType">The spin lock type of the wait handle</param>
        ///
        protected WaitHandle(
            SignalState     initialState,
            SignalState     signalStateAfterImediateWait,
            SpinLock.Types  spinLockType)
            : base(initialState, signalStateAfterImediateWait)
        {
            this.singleHandle = new WaitHandle[1] { this };
            // Initialize waithandle spinlock
            this.myLock = new SpinLock(spinLockType);
        }

        ///
        /// <summary>
        /// Wait on a handle with a specified time out.
        /// </summary>
        ///
        /// <param name="timeout">Time out </param>
        ///
        public bool WaitOne(TimeSpan timeout)
        {
            return (WaitAny(singleHandle, 1, timeout) != WaitTimeout);
        }

        ///
        /// <summary>
        /// Wait on a handle with a specified time out.
        /// </summary>
        ///
        /// <param name="stop">Time out </param>
        ///
        internal bool WaitOne(SchedulerTime stop)
        {
            return (WaitAny(singleHandle, 1, stop) != WaitTimeout);
        }

        ///
        /// <summary>
        /// Wait on a handle without time out
        /// </summary>
        ///
        public bool WaitOne()
        {
            return WaitOne(SchedulerTime.MaxValue);
        }

        ///
        /// <summary>
        /// Wait on a set of handles until one of them becomes signaled with a specified time out.
        /// </summary>
        ///
        /// <param name="waitHandles">Wait handles to wait on </param>
        /// <param name="timeout">Time out </param>
        ///
        public static int WaitAny(WaitHandle[] waitHandles, TimeSpan timeout)
        {
            SchedulerTime stop = SchedulerTime.Now + timeout;
            return WaitAny(waitHandles, waitHandles.Length, stop);
        }

        ///
        /// <summary>
        /// Wait on a set of handles until one of them becomes signaled with a specified time out.
        /// </summary>
        ///
        /// <param name="waitHandles">Wait handles to wait on </param>
        /// <param name="stop">Time out </param>
        ///
        public static int WaitAny(WaitHandle[] waitHandles, SchedulerTime stop)
        {
            return WaitAny(waitHandles, waitHandles.Length, stop);
        }

        ///
        /// <summary>
        /// Wait on a set of handles until one of them becomes signaled without timeout.
        /// </summary>
        ///
        /// <param name="waitHandles">Wait handles to wait on </param>
        ///
        public static int WaitAny(WaitHandle[] waitHandles)
        {
            return WaitAny(waitHandles, SchedulerTime.MaxValue);
        }

        ///
        /// <summary>
        /// Wait on a set of handles until one of them becomes signaled with a specified time out.
        /// </summary>
        ///
        /// <param name="waitHandles">Wait handles to wait on </param>
        /// <param name="waitHandlesCount">A number of wait handles to wait on </param>
        /// <param name="timeout">Time out </param>
        ///
        public int WaitAny(
            WaitHandle[]    waitHandles,
            int             waitHandlesCount,
            TimeSpan        timeout)
        {
            SchedulerTime stop;

            if (timeout != TimeSpan.MaxValue) {
                stop = SchedulerTime.Now + timeout;
            }
            else {
                stop = SchedulerTime.MaxValue;
            }
            return WaitAny(waitHandles, waitHandlesCount, stop);
        }

        ///
        /// <summary>
        /// Wait on a set of handles until one of them becomes signaled with a specified time out.
        /// </summary>
        ///
        /// <param name="waitHandles">Wait handles to wait on </param>
        /// <param name="waitHandlesCount">A number of wait handles to wait on </param>
        /// <param name="stop">Time out </param>
        ///
        public static int WaitAny(
            WaitHandle[]        waitHandles,
            int                 waitHandlesCount,
            SchedulerTime       stop)
        {
            // Retrieve current thread information
            Thread                  currentThread = Thread.CurrentThread;
            Thread                  target = null;
            int                     unblockedBy;
            ThreadEntry[]           entries = currentThread.GetWaitEntries(
                                                               waitHandlesCount);

            // Before we attempting to enqueue ourselves into the wait queues make sure
            // we disable abort
            currentThread.DelayStop(true);

            // Perepare for a wait - enqueue ourselves into every wait handle
            unblockedBy = PreWaitAnyInternal(currentThread,
                                             waitHandles,
                                             entries,
                                             waitHandlesCount);

            // If we are in the process of blocking: Block
            if (UninitWait == unblockedBy) {
                // Allow thread to be aborted at this point
                currentThread.DelayStop(false);

                // Update thread WaitFor information: Indicate every one that we waiting -
                // scheduler ones wakes us up is responsible for cleaning up wait information
                // by using ResetWaitInfo call
                //currentThread.UpdateWaitInfo (waitHandles,
                //                        waitHandlesCount,
                //                        entries,
                //                        stop);  

                // Write out log record
                Monitoring.Log(Monitoring.Provider.Thread,
                               (ushort)ThreadEvent.WaitAny, 0,
                               (uint)stop.Ticks, (uint)(stop.Ticks >> 32),
                               (uint)currentThread.threadIndex, 0, 0);


                // Let scheduler know that we are blocking
                Kernel.TheScheduler.OnThreadBlocked(currentThread, stop);

                // Our thread is about to run so we can disassociate it from wait handles
                PostWaitAnyInternal(currentThread,
                                 waitHandles,
                                 entries,
                                 waitHandlesCount);

                // Thread has the unblocked information
                unblockedBy = currentThread.UnblockedBy;
           }

           // Assert post condition: unblocked by can't be uninitialized
           VTable.Assert(unblockedBy != WaitHandle.UninitWait);

            // If there are wait handles and we were unblocked by not the timeout
            if (waitHandles != null && unblockedBy >= 0
                                 && unblockedBy < waitHandlesCount) {
               // Complete wait
               waitHandles[unblockedBy].CompleteWait (currentThread);

               // When we were signalged delay abort has been set - now we can turn it off
               // For mutex complete wait will add delay abort. It will remain on until
               // mutex is released
               currentThread.DelayStop(false);
            }

            // Make sure that we pay attention to abort
            currentThread.ProcessAbortIfRequired();

           return unblockedBy;
        }

        ///
        /// <summary>
        /// Signal wait handle by waking up a single waiter or if there are no waiters
        /// set handle to specified stated
        /// </summary>
        ///
        /// <param name="signalStateIfNoWaiters">
        /// Set the wait handle into specified state if no waiters   present
        /// </param>
        ///
        [NoHeapAllocation]
        protected void SignalOne(SignalState signalStateIfNoWaiters)
        {
            // Single a waiting thread and put it in the deferredWakeupQueue
            ThreadQueueStruct deferredWakeupQueue = SignalOneWithNoWakeup(signalStateIfNoWaiters);

            // Wakeup a waiter if we need to
            WakeupOneWaiter(deferredWakeupQueue);
        }

        ///
        /// <summary>
        /// Signal wait handle by waking up all waiters. Set wait handle into specified state
        /// in both cases when waiters present and not
        /// </summary>
        ///
        /// <param name="signalStateIfNoWaiters">
        /// Set the wait handle into specified state if no waiters present
        /// </param>
        ///
        /// <param name="signalStateIfWaiters">
        /// Set the wait handle into specified state if waiter are present
        /// </param>
        ///
        [NoHeapAllocation]
        protected void SignalAll(
            SignalState     signalStateIfNoWaiters,
            SignalState     signalStateIfWaiters)
        {
            // Single the waiting threads and put them in the deferredWakeupQueue
            ThreadQueueStruct deferredWakeupQueue = SignalAllWithNoWakeup(
                signalStateIfNoWaiters,
                signalStateIfWaiters);

            // Wakeup a waiter if we need to
            WakeupAllWaiters(deferredWakeupQueue);
        }

        /// <summary>
        /// This field is an array of length 1 containing 'this'.
        /// It is used to avoid allocation when calling WaitAny from WaitOne.
        /// </summary>
        private WaitHandle[] singleHandle;
    }

    ///
    /// <summary>
    /// Base class for all synchronization objects such as events and mutex
    /// </summary>
    ///
    [NoCCtor]
    [CLSCompliant(false)]
    public abstract class WaitHandleBase
    {
        /// <summary > Time out constant</summary>
        public const int WaitTimeout = -1;

        /// <summary > Time out constant</summary>
        public const int UninitWait = -2;

        /// <summary> Infinite time out </summary>
        public const int InfinityTimeout = -1;

        /// <summary> GC uses this for unblocked by information </summary>
        public const int UnblockedByGC = -3;

        /// <summary> Unblocked by abort </summary>
        public const int UnblockedByAbort = -4;

        /// <summary> The state of the handle, signaled or unsignaled </summary>
        protected enum SignalState : int
        {
            Unsignaled = 0,
            Signaled = 1,
        }

        ///
        /// <summary>
        /// Constructor
        /// </summary>
        ///
        /// <param name="initialState">Initial state of an handle </param>
        /// <param name="signalStateAfterImediateWait">
        ///    Value represents a state of a handle when wait satisfied right a way
        /// </param>
        ///
        protected WaitHandleBase(
            SignalState     initialState,
            SignalState     signalStateAfterImediateWait)
        {
            this.id = ++idGenerator;
            this.owner = null;
            this.signaledQueue = new ThreadQueue(this);
            this.waitingQueue = new ThreadQueue(this);
            this.signaled = initialState;
            this.signalStateAfterImediateWait = signalStateAfterImediateWait;
        }

        ///
        /// <summary>
        /// Perform the work to signal wait handle or if there are no waiters
        /// set handle to specified stated. Put the signaled waiter to a deferred
        /// wakeup queue if there is any and return the queue.
        /// </summary>
        ///
        /// <param name="signalStateIfNoWaiters">
        /// Set the wait handle into specified state if no waiters present
        /// </param>
        ///
        [Inline]
        [NoHeapAllocation]
        protected ThreadQueueStruct SignalOneWithNoWakeup(SignalState signalStateIfNoWaiters)
        {
            Thread              currentThread = Thread.CurrentThread;
            ThreadEntry         nextThreadEntry;
            ThreadEntry         waitDoneThreadEntry;
            int                 unblockerId = UninitWait;
            int                 entryId = UninitWait;

            // The method below should allocate struct on the stack!!
            ThreadQueueStruct   deferredWakeupQueue = new ThreadQueueStruct();

            bool shouldEnable = Processor.DisableInterrupts();
            myLock.Acquire(currentThread);
            try {
                // Acquire lock. If you hit assert during acquire, and the code is handling
                // interrupt, you may need to use interrupt aware synchronization classes.
                // See the comment for  InterruptAwareAutoResetEvent, InterruptAwareManualResetEvent,
                // and InterruptAwareMutex for details.

                ThreadEntryEnum threadEntryEnum = new ThreadEntryEnum(this.waitingQueue.Head);
                nextThreadEntry = threadEntryEnum.GetNext();

                // Waitdone can move entry from one queue to another. Because of that we have
                // to be extremly careful. We move enumerator always one step ahead.
                if (nextThreadEntry != null) {

                    do {
                        waitDoneThreadEntry = nextThreadEntry;
                        entryId = waitDoneThreadEntry.Id;

                        // Move enumerator one step further - we have to do it before we call
                        // WaitDone otherwise we might be enumerating wrong list because entry
                        // can move lists during WaitDone call
                        nextThreadEntry = threadEntryEnum.GetNext();

                        // Perform actual signal
                        unblockerId = WaitDone(waitDoneThreadEntry,
                                               entryId,
                                               ref deferredWakeupQueue);

                        // We will need to loop until we have an entry that we succefully signalled
                    } while (entryId != unblockerId && nextThreadEntry != null);
                }

                // If we succesfully process signal mark state appropriately
                if (unblockerId != UninitWait && (entryId == unblockerId)) {

                    // Make sure that state is no longer signalled
                    this.signaled = SignalState.Unsignaled;
                }
                else {
                    // Set state to specified by caller
                    signaled = signalStateIfNoWaiters;
                }
            }
            finally {
                // Release lock
                myLock.Release();

                // Reenable interrupts
                Processor.RestoreInterrupts(shouldEnable);
            }

            return deferredWakeupQueue;
        }

        ///
        /// <summary>
        /// Wakeup a single waiter in the deferred queue if there is one.
        /// </summary>
        ///
        /// <param name="deferredWakeupQueue">The queue that contains the waiter thread</param>
        ///
        [Inline]
        [NoHeapAllocation]
        protected static void WakeupOneWaiter(ThreadQueueStruct deferredWakeupQueue)
        {
            // Wakeup a waiter if we need to
            if (!deferredWakeupQueue.IsEmpty()) {

                // Retrieve thread from deferred queue
                Thread threadToWakeup = deferredWakeupQueue.DequeueHead().Thread;

                // Add the unblocked thread to the scheduler's runnable queue
                Kernel.TheScheduler.OnThreadUnblocked(threadToWakeup);

                // At this point queue should be empty!
                VTable.Assert(deferredWakeupQueue.IsEmpty());
            }
        }

        ///
        /// <summary>
        /// Perform the work to signal all waiters and then set handle to specified stated.
        /// Put the signaled waiters to a deferred wakeup queue if there is any and
        /// return the queue.
        /// </summary>
        ///
        /// <param name="signalStateIfNoWaiters">
        /// Set the wait handle into specified state if no waiters present
        /// </param>
        ///
        /// <param name="signalStateIfWaiters">
        /// Set the wait handle into specified state if waiter are present
        /// </param>
        ///
        [NoHeapAllocation]
        protected ThreadQueueStruct SignalAllWithNoWakeup(
            SignalState signalStateIfNoWaiters,
            SignalState signalStateIfWaiters)
        {
            bool                notified = false;
            Thread              currentThread = Thread.CurrentThread;
            ThreadEntry         waitDoneThreadEntry;
            ThreadEntry         nextThreadEntry;
            ThreadQueueStruct   deferredWakeupQueue = new ThreadQueueStruct();
            int                 unblockerId = UninitWait;
            int                 numberOfUnblockedWaiters = 0;
            int                 entryId = UninitWait;

            // Acquire lock. If you hit assert during acquire, and the code is handling
            // interrupt, you may need to use interrupt aware synchronization classes.
            // See the comment for  InterruptAwareAutoResetEvent, InterruptAwareManualResetEvent,
            // and InterruptAwareMutex for details.
            bool shouldEnable = Processor.DisableInterrupts();
            myLock.Acquire(currentThread);
            try {
                ThreadEntryEnum threadEntryEnum = new ThreadEntryEnum(this.waitingQueue.Head);
                nextThreadEntry = threadEntryEnum.GetNext();

                // Waitdone can move entry from one queue to another. Because of that we have
                // to be extremly careful. We move enumerator always one step ahead.
                if (nextThreadEntry != null) {

                    do {
                        waitDoneThreadEntry = nextThreadEntry;
                        entryId = waitDoneThreadEntry.Id;

                        // Move enumerator one step further - we have to do it before we call
                        // WaitDone otherwise we might be enumerating wrong list because entry
                        // can move lists during WaitDone call
                        nextThreadEntry = threadEntryEnum.GetNext();

                        // We are ready to call waitdone
                        unblockerId = WaitDone(waitDoneThreadEntry,
                                               entryId,
                                               ref deferredWakeupQueue);

                        // Remember if we succesfully signalled someone
                        if (unblockerId == entryId) {
                            numberOfUnblockedWaiters++;
                        }

                    } while (nextThreadEntry != null);
                }

                // If we succesfully signalled someone, record state accordingly
                if (numberOfUnblockedWaiters > 0) {

                    // Update signal state in case when waiters are present
                    this.signaled = signalStateIfWaiters;
                }
                else {
                    // Don't forget to update state when waiters are not present
                    this.signaled = signalStateIfNoWaiters;
                }
            }
            finally {
                // Release lock
                myLock.Release();

                // Reenable interrupts
                Processor.RestoreInterrupts(shouldEnable);
            }

            return deferredWakeupQueue;
        }

        ///
        /// <summary>
        /// Wakeup all waiters in the deferred queue if there are any
        /// </summary>
        ///
        /// <param name="deferredWakeupQueue">The queue that contains the waiter threads</param>
        ///
        [Inline]
        [NoHeapAllocation]
        protected static void WakeupAllWaiters(ThreadQueueStruct deferredWakeupQueue)
        {
            ThreadEntry entryToWakeup;

            // Unblock threads that we found we need to unblock
            while ((entryToWakeup = deferredWakeupQueue.DequeueHead()) != null) {

                // Get the thread
                Thread threadToWakeup = entryToWakeup.Thread;

                // Add the unblocked thread to the scheduler's runnable queue
                Kernel.TheScheduler.OnThreadUnblocked(threadToWakeup);
            }
        }

        ///
        /// <summary>
        /// Depending on the state of a handle decide either to acquire handle or wait
        /// </summary>
        ///
        /// <param name="entry">
        /// Thread entry to enqueu onto waiting queue when can't satisfy request
        /// </param>
        /// <param name="handleId">
        /// Id of the handle that we are trying to acquire - is used to check if thread can be unblocked
        /// </param>
        ///
        [NoHeapAllocation]
        protected virtual bool AcquireOrEnqueue(ThreadEntry entry, int handleId)
        {
            bool didAcquire = true;
            Thread currentThread = Thread.CurrentThread;

            // Acquire lock. If you hit assert during acquire, and the code is handling
            // interrupt, you may need to use interrupt aware synchronization classes.
            // See the comment for  InterruptAwareAutoResetEvent, InterruptAwareManualResetEvent,
            // and InterruptAwareMutex for details.
            bool shouldEnable = Processor.DisableInterrupts();
            myLock.Acquire(currentThread);
            try {
                // If the handle is signaled and thread hasn't been unblocked yet.
                if ((this.signaled == SignalState.Signaled) &&
                    (currentThread.Unblock(handleId) == handleId)) {

                    // Make signaled state to be as dictated by child class during initialization
                    this.signaled = this.signalStateAfterImediateWait;
                }
                else {
                    // Enqueue entry into wating queue:
                    this.waitingQueue.EnqueueHead(entry);

                    // We couldn't acquire object set return value properly
                    didAcquire = false;
                }
            }
            finally {
                // Release lock
                myLock.Release();

                // Reenable interrupts
                Processor.RestoreInterrupts(shouldEnable);
            }

            return didAcquire;
        }

        ///
        /// <summary>
        /// Associate a thread with wait handles if one of the waits satisfied return
        /// waithandle id - actual unblocker. if none of the states satisfied return UninitWait
        /// indicating that thread has to proceede with blocking
        /// </summary>
        ///
        protected static int PreWaitAnyInternal(
            Thread           currentThread,
            WaitHandleBase[] waitHandles,
            ThreadEntry[]    entries,
            int              waitHandlesCount)
        {
            int marked;
            int released;
            int unblockedBy = UninitWait;

            VTable.Assert(currentThread.ThreadState == ThreadState.Running);

            // Prepare thread for blocking - Unblock call might be called from
            // either AcquireOrEnqueue or from WaitDone
            currentThread.PrepareForBlocking();

            // Enqueue on all of the non-signaled handles.
            for (marked = 0; marked < waitHandlesCount; marked++) {

                // Initialize entry id
                entries[marked].Id = marked;

                // Attempt to wait on a handler
                if (waitHandles[marked].AcquireOrEnqueue(entries[marked], marked)) {

                    // Our wait succeeded, remove ourselves from the wait queues
                    for (released = 0; released < marked; released++) {
                        waitHandles[released].Remove(entries[released]);
                    }

                    // Remember unblockedBy
                    unblockedBy = currentThread.UnblockedBy;
                    break;
                }
            }

            return unblockedBy;
        }

        ///
        /// <summary>
        /// Post wait is to dissasociate thread from all handlers
        /// </summary>
        ///
        protected static void PostWaitAnyInternal(
            Thread           currentThread,
            WaitHandleBase[] waitHandles,
            ThreadEntry[]    entries,
            int              waitHandlesCount)
        {
            ThreadState     state;
            int             handlerIdx;
            int             unblockedBy = WaitHandle.WaitTimeout;
            int             resultUnblockedBy = WaitHandle.WaitTimeout;

            VTable.Assert(currentThread.ThreadState == ThreadState.Running);

            // Dequeue a thread from all hadndles it was waiting on
            for (handlerIdx = 0; handlerIdx < waitHandlesCount; handlerIdx++) {
                // Dissaociate handler from entry
                waitHandles[handlerIdx].Remove(entries[handlerIdx]);
            }
        }

        ///
        /// <summary>
        /// This method is called when a synchronization object completes the wait for
        /// thread.
        /// </summary>
        ///
        /// <param name="entry">Thread entry to signal</param>
        /// <param name="handleId">Id of wait handle</param>
        /// <param name="deferredQueue">Deferred queue to use for deferred wakeup</param>
        ///
        [NoHeapAllocation]
        private int WaitDone(
            ThreadEntry             entry,
            int                     handleId,
            ref ThreadQueueStruct   deferredQueue)
        {
            ThreadState     state;
            int             handledIdUnblocked;

            // Assert preconditions: We assume that queues are stable - spinlock is held when
            // this method is called
            VTable.Assert(myLock.IsHeldBy(Thread.CurrentThread));

            // Indicate that thread migth be given owrneship of the object so that it can't be aborted
            entry.Thread.DelayStop(true);

            //Attempt to unblock thread, if we fail it means that thread has already timed out
            // If thread has timed out don't move it to signaled queue
            if ((handledIdUnblocked = entry.Thread.Unblock(handleId)) == handleId) {

                // The signal is good-we can take a thread from non-signaled queue and
                // move it to signaled
                MoveEntryToSignalQueue(entry);

                // If thread state is blocked - we will be responsible for waking it up
                if (entry.Thread.ShouldCallSchedulerUnBlock(handleId)) {
                    // Enqueue entry onto deferred unblock queue. We will call unblock
                    // once we are done with processing signal and we released the lock
                    deferredQueue.EnqueueTail(entry.Thread.deferredEntry);
                }
            }
            else {
                // We haven't granted ownership to the thread so that we need to restore its
                // delay abort status
                entry.Thread.DelayStop(false);
            }

            return handledIdUnblocked;
        }

        ///
        /// <summary>
        /// This method is called when a synchrnoization object completes the wait for
        /// thread.
        /// </summary>
        ///
        /// <param name="entry">Thread entry to move from unsignaled queue to singlaed</param>
        ///
        [NoHeapAllocation]
        private void MoveEntryToSignalQueue(ThreadEntry entry)
        {
            // Assert preconditions: Entry should be enqueued to nonsignaled queue protectiong
            // spinlock has to be taken
            VTable.Assert(waitingQueue.IsEnqueued(entry));
            VTable.Assert(myLock.IsHeldBy(Thread.CurrentThread));

            // Remove thread from waiting queue
            waitingQueue.Remove(entry);

            // Insert thread into signaled queue
            signaledQueue.EnqueueHead(entry);
        }

        ///
        /// <summary>
        /// Remove entry from the wait handle
        /// </summary>
        ///
        /// <param name="entry">
        /// Entry to remove
        /// </param>
        ///
        [NoHeapAllocation]
        private void Remove(ThreadEntry entry)
        {
            Thread currentThread = Thread.CurrentThread;

            // Acquire lock. If you hit assert during acquire, and the code is handling
            // interrupt, you may need to use interrupt aware synchronization classes.
            // See the comment for  InterruptAwareAutoResetEvent, InterruptAwareManualResetEvent,
            // and InterruptAwareMutex for details.
            bool shouldEnable = Processor.DisableInterrupts();
            myLock.Acquire(currentThread);
            try {
                // Assert preconditions: entry should be on a either non signaled queue or if it is
                // on signaled queue thread's unblocked Id should be equal to entry's Id
                // We can run this assert only while spinlock is held because first we unblock thread
                // and then moving it from one queue to another. We do both of these operations while
                // holding spinlock. It is possible for thread to start running once it was unblocked.
                // When it reaches this method it is possible that it hasn't been moved to signaled queue yet
                // If that happens and we try to assert without holding spinlock assert will fire.
                VTable.Assert(entry.queue == this.waitingQueue ||
                              (entry.queue == this.signaledQueue &&
                               entry.Id == currentThread.UnblockedBy));


                // Remove entry from the queue
                entry.RemoveFromQueue();
            }
            finally {
                // Release lock
                myLock.Release();

                // Reenable interrupts
                Processor.RestoreInterrupts(shouldEnable);
            }
        }

        ///
        /// <summary>
        /// Return owner of a handle
        /// </summary>
        ///
        /// <remark>
        /// Consider removing this method
        /// </remark>
        [NoHeapAllocation]
        internal Thread GetBeneficiary()
        {
            return owner;
        }

        ///
        /// <summary>
        /// Complete wait - used by mutex to record ownership
        /// </summary>
        ///
        /// <param name="ownerThread">Thread owner</param>
        ///
        [NoHeapAllocation]
        protected virtual void CompleteWait(Thread ownerThread)
        {
            return;
        }

        /// <summary>State of the handler</summary>
        private volatile SignalState        signaled;

        /// <summary> Signal state after wait - policy of the child class </summary>
        protected SignalState               signalStateAfterImediateWait;

        /// <summary> An owner of the handler </summary>
        protected volatile Thread           owner;

        /// <summary> A waiting queue </summary>
        protected ThreadQueue               waitingQueue;

        /// <summary> A signaled queue </summary>
        protected ThreadQueue               signaledQueue;

        /// <summary> A unique id of wait handler </summary>
        protected int                       id;

        /// <summary> Uniqifier </summary>
        private static int                  idGenerator;

        /// <summary> Lock to protect queues </summary>
        protected SpinLock                  myLock;
    }
}
