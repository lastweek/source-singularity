///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Scheduler.cs
//
//  Note:
//

//#define DEBUG_SCHEDULER

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;

namespace Microsoft.Singularity.Scheduling
{
    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from halidt.asm")]
    public abstract class Scheduler
    {
        ///
        /// <summary>
        /// Constructor - is used to generate scheduler Ids
        /// </summary>
        ///


        protected Scheduler()
        {
        }

        public abstract void Initialize();

        [CLSCompliant(false)]
        public abstract void Finalize();

        [CLSCompliant(false)]
        public abstract void OnDispatcherInitialize(int dispatcherId);

        [CLSCompliant(false)]
        public abstract void OnThreadStateInitialize(Thread thread, bool constructorCalled);

        [CLSCompliant(false)]
        public abstract void OnThreadStart(Thread thread);

        [CLSCompliant(false)]
        public abstract void OnThreadBlocked(Thread thread, SchedulerTime stop);

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public abstract void OnThreadUnblocked(Thread thread);

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public abstract void OnThreadYield(Thread thread);

        [CLSCompliant(false)]
        public abstract void OnThreadStop(Thread thread);

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public abstract void OnThreadFreezeIncrement(Thread thread);

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public abstract void OnThreadFreezeDecrement(Thread thread);

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public abstract TimeSpan OnTimerInterrupt(int affinity, SchedulerTime now);

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static bool IsIdleThread (int threadIdx)
        {
            return ProcessorDispatcher.IsIdleThread(threadIdx);
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public abstract void AddRunnableThread(Thread thread);

        ///
        /// <summary>
        /// Run scheduling policy to decide the next thread to run
        /// </summary>
        ///
        /// <param name="affinity">Set the returned running thread to this affinity.</param>
        /// <param name="currentThread">the thread currently running</param>
        /// <param name="schedulerAction">thread state to change to for the current thread</param>
        /// <param name="currentTime">Current system time</param>
        ///
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public abstract Thread RunPolicy(
            int             affinity,
            Thread          currentThread,
            ThreadState     schedulerAction,
            SchedulerTime   currentTime);

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public abstract void Suspend(Thread thread);

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public abstract void Resume(Thread thread);

        ///
        /// <summary>
        ///    Scheduler hints for enquing threads
        /// </summary>
        ///
        [Flags]
        public enum Hint
        {
            Head            = 0,
            Tail            = 1,
        }

        ///
        /// <summary>
        /// Retrieve scheduler lock - used by dispatcher to protect scheduler state
        /// </summary>
        ///
        [CLSCompliant(false)]
        [NoHeapAllocation]
        internal abstract SchedulerLock RetrieveSchedulerLock(int affinity);
    }

    ///
    /// <summary>
    /// Scheduler lock class is used to wrap a spinlock structure so that it can be shared with a
    /// dispatcher.
    /// </summary>
    ///
    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from halidt.asm")]
    internal class SchedulerLock
    {
        ///
        /// <summary>
        /// Constructor
        /// </summary>
        ///
        public SchedulerLock()
        {
            // Initialize spinlock
            this.spinlock = new SpinLock(SpinLock.Types.Scheduler);
        }


        ///
        /// <summary>
        /// A method is used to acquire scheduler lock
        /// </summary>
        ///
        [NoHeapAllocation]
        public void Acquire(Thread currentThread)
        {
            this.spinlock.Acquire(currentThread);
        }

        ///
        /// <summary>
        /// A method is used to release scheduler lock
        /// </summary>
        ///
        [NoHeapAllocation]
        public void Release(Thread currentThread)
        {
            this.spinlock.Release(currentThread);
        }

        ///
        /// <summary>
        /// A method is used to acquire scheduler lock
        /// </summary>
        ///
        [NoHeapAllocation]
        public void Acquire()
        {
            this.spinlock.Acquire();
        }

        ///
        /// <summary>
        /// Try to acquire the spin lock. Always return immediately.
        /// </summary>
        /// <returns> true if the spin lock is acquired. </returns>
        ///
        [NoHeapAllocation]
        public bool TryAcquire()
        {
            return this.spinlock.TryAcquire();
        }

        ///
        /// <summary>
        /// A method is used to release scheduler lock
        /// </summary>
        ///
        [NoHeapAllocation]
        public void Release()
        {
            this.spinlock.Release();
        }


        ///
        /// <summary>
        /// Check if thread holds the spinlock
        /// </summary>
        ///
        [NoHeapAllocation]
        public bool IsHeldBy(Thread currentThread)
        {
            return this.spinlock.IsHeldBy(currentThread);
        }


        /// <summary> Actual spinlock that class wraps </summary>
        [AccessedByRuntime("referenced from halidt.asm")]
        private SpinLock                    spinlock;

    }
}
