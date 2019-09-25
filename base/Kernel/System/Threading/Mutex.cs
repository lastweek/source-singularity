////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Mutex.cs
//
//  Note:
//

using System;
using System.Threading;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Scheduling;

namespace System.Threading
{
    [CLSCompliant(false)]
    public enum MutexEvent
    {
        AcquireAgain = 1,
        Acquire = 2,
        Enqueue = 3,
    }

    ///
    /// <summary>
    ///     Mutex class implementing a mutex functionality
    /// </summary>
    ///
    [NoCCtor]
    [CLSCompliant(false)]
    public sealed class Mutex : WaitHandle
    {
        ///
        /// <summary>
        ///     Default constructor
        ///</summary>
        ///
        public Mutex()
            : this(false, true)
        {
        }

        ///
        /// <summary>
        ///     Constructor
        ///</summary>
        ///
        /// <param name="initiallyOwned">Initial state of a mutex</param>
        ///
        /// <remark> We assume that mutex can initially be owned by current thread only </remark>
        ///
        public Mutex(bool initiallyOwned)
            : this(initiallyOwned, true)
        {
        }

        ///
        /// <summary>
        ///     Constructor
        ///</summary>
        ///
        /// <param name="initiallyOwned">Initial state of a mutex</param>
        /// <param name="isKernelObject">
        ///     True if this mutex is created by kernel and therefore used by kernel threads. 
        ///     False if this mutex is created by a SIP and therefore used only by the SIP.
        /// 
        ///     A kernel thread is not allowed to be forcibly stopped while owning a mutex,
        ///     whereas SIP threads can be forcibly stopped while owning a mutex. This doesn't
        ///     create problems for SIPs because the only time a SIP thread is forced to stop is
        ///     during process torn down.
        /// </param>
        ///
        /// <remark> We assume that mutex can initially be owned by current thread only </remark>
        ///
        public Mutex(bool initiallyOwned, bool isKernelObject)
            : base(initiallyOwned ? WaitHandle.SignalState.Unsignaled : 
                                   WaitHandle.SignalState.Signaled,
                   WaitHandle.SignalState.Unsignaled,
                   SpinLock.Types.Mutex)

        {
            this.isKernelObject = isKernelObject;
            if (initiallyOwned) {
                Thread currentThread = Thread.CurrentThread;
                this.owner = Thread.CurrentThread;

                if (this.isKernelObject) {
                    // Kernel thread can't be stop if it owns mutex
                    currentThread.DelayStop(true);
                }

                this.acquired = 1;
            }
        }

        ///
        /// <summary>
        ///     Finalize method - release mutex by hand if it is going away
        ///</summary>
        ///
        [CLSCompliant(false)]
        public void Finalize() {

            // If a thread owns mutex and mutex is pure kernel object update its dealy abort counter
            if (this.owner != null && this.isKernelObject) {
                this.owner.DelayStop(false);
            }
        }

        ///
        /// <summary>
        ///     Acquire mutex without time out specified
        ///</summary>
        ///
        public void AcquireMutex()
        {
            WaitOne(SchedulerTime.MaxValue);
        }

        ///
        /// <summary>
        ///     Acquire mutex with time out specified
        ///</summary>
        ///
        /// <param name="stop">Specified time out</param>
        ///
        public bool AcquireMutex(SchedulerTime stop)
        {
            bool        result = true;;
            Thread      currentThread = Thread.CurrentThread;

            // If we own the mutex we can by pass the wait - do wait only if we don't own
            if (this.owner != currentThread) {
                result = WaitOne(stop);
            }
            else {
                // Don't forget to update recursion counter
                this.acquired++;
            }
             

            return result;
        }

        ///
        /// <summary>
        ///     Release mutex 
        ///</summary>
        ///
        public void ReleaseMutex()
        {
            // Assert precondition: Only thread that owns mutex can release it and mutex 
            // acquired counter should be strictly positive
            VTable.Assert(Thread.CurrentThread == this.owner);
            VTable.Assert(this.acquired > 0);

            if (Thread.CurrentThread == this.owner && this.acquired > 0) {
                // Decrement recurtion counter - first step for giving up ownership
                this.acquired--;

                // If we are done with mutex - give up ownership
                if (this.acquired == 0) {

                    //Indicate that noone longer owns mutex
                    this.owner = null;

                    // Wakeup waiters
                    SignalOne(WaitHandle.SignalState.Signaled);

                    // If this is kernel object, the thread can be aborted now
                    if (this.isKernelObject) {
                        Thread.CurrentThread.DelayStop(false);
                    }
                }
            }
        }

        ///
        /// <summary>
        ///     Check if mutex is owned by the current thread
        ///</summary>
        ///
        internal bool IsOwnedByCurrentThread()
        {
            return (Thread.CurrentThread == owner);
        }

        ///
        /// <summary>
        ///     Try to acquire a mutex if acquire fail entry will be enqueued onto wait queue
        ///</summary>
        ///
        /// <param name="entry">Entry represents a thread attempting to acquire mutex</param>
        /// <param name="handleId">
        ///     Id of the handle that we are trying to acquire - is used to check if thread can be unblocked
        /// </param>
        ///
        [NoHeapAllocation]
        protected override bool AcquireOrEnqueue(ThreadEntry entry, int handleId)
        {
             bool didAcquire = true;

            // Assert preconditions: Current thread and entry's thread should be the same
            VTable.Assert(Thread.CurrentThread == entry.Thread);
            VTable.Assert(Thread.CurrentThread.IsAbortDelayed());
            
            // If we currently don't own mutex try to acquire it or enqueue ourselves..
            if (this.owner != entry.Thread) {
                didAcquire = base.AcquireOrEnqueue (entry, handleId);
            }

            return didAcquire;
        }

        ///
        /// <summary>
        ///     Complete wait - used by mutex to record ownership
        ///</summary>
        ///
        /// <param name="ownerThread">Thread owner</param>
        ///
        [NoHeapAllocation]
        protected override void CompleteWait(Thread ownerThread)
        {
            // Assert preconditions
            VTable.Assert(Thread.CurrentThread == ownerThread);
            
            // Update recursion counter
            this.acquired++;

            //If this is first time we acquired mutex don't forget to update owner
            if (this.acquired == 1) {

                if (this.isKernelObject) {
                    // Kernel thread can't be stop if it owns mutex
                    ownerThread.DelayStop(true);
                }
                this.owner = ownerThread;
            }
        }

        /// <summary> 
        ///     Recursion counter indicating number of times mutex is acquired by the same
        ///     thread
        /// </summary>
        private int             acquired = 0;

        /// <summary>
        ///     True if this mutex is created by kernel and therefore used by kernel threads. 
        ///     False if this mutex is created by a SIP and therefore used only by the SIP.
        ///     
        ///     A kernel thread is not allowed to be forcibly stopped while owning a mutex,
        ///     whereas SIP threads can be forcibly stopped while owning a mutex. This doesn't
        ///     create problems for SIPs because the only time a SIP thread is forced to stop is
        ///     during process torn down.
        /// </summary>
        private readonly bool   isKernelObject;
    }
}
