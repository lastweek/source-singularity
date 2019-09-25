////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//      User spinlock functionality 
//
using System;
using Microsoft.Singularity;
using System.Runtime.CompilerServices;
using System.Threading;

namespace System.Threading
{
    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from halidt.asm")]
    public struct SpinLock
    {
        ///
        /// <summary>
        ///     Acquire spinlock
        /// </summary>
        ///
        [NoHeapAllocation]
        [Inline]
        public void Acquire()
        {
            Thread  thread = Thread.CurrentThread;
            AcquireInternal(thread, thread.GetThreadId());
        }

        ///
        /// <summary>
        ///     Acquire spinlock
        /// </summary>
        ///
        /// <param name="threadId">Thread's Id acquiring spinlock</param>
        ///
        [NoHeapAllocation]
        [Inline]
        public void Acquire(int threadId)
        {
            AcquireInternal(Thread.GetThreadFromThreadId(threadId), threadId);
        }

        ///
        /// <summary>
        ///     Acquire spinlock
        /// </summary>
        ///
        /// <param name="thread">Thread acquiring spinlock</param>
        ///
        [NoHeapAllocation]
        public void Acquire(Thread thread)
        {
            AcquireInternal(thread, thread.GetThreadId());
        }

        ///
        /// <summary>
        ///     Release spinlock
        /// </summary>
        ///
        [NoHeapAllocation]
        public void Release()
        {
            Thread  thread = Thread.CurrentThread;

            // Release spinlock
            ReleaseInternal(thread, thread.GetThreadId());
        }

        ///
        /// <summary>
        ///     Release spinlock
        /// </summary>
        ///
        /// <param name="threadId">Thread's Id releasing spinlock</param>
        ///
        [NoHeapAllocation]
        public void Release(int threadId)
        {
            // Release spinlock
            ReleaseInternal(Thread.GetThreadFromThreadId(threadId), threadId);
        }

        ///
        /// <summary>
        ///     Release spinlock
        /// </summary>
        ///
        /// <param name="thread">Thread releasing spinlock</param>
        ///
        [NoHeapAllocation]
        public void Release(Thread thread)
        {
            // Release spinlock
            ReleaseInternal(thread, thread.GetThreadId());
        }

        ///
        /// <summary>
        ///     Try to acquire the spin lock. Always return immediately. 
        /// </summary>
        ///
        /// <returns> true if the spin lock is acquired. </returns>
        [NoHeapAllocation]
        public bool TryAcquire()
        {
            Thread  thread = Thread.CurrentThread;
            return TryAcquireInternal(thread, thread.GetThreadId());
        }

        ///
        /// <summary>
        ///     Try to acquire the spin lock. Always return immediately. 
        /// </summary>
        ///
        /// <returns> true if the spin lock is acquired. </returns>
        ///
        /// <param name="thread">Thread acquiring spinlock</param>
        ///

        [NoHeapAllocation]
        public bool TryAcquire(Thread thread)
        {
            int threadId = thread.GetThreadId();

            return TryAcquireInternal(thread, thread.GetThreadId());
        }

        /// 
        /// <summary>
        ///     Method to find out if spinlock is held by specified thread
        /// </summary>
        /// <returns> true if the spin lock is acquired. </returns>
        ///
        /// <param name="thread">Thread to verify possible spinlock's ownership</param>
        ///
        [NoHeapAllocation]
        public bool IsHeldBy(Thread thread)
        {
            return baseLock.IsHeldBy(thread.GetThreadId()+1);
        }

        /// 
        /// <summary>
        ///     Method to find out if spinlock is held by specified thread
        /// </summary>
        /// <returns> true if the spin lock is acquired. </returns>
        ///
        /// <param name="threadId">Thread's Id to verify possible spinlock's ownership</param>
        ///
        [NoHeapAllocation]
        public bool IsHeldBy(int threadId)
        {
            return baseLock.IsHeldBy(threadId+1);
        }

        /// 
        /// <summary>
        ///     Assert thatf spinlock is held by specified thread
        /// </summary>
        ///
        /// <param name="thread">Thread to verify possible spinlock's ownership</param>
        ///
        [System.Diagnostics.Conditional("DEBUG")]
        [NoHeapAllocation]
        public void AssertHeldBy(Thread thread)
        {
            VTable.Assert(IsHeldBy(thread));
        }

        /// 
        /// <summary>
        ///     Assert thatf spinlock is held by specified thread
        /// </summary>
        ///
        /// <param name="threadId">Thread's Id to verify possible spinlock's ownership</param>
        ///
        [System.Diagnostics.Conditional("DEBUG")]
        [NoHeapAllocation]
        public void AssertHeldBy(int threadId)
        {
            VTable.Assert(IsHeldBy(threadId));
        }

        /// 
        /// <summary>
        ///     Try to acquire the spin lock. Always return immediately. 
        /// </summary>
        /// <returns> true if the spin lock is acquired. </returns>
        ///
        /// <param name="thread">Thread acquiring spinlock</param>
        /// <param name="threadId">Thread's Id acquiring spinlock</param>
        ///
        [NoHeapAllocation]
        private bool TryAcquireInternal(Thread thread, int threadId)
        {
            bool result;

            VTable.Assert(thread != null);

            // Notify thread that we are about to acquire spinlock
            thread.NotifySpinLockAboutToAcquire(this.baseLock.Type);
            
            result = baseLock.TryAcquire(threadId+1);

            // If we didn't acquire spinlock -we should notify thread about it: Just use release
            // notification 
            if (!result) {
                thread.NotifySpinLockReleased(this.baseLock.Type);
            }

            return result;
        }

        /// 
        /// <summary>
        ///     Acquire the spin lock. 
        /// </summary>
        ///
        /// <param name="thread">Thread acquiring spinlock</param>
        /// <param name="threadId">Thread's Id acquiring spinlock</param>
        ///
        [NoHeapAllocation]
        private void AcquireInternal(Thread thread, int threadId)
        {
            VTable.Assert(thread != null);

            // Thread has to be notified if we are about to acquire spinlock
            thread.NotifySpinLockAboutToAcquire(this.baseLock.Type);
            
            // Get lock
            baseLock.Acquire(threadId+1);
        }

        /// 
        /// <summary>
        ///     Release the spin lock. 
        /// </summary>
        ///
        /// <param name="thread">Thread releasing spinlock</param>
        /// <param name="threadId">Thread's Id releasing spinlock</param>
        ///
        [NoHeapAllocation]
        private void ReleaseInternal(Thread thread, int threadId)
        {
            // Assert preconditions: Thread can't be null
            VTable.Assert(thread != null);

            // Release spinlock
            baseLock.Release(threadId+1);

            // Don't forget to notify thread that it just released spinlock
            thread.NotifySpinLockReleased(this.baseLock.Type);
        }

        /// <summary> Actual mechanism implementing spinlock</summary>
        private SpinLockBase                        baseLock;
    }
}
