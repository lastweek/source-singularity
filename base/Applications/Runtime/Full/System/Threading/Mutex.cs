// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Threading
{
    using System;
    using System.Threading;
    using System.Runtime.CompilerServices;
    using Microsoft.Singularity;
    using Microsoft.Singularity.V1.Threads;
    using Microsoft.Singularity.V1.Services;

    //| <include path='docs/doc[@for="Mutex"]/*' />
    [CLSCompliant(false)]
    public sealed class Mutex : WaitHandle
    {
        private MutexHandle handle;

        //| <include path='docs/doc[@for="Mutex.Mutex2"]/*' />
        public Mutex(bool initiallyOwned)
        {
            MutexHandle handleOnStack;
            if (!MutexHandle.Create(initiallyOwned, out handleOnStack)) {
                throw new HandleCreateException();
            }
            handle = handleOnStack;
        }

        //| <include path='docs/doc[@for="Mutex.Mutex3"]/*' />
        public Mutex()
        {
            MutexHandle handleOnStack;
            if (!MutexHandle.Create(false, out handleOnStack)) {
                throw new HandleCreateException();
            }
            handle = handleOnStack;
        }

        /// <summary>
        /// Finalizer is responsible for freeing handle that keeps corresponding
        /// kernel AutoResetEvent object live.
        /// </summary>
        ~Mutex() {
            if (this.handle.id != 0) {
                MutexHandle.Dispose(this.handle);
                this.handle = new MutexHandle();
            }
        }

        public bool AcquireMutex()
        {
            return WaitOne();
        }

        public bool AcquireMutex(SchedulerTime stop)
        {
            return WaitOne(stop);
        }


        //| <include path='docs/doc[@for="Mutex.ReleaseMutex"]/*' />
        public void ReleaseMutex()
        {
            MutexHandle.Release(handle);
            GC.KeepAlive(this);
        }

        // Called by monitor to see if its lock is held by the current thread.
        internal bool IsOwnedByCurrentThread()
        {
            bool b = MutexHandle.IsOwnedByCurrentThread(handle);
            GC.KeepAlive(this);
            return b;
        }

        protected override SyncHandle Handle{
            get {
                return handle;
            }
        }

        //| <include path='docs/doc[@for="WaitHandle.WaitOne"]/*' />
        public override bool WaitOne(TimeSpan timeout)
        {
            bool b = SyncHandle.WaitOne(handle, timeout);
            GC.KeepAlive(this);
            return b;
        }

        //| <include path='docs/doc[@for="WaitHandle.WaitOne1"]/*' />
        public override bool WaitOne(SchedulerTime stop)
        {
            bool b = SyncHandle.WaitOne(handle, stop);
            GC.KeepAlive(this);
            return b;
        }

        //| <include path='docs/doc[@for="SyncHandle.WaitOne2"]/*' />
        public override bool WaitOne()
        {
            bool b = SyncHandle.WaitOne(handle);
            GC.KeepAlive(this);
            return b;
        }

        //| <include path='docs/doc[@for="MutexHandle.Dispose"]/*' />
        protected override void Dispose(bool explicitDisposing)
        {
            if (handle.id != 0) {
                MutexHandle.Dispose(handle);
                handle = new MutexHandle();
            }
        }
    }
}
