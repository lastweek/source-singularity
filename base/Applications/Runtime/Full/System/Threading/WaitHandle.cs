// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: WaitHandle    (this name is NOT definitive)
//
// Purpose: Class to represent all synchronization objects in the runtime (that allow multiple wait)
//
//=============================================================================  

namespace System.Threading
{
    using System;
    using System.Threading;
    using System.Runtime.CompilerServices;
    using System.Collections;
    using Microsoft.Singularity;
    using Microsoft.Singularity.V1.Threads;
    using Microsoft.Singularity.V1.Services;

    //| <include path='docs/doc[@for="WaitHandle"]/*' />
    [CLSCompliant(false)]
    public abstract class WaitHandle : IDisposable
    {
        //| <include path='docs/doc[@for="WaitHandle.WaitTimeout"]/*' />
        public const int WaitTimeout = -1;

        protected WaitHandle()
        {
        }

        protected abstract SyncHandle Handle{
            get;
        }

        //| <include path='docs/doc[@for="WaitHandle.WaitOne"]/*' />
        public abstract bool WaitOne(TimeSpan timeout);

        //| <include path='docs/doc[@for="WaitHandle.WaitOne1"]/*' />
        public abstract bool WaitOne(SchedulerTime stop);

        [Obsolete("Do not use DateTime for scheduling. It is meaningless. Use SchedulerTime")]
        public bool WaitOne(DateTime stop) {
            SchedulerTime st = SchedulerTime.MinValue + (stop - DateTime.BootTime);
            return WaitOne(st);
        }

        //| <include path='docs/doc[@for="SyncHandle.WaitOne2"]/*' />
        public abstract bool WaitOne();

        //| <include path='docs/doc[@for="WaitHandleHandle.WaitAny"]/*' />
        public static unsafe int WaitAny(WaitHandle[] waitHandles,
                                         TimeSpan timeout)
        {
            SyncHandle[] handles = Thread.CurrentThread.GetSyncHandles(waitHandles.Length);
            for (int i = 0; i < waitHandles.Length; i++) {
                handles[i] = waitHandles[i].Handle;
            }
            fixed (SyncHandle *array = &handles[0]) {
                return SyncHandle.WaitAny(array, waitHandles.Length, timeout);
            }
        }

        //| <include path='docs/doc[@for="WaitHandleHandle.WaitAny"]/*' />
        public static unsafe int WaitAny(WaitHandle[] waitHandles,
                                         SchedulerTime stop)
        {
            SyncHandle[] handles = Thread.CurrentThread.GetSyncHandles(waitHandles.Length);
            for (int i = 0; i < waitHandles.Length; i++) {
                handles[i] = waitHandles[i].Handle;
            }
            fixed (SyncHandle *array = &handles[0]) {
                return SyncHandle.WaitAny(array, waitHandles.Length, stop);
            }
        }

        //| <include path='docs/doc[@for="WaitHandleHandle.WaitAny2"]/*' />
        public static unsafe int WaitAny(WaitHandle[] waitHandles)
        {
            SyncHandle[] handles = Thread.CurrentThread.GetSyncHandles(waitHandles.Length);
            for (int i = 0; i < waitHandles.Length; i++) {
                handles[i] = waitHandles[i].Handle;
            }
            fixed (SyncHandle *array = &handles[0]) {
                return SyncHandle.WaitAny(array, waitHandles.Length);
            }
        }

        //| <include path='docs/doc[@for="WaitHandle.Dispose"]/*' />
        protected abstract void Dispose(bool explicitDisposing);

        //| <include path='docs/doc[@for="WaitHandle.Close"]/*' />
        public virtual void Close()
        {
            Dispose(true);
            GC.nativeSuppressFinalize(this);
        }

        //| <include path='docs/doc[@for="WaitHandle.IDisposable.Dispose"]/*' />
        /// <internalonly/>
        void IDisposable.Dispose()
        {
            Dispose(true);
            GC.nativeSuppressFinalize(this);
        }

        //| <include path='docs/doc[@for="WaitHandle.Finalize"]/*' />
        ~WaitHandle()
        {
            Dispose(false);
        }

        public static implicit operator WaitHandle(SyncHandle s) {
            return new SyncWaitHandle(s);
        }

    }

        internal class SyncWaitHandle : WaitHandle
        {
            private readonly SyncHandle _sync;
            public SyncWaitHandle(SyncHandle s) {
                _sync = s;
            }
            protected override SyncHandle Handle {
                get { return _sync; }
            }
            public override bool WaitOne(TimeSpan timeout) {
                return SyncHandle.WaitOne(Handle, timeout);
            }
            public override bool WaitOne(SchedulerTime stop) {
                return SyncHandle.WaitOne(Handle, stop);
            }
            public override bool WaitOne() {
                return SyncHandle.WaitOne(Handle);
            }
            protected override void Dispose(bool explicitDisposing) {
                // todo: implement
            }
        }

}
