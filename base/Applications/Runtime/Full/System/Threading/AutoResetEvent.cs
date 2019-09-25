// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Threading
{

    using System;
    using System.Runtime.CompilerServices;
    using Microsoft.Singularity;
    using Microsoft.Singularity.V1.Threads;
    using Microsoft.Singularity.V1.Services;

    //| <include path='docs/doc[@for="AutoResetEvent"]/*' />
    [CLSCompliant(false)]
    public sealed class AutoResetEvent : WaitHandle
    {
        private AutoResetEventHandle handle;

        //| <include path='docs/doc[@for="AutoResetEvent.AutoResetEvent2"]/*' />
        public AutoResetEvent(bool initialState)
        {
            AutoResetEventHandle handleOnStack;
            if (!AutoResetEventHandle.Create(initialState, out handleOnStack)) {
                throw new HandleCreateException();
            }
            handle = handleOnStack;
        }

        /// <summary>
        /// Finalizer is responsible for freeing handle that keeps corresponding
        /// kernel AutoResetEvent object live.
        /// </summary>
        ~AutoResetEvent() {
            if (this.handle.id != 0) {
                AutoResetEventHandle.Dispose(this.handle);
                this.handle = new AutoResetEventHandle();
            }
        }

        //| <include path='docs/doc[@for="AutoResetEvent.Reset"]/*' />
        public void Reset()
        {
            AutoResetEventHandle.Reset(handle);
            GC.KeepAlive(this);
        }

        //| <include path='docs/doc[@for="AutoResetEvent.Set"]/*' />
        public void Set()
        {
            AutoResetEventHandle.Set(handle);
            GC.KeepAlive(this);
        }

        //| <include path='docs/doc[@for="AutoResetEvent.SetAll"]/*' />
        public void SetAll()
        {
            AutoResetEventHandle.SetAll(handle);
            GC.KeepAlive(this);
        }

        internal void SetNoGC()
        {
            AutoResetEventHandle.SetNoGC(handle);
            GC.KeepAlive(this);
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

        internal bool WaitOneNoGC()
        {
            bool b = SyncHandle.WaitOneNoGC(handle);
            GC.KeepAlive(this);
            return b;
        }

        //| <include path='docs/doc[@for="AutoResetEventHandle.Dispose"]/*' />
        protected override void Dispose(bool explicitDisposing)
        {
            if (handle.id != 0) {
                AutoResetEventHandle.Dispose(handle);
                handle = new AutoResetEventHandle();
            }
        }
    }
}
