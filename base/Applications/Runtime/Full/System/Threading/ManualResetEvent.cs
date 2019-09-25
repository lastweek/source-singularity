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

    //| <include path='docs/doc[@for="ManualResetEvent"]/*' />
    [CLSCompliant(false)]
    public sealed class ManualResetEvent : WaitHandle
    {
        private ManualResetEventHandle handle;

        //| <include path='docs/doc[@for="ManualResetEvent.ManualResetEvent2"]/*' />
        public ManualResetEvent(bool initialState)
        {
            ManualResetEventHandle handleOnStack;
            if (!ManualResetEventHandle.Create(initialState, out handleOnStack)) {
                throw new HandleCreateException();
            }
            handle = handleOnStack;
        }

        /// <summary>
        /// Finalizer is responsible for freeing handle that keeps corresponding
        /// kernel object live.
        /// </summary>
        ~ManualResetEvent() {
            if (this.handle.id != 0) {
                ManualResetEventHandle.Dispose(this.handle);
                this.handle = new ManualResetEventHandle();
            }
        }

        //| <include path='docs/doc[@for="ManualResetEvent.Reset"]/*' />
        public void Reset()
        {
            ManualResetEventHandle.Reset(handle);
            GC.KeepAlive(this);
        }

        //| <include path='docs/doc[@for="ManualResetEvent.Set"]/*' />
        public bool Set()
        {
            bool b = ManualResetEventHandle.Set(handle);
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

        //| <include path='docs/doc[@for="ManualResetEventHandle.Dispose"]/*' />
        protected override void Dispose(bool explicitDisposing)
        {
            if (handle.id != 0) {
                ManualResetEventHandle.Dispose(handle);
                handle = new ManualResetEventHandle();
            }
        }
    }
}
