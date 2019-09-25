////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   AutoResetEventHandle.csi
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity.V1.Threads
{
    [CLSCompliant(false)]
    public struct AutoResetEventHandle // : public SyncHandle
    {
        public readonly UIntPtr id; // could be moved to SyncHandle

        public static readonly AutoResetEventHandle Zero = new AutoResetEventHandle();

        internal AutoResetEventHandle(UIntPtr id)
        {
            this.id = id;
        }

        [ExternalEntryPoint]
        public static unsafe bool CreateImpl(
            bool initialState,
            AutoResetEventHandle * handle)
        {
            return Create(initialState, out *handle);
        }

        public static bool Create(bool initialState,
                                  out AutoResetEventHandle handle)
        {
            //
            // Create a new auto-reset event, and a handle in the current
            // process to hold it.
            //
            handle = new AutoResetEventHandle(
                Thread.CurrentProcess.AllocateHandle(
                    new AutoResetEvent(initialState)));

            Tracing.Log(Tracing.Debug, "AutoResetEventHandle.Create(state=, out id={0:x8})",
                        handle.id);
            return true;
        }

        [ExternalEntryPoint]
        public static void Dispose(AutoResetEventHandle handle)
        {
            Dispose(Thread.CurrentProcess, handle);
        }

        internal static void Dispose(Process process,
                                     AutoResetEventHandle handle)
        {
            Tracing.Log(Tracing.Debug, "AutoResetEventHandle.Dispose(id={0:x8})",
                        handle.id);
            //
            // Releasing the handle will allow the auto-reset event to be
            // garbage-collected.
            //
            process.ReleaseHandle(handle.id);
        }

        [ExternalEntryPoint]
        public static bool Reset(AutoResetEventHandle handle)
        {
            //
            // Convert the handle to an auto-reset event; reset the event.
            //
            AutoResetEvent are = HandleTable.GetHandle(handle.id) as AutoResetEvent;
            bool ret = are.Reset();

            Tracing.Log(Tracing.Debug, "AutoResetEventHandle.Reset(id={0:x8})",
                        handle.id);

            return ret;
        }

        [ExternalEntryPoint]
        public static bool Set(AutoResetEventHandle handle)
        {
            //
            // Convert the handle to an auto-reset event; set the event.
            //
            AutoResetEvent are = HandleTable.GetHandle(handle.id) as AutoResetEvent;
            bool ret = are.Set();

            Tracing.Log(Tracing.Debug, "AutoResetEventHandle.Set(id={0:x8})",
                        handle.id);

            return ret;
        }

        [ExternalEntryPoint]
        public static bool SetAll(AutoResetEventHandle handle)
        {
            //
            // Convert the handle to an auto-reset event; set the event.
            //
            AutoResetEvent are = HandleTable.GetHandle(handle.id) as AutoResetEvent;
            bool ret = are.SetAll();

            Tracing.Log(Tracing.Debug, "AutoResetEventHandle.SetAll(id={0:x8})",
                        handle.id);

            return ret;
        }

        [ExternalEntryPoint(IgnoreCallerTransition=1)]
        public static bool SetNoGC(AutoResetEventHandle handle) {
            return Set(handle);
        }
    }
}
