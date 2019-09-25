////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ManualResetEventHandle.cs
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
    public struct ManualResetEventHandle // : public SyncHandle
    {
        public readonly UIntPtr id; // could be moved to SyncHandle

        public static readonly ManualResetEventHandle Zero = new ManualResetEventHandle();

        internal ManualResetEventHandle(UIntPtr id)
        {
            this.id = id;
        }

        [ExternalEntryPoint]
        public static unsafe bool CreateImpl(
            bool initialState,
            ManualResetEventHandle * handle)
        {
            return Create(initialState, out *handle);
        }

        public static bool Create(bool initialState,
                                  out ManualResetEventHandle handle)
        {
            //
            // Create a new manual-reset event, and a handle in the current
            // process to hold it.
            //
            handle = new ManualResetEventHandle(
                Thread.CurrentProcess.AllocateHandle(
                    new ManualResetEvent(initialState)));

            Tracing.Log(Tracing.Debug, "ManualResetEventHandle.Create(state=, out id={0:x8})",
                        handle.id);
            return true;
        }

        [ExternalEntryPoint]
        public static void Dispose(ManualResetEventHandle handle)
        {
            Tracing.Log(Tracing.Debug, "ManualResetEventHandle.Dispose(id={0:x8})",
                        handle.id);

            //
            // Releasing the handle will allow the manual-reset event to be
            // garbage-collected.
            //
            Thread.CurrentProcess.ReleaseHandle(handle.id);
        }

        [ExternalEntryPoint]
        public static bool Reset(ManualResetEventHandle handle)
        {
            //
            // Convert the handle to a manual-reset event; reset the event.
            //
            ManualResetEvent mre = HandleTable.GetHandle(handle.id) as ManualResetEvent;
            bool ret = mre.Reset();

            Tracing.Log(Tracing.Debug, "ManualResetEventHandle.Reset(id={0:x8})",
                        handle.id);

            return ret;
        }

        [ExternalEntryPoint]
        public static bool Set(ManualResetEventHandle handle)
        {
            //
            // Convert the handle to a manual-reset event; set the event.
            //
            ManualResetEvent mre = HandleTable.GetHandle(handle.id) as ManualResetEvent;
            bool ret = mre.Set();

            Tracing.Log(Tracing.Debug, "ManualResetEventHandle.Set(id={0:x8})",
                        handle.id);

            return ret;
        }
    }
}
