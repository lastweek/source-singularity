////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   SyncHandle.cs
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
    public struct SyncHandle
    {
        public readonly UIntPtr id;

        public static readonly SyncHandle Zero = new SyncHandle();

        [Inline]
        public static implicit operator SyncHandle(MutexHandle handle)
        {
            return new SyncHandle(handle.id);
        }

        [Inline]
        public static implicit operator SyncHandle(AutoResetEventHandle handle)
        {
            return new SyncHandle(handle.id);
        }

        [Inline]
        public static implicit operator SyncHandle(ManualResetEventHandle handle)
        {
            return new SyncHandle(handle.id);
        }

        internal SyncHandle(UIntPtr id)
        {
            this.id = id;
        }

#if false
        /// REVIEW: generalizes waiting across events and endpoints
        /// should review to ensure this is safe
        public WaitHandle GetWaitHandle() {
            return HandleTable.GetHandle(id) as WaitHandle;
        }

        public static implicit operator WaitHandle(SyncHandle s) {
            return HandleTable.GetHandle(s.id) as WaitHandle;
        }
#endif

        //////////////////////////////////////////////////////////////////////
        //
        // The following methods could be moved to WaitHandle if we had
        // struct inheritance.
        //
        [ExternalEntryPoint]
        public static bool WaitOne(SyncHandle handle)
        {
            //
            // Convert the handle to a waitHandle; wait on the waitHandle.
            //
            WaitHandle waitHandle = HandleTable.GetHandle(handle.id) as WaitHandle;
            bool ret = waitHandle.WaitOne(SchedulerTime.MaxValue);

            Tracing.Log(Tracing.Debug, "SyncHandle.WaitOne(id={0:x8})", handle.id);

            return ret;
        }

        [ExternalEntryPoint(IgnoreCallerTransition=1)]
        public static bool WaitOneNoGC(SyncHandle handle)
        {
            WaitHandle waitHandle =
                HandleTable.GetHandle(handle.id) as WaitHandle;
            bool ret = waitHandle.WaitOne(SchedulerTime.MaxValue);
            Tracing.Log(Tracing.Debug, "SyncHandle.WaitOneNoGC(id={0:x8})",
                        handle.id);
            return ret;
        }

        [ExternalEntryPoint]
        public static bool WaitOne(SyncHandle handle,
                                   TimeSpan timeout)
        {
            //
            // Convert the handle to a waitHandle; wait on the waitHandle.
            //
            WaitHandle waitHandle = HandleTable.GetHandle(handle.id) as WaitHandle;
            bool ret = waitHandle.WaitOne(SchedulerTime.Now + timeout);

            Tracing.Log(Tracing.Debug, "SyncHandle.WaitOne(id={0:x8}, time=)",
                        handle.id);

            return ret;
        }

        [ExternalEntryPoint]
        public static bool WaitOne(SyncHandle handle,
                                   SchedulerTime stop)
        {
            //
            // Convert the handle to a waitHandle; wait on the waitHandle.
            //
            WaitHandle waitHandle = HandleTable.GetHandle(handle.id) as WaitHandle;
            bool ret = waitHandle.WaitOne(stop);

            Tracing.Log(Tracing.Debug, "SyncHandle.WaitOne(id={0:x8}, stop=)",
                        handle.id);

            return ret;
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe int WaitAny(SyncHandle * handles,
                                         int handleCount)
        {
            WaitHandle[] waits = Thread.CurrentThread.GetSyncHandles(handleCount);
            for (int i = 0; i < handleCount; i++) {
                waits[i] = HandleTable.GetHandle(handles[i].id) as WaitHandle;;
            }

            int ret = WaitHandle.WaitAny(waits, handleCount, SchedulerTime.MaxValue);

            Tracing.Log(Tracing.Debug,
                        "SyncHandle.WaitAny(handles={0:x8}, count={1}) = {2}",
                        (UIntPtr)handles,
                        (UIntPtr)unchecked((uint)handleCount),
                        (UIntPtr)unchecked((uint)ret));

            for (int i = 0; i < handleCount; i++) {
                waits[i] = null;
            }
            return ret;
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe int WaitAny(SyncHandle * handles,
                                         int handleCount,
                                         TimeSpan timeout)
        {
            WaitHandle[] waits = Thread.CurrentThread.GetSyncHandles(handleCount);
            for (int i = 0; i < handleCount; i++) {
                waits[i] = HandleTable.GetHandle(handles[i].id) as WaitHandle;;
            }

            int ret = WaitHandle.WaitAny(waits, handleCount,
                                         SchedulerTime.Now + timeout);

            Tracing.Log(Tracing.Debug,
                        "SyncHandle.WaitAny(handles={0:x8}, count={1}, time=) = {2}",
                        (UIntPtr)handles,
                        (UIntPtr)unchecked((uint)handleCount),
                        (UIntPtr)unchecked((uint)ret));

            for (int i = 0; i < handleCount; i++) {
                waits[i] = null;
            }
            return ret;
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe int WaitAny(SyncHandle * handles,
                                         int handleCount,
                                         SchedulerTime stop)
        {
            WaitHandle[] waits = Thread.CurrentThread.GetSyncHandles(handleCount);
            for (int i = 0; i < handleCount; i++) {
                waits[i] = HandleTable.GetHandle(handles[i].id) as WaitHandle;;
            }

            int ret = WaitHandle.WaitAny(waits, handleCount, stop);

            Tracing.Log(Tracing.Debug,
                        "SyncHandle.WaitAny(handles={0:x8}, count={1}, stop=) = {2}",
                        (UIntPtr)handles,
                        (UIntPtr)unchecked((uint)handleCount),
                        (UIntPtr)unchecked((uint)ret));

            for (int i = 0; i < handleCount; i++) {
                waits[i] = null;
            }
            return ret;
        }
    }
}
