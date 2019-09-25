////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ThreadHandle.cs
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
    //| <include path='docs/doc[@for="ThreadHandle"]/*' />
    [CLSCompliant(false)]
    public struct ThreadHandle
    {
        public readonly UIntPtr id;

        public static readonly ThreadHandle Zero = new ThreadHandle();

        internal ThreadHandle(UIntPtr id)
        {
            this.id = id;
        }

        [ExternalEntryPoint]
        public static unsafe bool CreateImpl(
            int threadIndex,
            ContainerHandle container,
            ThreadHandle * handle,
            UIntPtr * threadContext)
        {
            return Create(threadIndex, container, out *handle,
                out *threadContext);
        }

        public static unsafe bool Create(int threadIndex,
                                         ContainerHandle container,
                                         out ThreadHandle handle,
                                         out UIntPtr threadContext)
        {
            bool ret = Thread.CurrentProcess.CreateThread(threadIndex, out handle, out threadContext);
            Tracing.Log(Tracing.Debug, "ThreadHandle.Create(index={0}, cont={1:x8}) = {2:x8}",
                        (UIntPtr)unchecked((uint)threadIndex), container.id, handle.id);
            return ret;
        }

        [ExternalEntryPoint]
        public static void Dispose(ThreadHandle handle)
        {
            Tracing.Log(Tracing.Debug, "ThreadHandle.Dispose(id={0:x8})", handle.id);
            Thread.CurrentProcess.ReleaseHandle(handle.id);
        }

        [ExternalEntryPoint]
        public static void Start(ThreadHandle handle)
        {
            Thread thread = HandleTable.GetHandle(handle.id) as Thread;
            Tracing.Log(Tracing.Debug, "ThreadHandle.Start(id={0:x8})", handle.id);

            thread.Start();
        }

        [ExternalEntryPoint]
        public static int GetAffinity(ThreadHandle handle)
        {
            int affinity = Processor.GetCurrentProcessorId();
            Tracing.Log(Tracing.Debug, "ThreadHandle.GetAffinity(id={0:x8}, out affinity={1})",
                        handle.id, (UIntPtr)unchecked(affinity));
            return affinity;
        }

        [ExternalEntryPoint]
        public static void SetAffinity(ThreadHandle handle, int affinity)
        {

            Tracing.Log(Tracing.Debug, "ThreadHandle.SetAffinity(id={0:x8}, affinity={1})",
                        handle.id, (UIntPtr)unchecked(affinity));

            Thread thread = HandleTable.GetHandle(handle.id) as Thread;
            thread.SetAffinity(affinity);
        }

        [ExternalEntryPoint]
        public static ThreadState GetThreadState(ThreadHandle handle)
        {
            Thread thread = HandleTable.GetHandle(handle.id) as Thread;
            ThreadState state = (ThreadState)thread.ThreadState;

            Tracing.Log(Tracing.Debug, "ThreadHandle.GetThreadState(id={0:x8}, out state={1})",
                        handle.id, (UIntPtr)unchecked((uint)state));

            return state;
        }

        [ExternalEntryPoint]
        public static TimeSpan GetExecutionTime(ThreadHandle handle)
        {
            Thread thread = HandleTable.GetHandle(handle.id) as Thread;
            TimeSpan ts = thread.ExecutionTime;

            Tracing.Log(Tracing.Debug, "ThreadHandle.GetExecutionTime(id={0:x8}, out time=)",
                        handle.id);
            return ts;
        }

        [ExternalEntryPoint]
        public static bool Join(ThreadHandle handle)
        {
            Thread thread = HandleTable.GetHandle(handle.id) as Thread;

            bool ret = true;
            thread.Join();
            Tracing.Log(Tracing.Debug, "ThreadHandle.Join(id={0:x8})", handle.id);

            return ret;
        }

        [ExternalEntryPoint]
        public static bool Join(ThreadHandle handle, TimeSpan timeout)
        {
            Thread thread = HandleTable.GetHandle(handle.id) as Thread;

            bool ret = thread.Join(timeout);
            Tracing.Log(Tracing.Debug, "ThreadHandle.Join(id={0:x8}, time=)", handle.id);

            return ret;
        }

        [ExternalEntryPoint]
        public static bool Join(ThreadHandle handle, SchedulerTime stop)
        {
            Thread thread = HandleTable.GetHandle(handle.id) as Thread;

            bool ret = thread.Join(stop);
            Tracing.Log(Tracing.Debug, "ThreadHandle.Join(id={0:x8}, stop=)", handle.id);

            return ret;
        }

        [ExternalEntryPoint]
        public static ThreadHandle CurrentThread()
        {
            Tracing.Log(Tracing.Debug, "ThreadHandle.CurrentThread()");
            return Thread.CurrentThread.Handle;
        }

        [CLSCompliant(false)]
        [ExternalEntryPoint]
        public static UIntPtr GetThreadLocalValue()
        {
            return Thread.GetThreadLocalValue();
        }

        [CLSCompliant(false)]
        [ExternalEntryPoint]
        public static void SetThreadLocalValue(UIntPtr value)
        {
            Thread.SetThreadLocalValue(value);
        }

        [ExternalEntryPoint]
        public static void Sleep(TimeSpan timeout)
        {
            Tracing.Log(Tracing.Debug, "ThreadHandle.Sleep(time=)");

            Thread.Sleep(timeout);
        }

        [ExternalEntryPoint]
        public static void Sleep(SchedulerTime stop)
        {
            Tracing.Log(Tracing.Debug, "ThreadHandle.Sleep(stop=)");

            Thread.Sleep(stop);
        }

        [ExternalEntryPoint]
        public static void Yield()
        {
            Tracing.Log(Tracing.Debug, "ThreadHandle.Yield()");

            Thread.Yield();
        }

        [ExternalEntryPoint]
        public static void SpinWait(int iterations)
        {
            Tracing.Log(Tracing.Debug, "ThreadHandle.SpinWait(iter={0})",
                        (UIntPtr)unchecked((uint)iterations));

            Thread.SpinWait(iterations);
        }

        //[ExternalEntryPoint]
        //public static unsafe uint GetPrincipal(/*[out]*/ char *outprincipal, uint maxout)
        //{
        //    Tracing.Log(Tracing.Debug, "ThreadHandle.GetPrincipal (using CurrentThread)");

        //    string name = Thread.CurrentThread.Process.Principal.Name;
        //    if (outprincipal == null)
        //        return (uint)name.Length;
        //    return (uint)name.InternalGetChars(outprincipal, (int)maxout);
        // }

        //[ExternalEntryPoint]
        //public static unsafe uint GetPrincipal(ThreadHandle handle, /*[out]*/ char *outprincipal, uint maxout)
        //{
        //    Tracing.Log(Tracing.Debug, "ThreadHandle.GetPrincipal (using a handle)");

        //    Thread thread = HandleTable.GetHandle(handle.id) as Thread;
        //    string name = thread.Process.Principal.Name;
        //    if (outprincipal == null)
        //        return (uint)name.Length;
        //    return (uint)name.InternalGetChars(outprincipal, (int)maxout);
        //}

    }
}
