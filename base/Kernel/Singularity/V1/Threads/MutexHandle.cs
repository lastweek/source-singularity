////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MutexHandle.cs
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
    public struct MutexHandle // : public SyncHandle
    {
        public readonly UIntPtr id; // could be moved to SyncHandle

        public static readonly MutexHandle Zero = new MutexHandle();

        internal MutexHandle(UIntPtr id)
        {
            this.id = id;
        }

        [ExternalEntryPoint]
        public static unsafe bool CreateImpl(
            bool initiallyOwned,
            MutexHandle * handle)
        {
            return Create(initiallyOwned, out *handle);
        }

        public static bool Create(bool initiallyOwned,
                                  out MutexHandle handle)
        {
            //
            // Create a new mutex, and a handle in the current process
            // to hold it.
            //
            //  Note: the mutex is created as a non-kernel object so that
            //  SIP threads owning mutex can be forcibly stopped
            //
            handle = new MutexHandle(Thread.CurrentProcess.AllocateHandle(
                                         new Mutex(initiallyOwned, false)));

            Tracing.Log(Tracing.Debug, "MutexHandle.Create(, out id={0:x8})",
                        handle.id);
            return true;
        }

        [ExternalEntryPoint]
        public static void Dispose(MutexHandle handle)
        {
            Tracing.Log(Tracing.Debug, "MutexHandle.Dispose(id={0:x8})",
                        handle.id);

            //
            // Releasing the handle will allow the mutex to be
            // garbage-collected.
            //
            Thread.CurrentProcess.ReleaseHandle(handle.id);
        }

        [ExternalEntryPoint]
        public static void Release(MutexHandle handle)
        {
            Tracing.Log(Tracing.Debug, "MutexHandle.Release(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a mutex; release the mutex.
            //
            Mutex mutex = HandleTable.GetHandle(handle.id) as Mutex;
            mutex.ReleaseMutex();
        }

        [ExternalEntryPoint]
        public static bool IsOwnedByCurrentThread(MutexHandle handle)
        {
            Tracing.Log(Tracing.Debug, "MutexHandle.IsOwnedByCurrentThread(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a mutex; check the ownership of the mutex.
            //
            Mutex mutex = HandleTable.GetHandle(handle.id) as Mutex;
            return mutex.IsOwnedByCurrentThread();
        }
    }
}
