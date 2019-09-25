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

namespace Microsoft.Singularity.V1.Threads
{
    public struct SyncHandle // : public WaitHandle
    {
        public readonly UIntPtr id; // could be moved to WaitHandle

        [Inline]
        [NoHeapAllocation]
        private SyncHandle(UIntPtr id)
        {
            this.id  = id;
        }

        [Inline]
        [NoHeapAllocation]
        public static implicit operator SyncHandle(MutexHandle handle)
        {
            return new SyncHandle(handle.id);
        }

        [Inline]
        [NoHeapAllocation]
        public static implicit operator SyncHandle(AutoResetEventHandle handle)
        {
            return new SyncHandle(handle.id);
        }

        [Inline]
        [NoHeapAllocation]
        public static implicit operator SyncHandle(ManualResetEventHandle handle)
        {
            return new SyncHandle(handle.id);
        }

        //////////////////////////////////////////////////////////////////////
        //
        // The following methods could be moved to WaitHandle if we had
        // struct inheritance.
        //
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool WaitOne(SyncHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool WaitOne(SyncHandle handle,
                                          TimeSpan timeout);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool WaitOne(SyncHandle handle,
                                          SchedulerTime stop);

        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool WaitOneNoGC(SyncHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe int WaitAny(SyncHandle * handles,
                                                int handleCount);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe int WaitAny(SyncHandle * handles,
                                                int handleCount,
                                                TimeSpan timeout);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe int WaitAny(SyncHandle * handles,
                                                int handleCount,
                                                SchedulerTime stop);
    }
}
