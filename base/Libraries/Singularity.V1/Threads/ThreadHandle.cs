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

namespace Microsoft.Singularity.V1.Threads
{
    public struct ThreadHandle
    {
        public readonly UIntPtr id;

        [NoHeapAllocation]
        public static unsafe bool Create(int threadIndex,
                                         ContainerHandle container,
                                         out ThreadHandle thread,
                                         out UIntPtr threadContext)
        {
            fixed (ThreadHandle * threadPtr = &thread) {
                fixed (UIntPtr * threadContextPtr = &threadContext) {
                    return CreateImpl(threadIndex, container, threadPtr,
                        threadContextPtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1182)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe extern bool CreateImpl(
            int threadIndex,
            ContainerHandle container,
            ThreadHandle * thread,
            UIntPtr * threadContext);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Dispose(ThreadHandle thread);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1408)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Start(ThreadHandle thread);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetAffinity(ThreadHandle thread);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void SetAffinity(ThreadHandle thread, int val);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern ThreadState GetThreadState(ThreadHandle thread);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern TimeSpan GetExecutionTime(ThreadHandle thread);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Join(ThreadHandle thread);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Join(ThreadHandle thread,
                                       TimeSpan timeout);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1216)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Join(ThreadHandle thread,
                                       SchedulerTime stop);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern ThreadHandle CurrentThread();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern UIntPtr GetThreadLocalValue();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void SetThreadLocalValue(UIntPtr value);


        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Sleep(TimeSpan timeout);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Sleep(SchedulerTime stop);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(512)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Yield();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void SpinWait(int iterations);

        //        [OutsideGCDomain]
        // [MethodImpl(MethodImplOptions.InternalCall)]
        // public static extern unsafe uint GetPrincipal(/*[out]*/ char *outprincipal, uint maxout);

        //[OutsideGCDomain]
        //[MethodImpl(MethodImplOptions.InternalCall)]
        // public static extern unsafe uint GetPrincipal(ThreadHandle handler, /*[out]*/ char *outprincipal, uint maxout);
    }
}
