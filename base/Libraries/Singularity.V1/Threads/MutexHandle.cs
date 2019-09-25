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

namespace Microsoft.Singularity.V1.Threads
{
    public struct MutexHandle // : public WaitHandle
    {
        public readonly UIntPtr id; // could be moved to WaitHandle

        [NoHeapAllocation]
        public static bool Create(bool initiallyOwned,
                                  out MutexHandle handle)
        {
            unsafe {
                fixed (MutexHandle * handlePtr = &handle) {
                    return CreateImpl(initiallyOwned, handlePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool CreateImpl(
            bool initiallyOwned,
            MutexHandle * handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Dispose(MutexHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Release(MutexHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool IsOwnedByCurrentThread(MutexHandle handle);
    }
}
