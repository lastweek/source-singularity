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

namespace Microsoft.Singularity.V1.Threads
{
    public struct ManualResetEventHandle // : public WaitHandle
    {
        public readonly UIntPtr id; // could be moved to WaitHandle

        [NoHeapAllocation]
        public static bool Create(bool initialState,
                                  out ManualResetEventHandle handle)
        {
            unsafe {
                fixed (ManualResetEventHandle * handlePtr = &handle) {
                    return CreateImpl(initialState, handlePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool CreateImpl(
            bool initialState,
            ManualResetEventHandle * handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Dispose(ManualResetEventHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(320)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Reset(ManualResetEventHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Set(ManualResetEventHandle handle);
    }
}
