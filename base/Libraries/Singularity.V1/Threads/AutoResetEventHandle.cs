////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   AutoResetEventHandle.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.V1.Threads
{
    public struct AutoResetEventHandle // : public WaitHandle
    {
        public readonly UIntPtr id; // could be moved to WaitHandle

        [NoHeapAllocation]
        public static bool Create(
            bool initialState,
            out AutoResetEventHandle handle)
        {
            unsafe {
                fixed (AutoResetEventHandle * handlePtr = &handle) {
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
            AutoResetEventHandle * handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Dispose(AutoResetEventHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(320)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Reset(AutoResetEventHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Set(AutoResetEventHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool SetAll(AutoResetEventHandle handle);

        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool SetNoGC(AutoResetEventHandle handle);
    }
}
