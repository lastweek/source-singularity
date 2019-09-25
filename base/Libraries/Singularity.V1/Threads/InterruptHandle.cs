////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   InterruptHandle.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Microsoft.Singularity.V1.Threads
{
    public struct InterruptHandle // : public WaitHandle
    {
        public readonly UIntPtr id; // could be moved to WaitHandle

        [NoHeapAllocation]
        public static bool Create(
            byte irq,
            out InterruptHandle handle)
        {
            unsafe {
                fixed (InterruptHandle * handlePtr = &handle) {
                    return CreateImpl(irq, handlePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool CreateImpl(
            byte irq,
            InterruptHandle * handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Dispose(InterruptHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Wait(InterruptHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Pulse(InterruptHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Ack(InterruptHandle handle);
    }
}
