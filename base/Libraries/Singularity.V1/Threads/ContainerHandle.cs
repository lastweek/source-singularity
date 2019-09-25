////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ContainerHandle.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.V1.Threads
{
    public struct ContainerHandle
    {
        public readonly UIntPtr id;

        [NoHeapAllocation]
        public static bool Create(out ContainerHandle container)
        {
            unsafe {
                fixed (ContainerHandle * containerPtr = &container) {
                    return CreateImpl(containerPtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1170)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool CreateImpl(ContainerHandle * container);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Dispose(ContainerHandle container);
    }
}
