////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DeliveryHandle.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.V1.Services
{
    public struct DeliveryHandle
    {
        public readonly UIntPtr id;

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Dispose(DeliveryHandle handle);
    }
}
