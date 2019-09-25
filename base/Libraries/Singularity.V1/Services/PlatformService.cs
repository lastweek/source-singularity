////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DebugService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;

namespace Microsoft.Singularity.V1.Services
{
    [AccessedByRuntime("Method called from CommonHal.cpp")]
    public struct PlatformService
    {
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool DisableInterrupts();

        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void RestoreInterrupts(bool enabled);

        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool InterruptsDisabled();

        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [CLSCompliant(false)]
        public static extern void CleanAndInvalidateDCache(UIntPtr address, UIntPtr length);

        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [CLSCompliant(false)]
        public static extern void InvalidateDCache(UIntPtr address, UIntPtr length);

        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [CLSCompliant(false)]
        public static extern void SetCacheAttributes(UIntPtr address, UIntPtr length, bool cacheable, bool bufferable);

        [NoHeapAllocation]
        [StackBound(32)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("Called from native kernel code")]
        public static extern int GetProcessorContextOffset();

        [NoHeapAllocation]
        [StackBound(32)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [AccessedByRuntime("Called from native kernel code")]
        public static extern int GetThreadContextOffset();
    }
}
