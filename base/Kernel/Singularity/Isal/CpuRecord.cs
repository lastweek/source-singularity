//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
// 
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// CpuRecord defines the low-level per-cpu state maintained by the Isal layer

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

#if ISA_IX
using Microsoft.Singularity.Isal.IX;
#elif ISA_ARM
using Microsoft.Singularity.Isal.Arm;
#endif

namespace Microsoft.Singularity.Isal
{
    [NoCCtor]
    [AccessedByRuntime("referenced in c++")]
    [CLSCompliant(false)]
    [System.Runtime.InteropServices.StructLayout(LayoutKind.Sequential, Pack=4)]
    [StructAlign(16)]
    public struct CpuRecord
    {
        // Area to spill current context for debugging purposes.
        // Note this must be 16-byte aligned
        [AccessedByRuntime("referenced in c++")]
        public SpillContext       spill;

        [AccessedByRuntime("referenced in c++")]
        public int                id;

        // Interrupt stack - this must be large enough to handle our deepest possible interrupt
        // nesting.
        [AccessedByRuntime("referenced in c++")]
        public unsafe UIntPtr     interruptStackBegin;
        [AccessedByRuntime("referenced in c++")]
        public unsafe UIntPtr     interruptStackLimit;

        // Default ThreadContext - this is used for boot and (perhaps?) interrupt processing
        // when no other thread is active.
        public ThreadRecord       bootThread;

#if ISA_ARM
        public DispatchStack      dispatchStack;
#endif
    }
}
