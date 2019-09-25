//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
// 
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ThreadRecord defines the low-level per-thread state maintained by the Isal layer

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

#if ISA_IX
using Microsoft.Singularity.Isal.IX;
#endif

namespace Microsoft.Singularity.Isal
{
    [NoCCtor]
    [AccessedByRuntime("referenced in c++")]
    [CLSCompliant(false)]
    [System.Runtime.InteropServices.StructLayout(LayoutKind.Sequential, Pack=4)]
    [StructAlign(16)]
    public struct ThreadRecord
    {
        // Spill context to use with this thread's execution is preempted
        // Note this must be 16-byte aligned
        [AccessedByRuntime("referenced in c++")]
        public SpillContext           spill;

        // The current stack limit for bounds checks - this is kept current with 
        // thread context switches. 
        // 
        // While this is really logically associated with the Cpu rather than
        // the thread, it is kept in the ThreadRecord since accesses into the Cpu
        // record would be non-atomic (in the case where a thread is interrupted and
        // migrates across processors).
        //
        // There are several cases where the activeStackLimit will differ from the
        // stackLimit:
        //    - when we switch to the interrupt stack
        //    - after we call SetCurrentThreadRecord, but before we do a context
        //            restore on that thread's context.

        [AccessedByRuntime("referenced in c++")]
        public UIntPtr                activeStackLimit;
    }
}

