//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// This file defines an architecture-neutral encapsulation of the state which is saved
// during a thread context switch.

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Isal.Arm
{
    // DispatchStack is a small per-cpu stack allocated to be used as the shadowed
    // sp in exception modes.  Its sole purpose is to save enough state to get
    // us back to normal execution mode.

    // The code in Interrupt.asm assumes that r4 is at offset 0 and

    [AccessedByRuntime("referenced in asm", AllFields = true)]
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential)]
    public struct DispatchStack
    {
        private uint    r4;
        private uint    sp; // aka r13

        public unsafe UIntPtr StackBegin
        {
            [NoHeapAllocation]
            get {
                fixed (uint *p = &r4) {
                    return (UIntPtr) p;
                }
            }
        }
    }
};
