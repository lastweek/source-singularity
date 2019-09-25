////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EFlags.cs
//
//  Note:
//

namespace Microsoft.Singularity.Isal.IX
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from C++")]
    internal struct EFlags
    {
        // System flags in the EFLAGS register

        [AccessedByRuntime("referenced from C++")]
        internal const uint CF     = 0x00000001;   // Carry
        [AccessedByRuntime("referenced from C++")]
        internal const uint VF     = 0x00000002;   // Valid
        [AccessedByRuntime("referenced from C++")]
        internal const uint PF     = 0x00000004;   // Parity
        [AccessedByRuntime("referenced from C++")]
        internal const uint AF     = 0x00000010;   // Aux. Carry
        [AccessedByRuntime("referenced from C++")]
        internal const uint ZF     = 0x00000040;   // Zero
        [AccessedByRuntime("referenced from C++")]
        internal const uint SF     = 0x00000080;   // Sign
        [AccessedByRuntime("referenced from C++")]
        internal const uint TF     = 0x00000100;   // Trap (SS)
        [AccessedByRuntime("referenced from C++")]
        internal const uint IF     = 0x00000200;   // Interruptible
        [AccessedByRuntime("referenced from C++")]
        internal const uint DF     = 0x00000400;   // Direction
        [AccessedByRuntime("referenced from C++")]
        internal const uint OF     = 0x00000800;   // Overflow
        [AccessedByRuntime("referenced from C++")]
        internal const uint IOPL   = 0x00003000;   // I/O Level
        [AccessedByRuntime("referenced from C++")]
        internal const uint NT     = 0x00004000;   // Nested Task
        [AccessedByRuntime("referenced from C++")]
        internal const uint RF     = 0x00010000;   // Resume
        [AccessedByRuntime("referenced from C++")]
        internal const uint VM     = 0x00020000;   // Virtual-8086
        [AccessedByRuntime("referenced from C++")]
        internal const uint AC     = 0x00040000;   // Alignment
        [AccessedByRuntime("referenced from C++")]
        internal const uint VIF    = 0x00080000;   //
        [AccessedByRuntime("referenced from C++")]
        internal const uint VIP    = 0x00100000;
        [AccessedByRuntime("referenced from C++")]
        internal const uint ID     = 0x00200000;
    }

    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from C++")]
    internal struct EFlagsShift
    {
        [AccessedByRuntime("referenced from C++")]
        internal const uint IF = 9;
    }
}
