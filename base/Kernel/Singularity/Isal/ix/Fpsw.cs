////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Fpsw.cs
//
//  Note:
//

namespace Microsoft.Singularity.Isal.IX
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from asm file")]
    internal struct Fpsw
    {
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort Busy                  = 0x8000;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort C3                    = 0x4000;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort Top                   = 0x3800;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort C2                    = 0x0400;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort C1                    = 0x0200;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort C0                    = 0x0100;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort ErrorSummary          = 0x0080;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort StackFaultError       = 0x0040;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort PrecisionError        = 0x0020;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort UnderflowError        = 0x0010;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort OverflowError         = 0x0008;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort ZeroDivideError       = 0x0004;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort DenormalOperandError  = 0x0002;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort InvalidOperationError = 0x0001;

        internal const ushort ErrorClearMask        = 0xb800;
    }
}

