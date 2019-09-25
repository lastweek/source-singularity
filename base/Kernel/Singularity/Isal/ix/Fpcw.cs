////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Fpcw.cs
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
    internal struct Fpcw
    {
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort RoundControlMask      = 0x0c00;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort PrecisionControlMask  = 0x0300;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort PrecisionMask         = 0x0020;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort UnderflowMask         = 0x0010;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort OverflowMask          = 0x0008;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort ZeroDivideMask        = 0x0004;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort DenormalOperandMask   = 0x0002;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort InvalidOperationMask  = 0x0001;

        [AccessedByRuntime("referenced from asm file")]
        internal const ushort RoundChop             = 0x0c00;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort RoundUp               = 0x0800;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort RoundDown             = 0x0400;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort RoundNear             = 0x0000;

        [AccessedByRuntime("referenced from asm file")]
        internal const ushort Precision24           = 0x0000;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort Precision53           = 0x0200;
        [AccessedByRuntime("referenced from asm file")]
        internal const ushort Precision64           = 0x0300;
    }
}

