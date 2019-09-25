////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   CR0.cs
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
    internal struct CR0
    {
        [AccessedByRuntime("referenced from asm file")] 
        internal const uint PE      = 0x00000001;
        [AccessedByRuntime("referenced from asm file")] 
        internal const uint MP      = 0x00000002;
        [AccessedByRuntime("referenced from asm file")]
        internal const uint EM      = 0x00000004;
        [AccessedByRuntime("referenced from asm file")] 
        internal const uint TS      = 0x00000008;
        [AccessedByRuntime("referenced from asm file")] 
        internal const uint ET      = 0x00000010;
        [AccessedByRuntime("referenced from asm file")] 
        internal const uint NE      = 0x00000020;
        [AccessedByRuntime("referenced from asm file")]
        internal const uint WP      = 0x00010000;
        [AccessedByRuntime("referenced from asm file")]
        internal const uint AM      = 0x00040000;
        [AccessedByRuntime("referenced from asm file")] 
        internal const uint NW      = 0x20000000;
        [AccessedByRuntime("referenced from asm file")] 
        internal const uint CD      = 0x40000000;
        [AccessedByRuntime("referenced from asm file")]
        internal const uint PG      = 0x80000000;
    }
}

