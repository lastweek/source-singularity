////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Tss.cs
//
//  Note:
//

namespace Microsoft.Singularity.Isal.IX
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    // Task State Segment
    [AccessedByRuntime("referenced from c++")]
    [StructLayout(LayoutKind.Sequential, Pack=4)]
    [CLSCompliant(false)]
    internal struct TSS64
    {
        internal uint     reserved1;

        [AccessedByRuntime("referenced in c++")]
        internal ulong      rsp0;
        [AccessedByRuntime("referenced in c++")]
        internal ulong      rsp1;
        [AccessedByRuntime("referenced in c++")] 
        internal ulong      rsp3;

        internal ulong     reserved2;

        [AccessedByRuntime("referenced in c++")]
        internal ulong ist1;
        [AccessedByRuntime("referenced in c++")]
        internal ulong ist2;
        [AccessedByRuntime("referenced in c++")]
        internal ulong ist3;
        [AccessedByRuntime("referenced in c++")]
        internal ulong ist4;
        [AccessedByRuntime("referenced in c++")]
        internal ulong ist5;
        [AccessedByRuntime("referenced in c++")]
        internal ulong ist6;
        [AccessedByRuntime("referenced in c++")]
        internal ulong ist7;

        internal ulong      reserved3;
        internal ushort     reserved4;

        [AccessedByRuntime("referenced in c++")] 
        internal ushort     io_bitmap_offset;

        // possibly followed by I/O-Permission Bitmap (up to 8 KB)
    }
}
