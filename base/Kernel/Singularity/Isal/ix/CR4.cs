////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   CR4.cs
//
//  Note:
//

namespace Microsoft.Singularity.Isal.IX
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    [CLSCompliant(false)]
    [AccessedByRuntime("Unknown")]
    internal struct CR4
    {
        [AccessedByRuntime("Unknown")]
        internal const uint VME     = 0x00000001;
        [AccessedByRuntime("Unknown")]
        internal const uint PVI     = 0x00000002;
        [AccessedByRuntime("Unknown")]
        internal const uint TSD     = 0x00000004;
        [AccessedByRuntime("Unknown")]
        internal const uint DE      = 0x00000008;
        [AccessedByRuntime("Unknown")]
        internal const uint PSE     = 0x00000010;
        [AccessedByRuntime("Unknown")]
        internal const uint PAE     = 0x00000020;
        [AccessedByRuntime("Unknown")]
        internal const uint MCE     = 0x00000040;
        [AccessedByRuntime("Unknown")]
        internal const uint PGE     = 0x00000080;
        [AccessedByRuntime("Unknown")]
        internal const uint PCE     = 0x00000100;       // Enable access to perf counters.
        [AccessedByRuntime("Unknown")]
        internal const uint OSFXSR  = 0x00000200;       // FXSAVE
        [AccessedByRuntime("Unknown")]
        internal const uint OSXMMEXCPT = 0x00000400;    // SSE
    }
}
