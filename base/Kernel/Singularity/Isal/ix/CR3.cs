////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   CR3.cs
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
    internal struct CR3
    {
        [AccessedByRuntime("Unknown")] 
        internal const uint PWT     = 0x00000008;
        [AccessedByRuntime("Unknown")] 
        internal const uint PCD     = 0x00000010;
    }
}

