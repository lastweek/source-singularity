///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   StressDirect.sg
//  Note:   Kernel diagnostics (testing and debugging)
//
//  (non-shipping extensions to kernel ABI, for testing and debugging)

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity.V1.Stress
{
    public struct StressDirect
    {
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe uint KPTest(SharedHeapService.Allocation* sharedArgs, int i);
    }
}
