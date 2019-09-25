///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   StressDirect.cs
//
//  Note:
//

using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.Memory;
using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.V1.Stress
{
    [CLSCompliant(false)]
    public struct StressDirect
    {
        [ExternalEntryPoint]
        static public unsafe uint KPTest(SharedHeapService.Allocation* sharedArgs, int i)
        {
            return Microsoft.Singularity.Stress.StressDirect.KPTest((SharedHeap.Allocation*) sharedArgs, i);
        }
    }
}
