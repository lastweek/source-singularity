////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Primitive stack segment manager
//

namespace Microsoft.Singularity.Memory
{

    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using Microsoft.Singularity;
    using Microsoft.Singularity.V1.Services;

    internal partial class Stacks {

        internal static unsafe void Initialize()
        {
            DebugStub.Print("Stacks.Initialize() called\n");
        }

        internal static unsafe void ReleaseResources()
        {
            DebugStub.Print("Stacks.ReleaseResources() called\n");
        }
    }
}
