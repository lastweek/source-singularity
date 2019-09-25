////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

namespace Microsoft.Singularity
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using System.Threading;

    using Microsoft.Singularity.V1.Services;
    using Microsoft.Singularity.V1.Threads;

    using Microsoft.Singularity.Isal;

    //
    //  Proxy class to access privileged system functions. Most of these will be 
    //  restricted to drivers only. The test whether a SIP can have access to such
    //  functions is controlled in the kernel side of the call.
    //
    
    [CLSCompliant(false)]
    [NoCCtor]
    [AccessedByRuntime("referenced in Processor.cpp")]
    public class PrivilegedGate
    {
        [NoHeapAllocation]
        [AccessedByRuntime("referenced from c++")]
        public static bool DisableInterrupts()
        {
            return Singularity.V1.Services.PlatformService.DisableInterrupts();
        }

        [NoHeapAllocation]
        [AccessedByRuntime("referenced from c++")]
        public static void RestoreInterrupts(bool enabled)
        {
            Singularity.V1.Services.PlatformService.RestoreInterrupts(enabled);
        }

        // Use this method for assertions only!
        [NoHeapAllocation]
        [AccessedByRuntime("referenced from c++")]
        public static bool InterruptsDisabled()
        {
            return Singularity.V1.Services.PlatformService.InterruptsDisabled();
        }
    }
}
