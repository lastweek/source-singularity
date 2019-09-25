////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using Microsoft.Singularity;
using System;
using System.Runtime.CompilerServices;

namespace System.Threading
{

    ///
    // Prevents preemption by disabling interrupts.
    // 
    [NoCCtor]
    [CLSCompliant(false)]
    public struct PreemptionLock
    {
        [Inline]
        [NoHeapAllocation]
        public bool Lock()
        {
#if TRACE
            Tracing.Log(Tracing.Debug, "PreemptionLock.Acquire()");
#endif
            return Processor.DisableLocalPreemption();
        }

        [Inline]
        [NoHeapAllocation]
        public void Unlock(bool iflag)
        {
#if TRACE
            Tracing.Log(Tracing.Debug, "PreemptionLock.Release()");
#endif
            Processor.RestoreLocalPreemption(iflag);
        }
    }
}
