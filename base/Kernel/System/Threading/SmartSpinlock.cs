////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ProtectionDomain.cs
//
//  Note:
//
//  SmartSpinlock is an object that wraps the SpinLock struct
//  and avoids actually interlocking memory on a single-processor
//  box.
//

using Microsoft.Singularity;
using System;
using System.Runtime.CompilerServices;

namespace System.Threading
{
    [CLSCompliant(false)]
    public class SmartSpinlock
    {
#if SINGULARITY_MP
        private SpinLock spin;
#endif

        public SmartSpinlock(SpinLock.Types type)
        {
#if SINGULARITY_MP
            this.spin = new SpinLock(type);
#endif
        }

        [Inline]
        public bool Lock()
        {
            bool enabled = Processor.DisableInterrupts();
#if SINGULARITY_MP
            spin.Acquire(Thread.CurrentThread);
#endif // SINGULARITY_MP
            return enabled;
        }

        [Inline]
        public void Unlock(bool iflag)
        {
#if SINGULARITY_MP
            spin.Release(Thread.CurrentThread);
#endif // SINGULARITY_MP
            Processor.RestoreInterrupts(iflag);
        }
    }
}
