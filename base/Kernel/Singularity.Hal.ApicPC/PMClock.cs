///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//
//  HalClock is expected to call PMClock's time maintenance
//  functions with a spin lock held.

namespace Microsoft.Singularity.Hal
{
    using Microsoft.Singularity.Hal.Acpi;

    using System;
    using System.Diagnostics;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

    [ CLSCompliant(false) ]
    internal class PMClock
    {
        PMTimer pmTimer;
        ulong   kernelTicksTotal;
        ulong   pmResidual;
        uint    pmLastUpdate;

        internal PMClock(PMTimer timer)
        {
            this.pmTimer          = timer;
            this.kernelTicksTotal = 0;
            this.pmResidual       = 0;
            this.pmLastUpdate     = pmTimer.Value;
        }

        [NoHeapAllocation]
        private static ulong PMTicksToKernelTicks(ulong pmTicks)
        {
            // REVIEW: Does this need to be a ulong?
            //
            // PM frequency is 3579545Hz.  Kernel tick frequency is 10MHz.
            // The conversion is:
            // kTicks = pmTicks * 10000000 / 3579545
            //        = pmTicks * (2 + 0xcb2cb8bed / 0x1000000000)
            //        = pmTicks * (0x2cb / 0x100 + 0x2cb / 0x100000 +
            //                     0x8bed / 0x1000000000)
            ulong tmp = pmTicks * 0x2cb;
            return (tmp >> 8) + (tmp >> 20) + ((pmTicks * 0x8bed) >> 36);
        }

        [NoHeapAllocation]
        private static uint PmDeltaTicks(uint pmNow, uint pmLast)
        {
            // We unconditionally round down to 24-bits as
            // values from PM timer may be 24-bit or 32-bit.
            return (pmNow - pmLast) & 0xffffff;
        }

        [NoHeapAllocation]
        internal ulong GetKernelTicks()
        {
            uint pmNow   = pmTimer.Value;
            uint pmDelta = PmDeltaTicks(pmNow, this.pmLastUpdate);
            return this.kernelTicksTotal +
                PMTicksToKernelTicks(this.pmResidual + pmDelta);
        }

        [NoHeapAllocation]
        internal void Update()
        {
            uint pmNow = pmTimer.Value;
            this.pmResidual += PmDeltaTicks(pmNow, this.pmLastUpdate);
            // Transfer time from residual to accumulated
            // time in one second intervals since there is
            // an integral relationship between the two.
            while (this.pmResidual >= PMTimer.FrequencyHz) {
                this.kernelTicksTotal += 10000000; // Kernel tick freq
                this.pmResidual       -= PMTimer.FrequencyHz;
            }
            this.pmLastUpdate = pmNow;
        }
    }
}
