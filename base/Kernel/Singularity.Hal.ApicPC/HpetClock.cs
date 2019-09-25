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
//

namespace Microsoft.Singularity.Hal
{
    using Microsoft.Singularity.Hal.Acpi;

    using System;
    using System.Diagnostics;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

    [ CLSCompliant(false) ]
    internal class HpetClock
    {
        Hpet     hpet;
        ulong    kernelTicksAccumulated;
        uint     hpetLastUpdate;

        internal HpetClock(Hpet timer, ulong initialKernelTicks)
        {
            this.hpet                   = timer;
            this.hpetLastUpdate         = hpet.MainCounterValue32;
            this.kernelTicksAccumulated = initialKernelTicks;
        }

        internal Hpet Hpet
        {
            get { return hpet; }
        }

        [NoHeapAllocation]
        private uint DeltaHpetTicksToKernelTicks(uint delta)
        {
            // Kernel ticks are every 100ns seconds
            ulong t = delta * (ulong)hpet.PeriodFs;
            t /= 100 * 1000 * 1000;
            return (uint) t;
        }

        [NoHeapAllocation]
        internal ulong GetKernelTicks()
        {
            uint now = hpet.MainCounterValue32;
            return (this.kernelTicksAccumulated +
                    DeltaHpetTicksToKernelTicks(now - this.hpetLastUpdate)
                    );
        }

        [NoHeapAllocation]
        internal void Update()
        {
            uint now = hpet.MainCounterValue32;
            this.kernelTicksAccumulated +=
                DeltaHpetTicksToKernelTicks(now - this.hpetLastUpdate);
            this.hpetLastUpdate = now;
        }

        [NoHeapAllocation]
        public static uint UpdateFrequency(Hpet hpet)
        {
            // Compute RTC clock frequency (2^n Hz) to avoid a
            // wrap between clock interrupts.
            ulong wrapPeriodUs =
                ((ulong)0xffffffffu * hpet.PeriodFs) / (1000000 * 1000);
            uint wrapFrequency =
                1 + (uint) ((long)1000000 / (1 + wrapPeriodUs));
            uint updateFrequency = 2;   // Min freq of RTC
            while (updateFrequency < 4 * wrapFrequency) {
                updateFrequency *= 2;
            }
            return updateFrequency;
        }
    }
}
