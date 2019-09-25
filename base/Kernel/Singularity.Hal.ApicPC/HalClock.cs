///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//
//  This file is an implementation of Interfaces/Hal/HalClock.csi
//
//  Having some form of time working when one or processors may be in the
//  debugger makes this hard and expensive.
//

#if SINGULARITY_MP
#error "This file is not for MP builds."
#endif // SINGULARITY_MP

namespace Microsoft.Singularity.Hal
{
    using Microsoft.Singularity.Hal.Acpi;

    using System;
    using System.Diagnostics;
    using System.Runtime.CompilerServices;

    public class HalClockApic : HalClock
    {
        Apic      apic;
        PMClock   pmClock;
        RTClockApic   rtClock;
        HpetClock hpetClock;

        long      lastKernelTicks;
        ulong     tscSnapshot;
        bool      tscSnapshotValid = false;
        long      ticksSnapshot;
        int       tickScale = 0;
        const int tickRoll = 24;

        internal HalClockApic(Apic apic, RTClockApic rtClock, PMClock /* ! */ pmClock)
        {
            this.apic        = apic;
            this.rtClock     = rtClock;
            this.pmClock     = pmClock;
            this.hpetClock   = null;
            this.tscSnapshot = 0;
            this.ticksSnapshot = 0;
            int ticksPerKernelTick =
                (int)(Processor.CyclesPerSecond / 10000000);
            this.tickScale = (1 << tickRoll) / ticksPerKernelTick;
            lastKernelTicks = InternalGetKernelTicks();
        }

        [NoHeapAllocation]
        public override long GetKernelTicks()
        {
            bool en = Processor.DisableInterrupts();
            try {
                long kernelTicks = InternalGetKernelTicks();
                if (kernelTicks >= lastKernelTicks ||
                    (kernelTicks < 0 && lastKernelTicks > 0)) {
                    lastKernelTicks = kernelTicks;
                    return kernelTicks;
                }
                else {
                    // Skew from switching between tsc and underlying clock
                    DebugStub.Assert(lastKernelTicks - kernelTicks < 5000000);
                    return lastKernelTicks;
                }
            }
            finally {
                Processor.RestoreInterrupts(en);
            }
        }

        [NoHeapAllocation]
        private long InternalGetKernelTicks()
        {
            if (!tscSnapshotValid) {
                if (hpetClock == null) {
                    ticksSnapshot = (long) pmClock.GetKernelTicks();

                }
                else {
                    ticksSnapshot = (long) hpetClock.GetKernelTicks();
                }
                tscSnapshot      = Processor.CycleCount;
                tscSnapshotValid = true;

                return ticksSnapshot;
            }
            else {
                long tscDelta  = (long)(Processor.CycleCount - tscSnapshot);
                long tickDelta = (tscDelta * tickScale) >> tickRoll;
                return ticksSnapshot + tickDelta;
            }
        }

        public byte Interrupt
        {
            [NoHeapAllocation]
            get { return rtClock.Interrupt; }
        }

        [NoHeapAllocation]
        public override void ClearInterrupt()
        {
            Microsoft.Singularity.Hal.Platform p = Microsoft.Singularity.Hal.Platform.ThePlatform;

            if (hpetClock == null) {
                pmClock.Update();
            }
            else {
                hpetClock.Update();
            }
	    rtClock.ClearInterrupt();
            tscSnapshotValid = false;
        }

        internal void SwitchToHpetClock(HpetClock hc)
        {
            // Change rt clock interrupt frequency to appropriate
            // rate for HPET main clock.
            rtClock.SetFrequency(HpetClock.UpdateFrequency(hc.Hpet));
            hpetClock = hc;
            DebugStub.Print("Hal switching to HpetClock.\n");
        }

        [NoHeapAllocation]
        public override void CpuResumeFromHaltEvent()
        {
            tscSnapshotValid = false;
        }

        [NoHeapAllocation]
        public override long GetRtcTime()
        {
            return rtClock.GetBootTime() + GetKernelTicks();
        }

        public override void SetRtcTime(long newRtcTime)
        {
            rtClock.SetRtcTime(newRtcTime, GetKernelTicks());
        }
    }
}
