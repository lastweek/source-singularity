///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

namespace Microsoft.Singularity.Hal
{
    using Microsoft.Singularity.Hal.Acpi;

    internal class Calibrate
    {
        private static uint PmDelta(uint newValue, uint oldValue)
        {
            // PmTimer may be 24 or 32 bits depending on system.
            // Simplest to treat as 24 bits.
            return (newValue - oldValue) & 0x00ffffff;
        }

        internal static void CpuCycleCounter(PMTimer pmTimer)
        {
            uint  pmLast  = pmTimer.Value;
            ulong tscLast = Processor.CycleCount;

            uint  pmLimit = PMTimer.FrequencyHz / 15;
            uint  pmAccum = 0;
            ulong tscNow  = 0;

            // Initial measurements
            tscLast = Processor.CycleCount;
            pmLast  = pmTimer.Value;

            // Measurement loop
            do
            {
                tscNow      = Processor.CycleCount;
                uint pmNow  = pmTimer.Value;
                pmAccum    += PmDelta(pmNow, pmLast);
                pmLast      = pmNow;
            } while (pmAccum < pmLimit);

            ulong tscHz = PMTimer.FrequencyHz * (tscNow - tscLast) / pmAccum;
            DebugStub.Print("Cpu{0}: TSC frequency {1} Hz\n",
                            __arglist(Processor.CurrentProcessor.Id, tscHz));
            Processor.CyclesPerSecond = tscHz;
        }

        internal static void ApicTimer(PMTimer pmTimer, ApicTimer apicTimer)
        {
            apicTimer.SetDivisor(1);
            apicTimer.SetOneShot();
            apicTimer.SetInterruptEnabled(false);
            apicTimer.SetInitialCount(~0u);

            uint apicLast = apicTimer.Value;
            uint pmLast   = pmTimer.Value;

            uint  pmLimit = PMTimer.FrequencyHz / 15;
            uint  pmAccum = 0;
            uint  apicNow = 0;

            // Initial measurements
            apicLast = apicTimer.Value;
            pmLast   = pmTimer.Value;
            do
            {
                apicNow     = apicTimer.Value;
                uint pmNow  = pmTimer.Value | 0xff000000;
                pmAccum    += PmDelta(pmNow, pmLast);
                pmLast      = pmNow;
            } while (pmAccum < pmLimit);

            ulong apicHz = PMTimer.FrequencyHz * (ulong)(apicLast - apicNow) / pmAccum;
            DebugStub.Print("Cpu{0}: APIC timer frequency {1} Hz\n",
                            __arglist(Processor.CurrentProcessor.Id, apicHz));

            apicTimer.SetBusFrequency((uint)apicHz);
        }
    }
}
