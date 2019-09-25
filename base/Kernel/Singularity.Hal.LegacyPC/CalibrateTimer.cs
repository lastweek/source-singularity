///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: CalibrateTimers.cs
//
//  Note:
//

// #define VERBOSE

using System;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Hal.Acpi;

namespace Microsoft.Singularity.Hal
{
    [ CLSCompliant(false) ]
    internal sealed class CalibrateTimers
    {
        private static int ApproxLog10(ulong value)
        {
            ulong thresh = 4;
            for (int i = 0; i < 20; i++) {
                if (thresh >= value) {
                    return i;
                }
                thresh *= 10;
            }
            return 0;
        }

        private static int MinSpread(ulong [] values, int width)
        {
            ulong maxIre = 0; // Inverse-relative error
            int   minCenter = 0;

            for (int i = 0; i < values.Length - width; i++) {
                ulong delta = values[i + width - 1] - values[i];
                ulong ire = values[i + width / 2] / (delta + 1);
                if (ire > maxIre) {
                    maxIre = ire;
                    minCenter = i + width / 2;
                }
            }
            return minCenter;
        }

        private static void DisplayResults(ulong tscHz, int i8254Hz)
        {
            DebugStub.Print("TSC measured at {0} MHz\n",
                            __arglist((int)(tscHz / 1000000)));
            DebugStub.Print("i8254 measured at {0} Hz\n",
                            __arglist(i8254Hz));
        }

        internal static bool Run(PMTimer pmtimer, Timer8254LegacyPC i8254)
        {
            const int testRuns = 8;
            int attempts = 0;

            const uint  pmMask    = 0xffffffu;
            const ulong tscMask   = 0xffffffffffff;
            const int   i8254Mask = 0xffff;

            ulong [] tscHz    = new ulong[testRuns];
            ulong [] i8254Hz  = new ulong[testRuns];
            uint  [] pmGoal   = new uint[testRuns];
            uint  [] pmActual = new uint[testRuns];

            i8254.Timer2Start();

          measure:
            attempts ++;
            for (uint i = 0; i < testRuns; i++) {
                uint testHz = 2u + (i % 5u);

                uint pmAccum = 0;
                uint pmLast  = pmtimer.Value & pmMask;
                uint pmEnd   = PMTimer.FrequencyHz / testHz;

                ulong tscStart = Processor.CycleCount;
                ulong tscEnd   = 0;

                int i8254Accum = 0;
                int i8254Last  = i8254.Timer2Read();

                while (pmAccum < pmEnd) {
                    // Spin to burn on few
                    // clock cycles.  On real hardware we stall
                    // reading the timers.  On VPC we see the
                    // PMTimer go backwards occasionally when
                    // hammering it so we call SpinWait to
                    // reduce the chance of observing it go
                    // backwards.
                    //
                    // Note: We explicitly use Thread.SpinWait
                    // since it will not be optimized out,
                    // unlike a simple spin loop.
                    System.Threading.Thread.SpinWait(10000);

                    uint pmNow = pmtimer.Value & pmMask;
                    if (pmNow < pmLast) {
                        // On VPC the PM
                        // timer occasionally goes backwards and
                        // this leads to bogus calibration
                        // points.
                        if (pmLast - pmNow < PMTimer.FrequencyHz / 2) {
                            // ignore measurement
                            continue;
                        }
                        // Clock wrap, measurement okay.
                    }
                    pmAccum += (pmNow + (pmMask + 1) - pmLast) & pmMask;
                    pmLast = pmNow;

                    tscEnd = Processor.CycleCount;

                    int i8254Now = i8254.Timer2Read();
                    i8254Accum += ((i8254Mask + 1) + i8254Last - i8254Now) &
                        i8254Mask;
                    i8254Last = i8254Now;
                }

                ulong tscDelta = (tscEnd + (tscMask + 1) - tscStart) & tscMask;

                tscHz[i]   = tscDelta * PMTimer.FrequencyHz / pmAccum;
                i8254Hz[i] = (ulong)i8254Accum * PMTimer.FrequencyHz / pmAccum;
                pmGoal[i]   = pmEnd;
                pmActual[i] = pmAccum;
            }

#region -*- temporary failure debugging support -*-

            ulong[] tscHzBackup = new ulong[tscHz.Length];
            ulong[] i8254HzBackup = new ulong[i8254Hz.Length];
            Array.Copy(tscHz, tscHzBackup, tscHz.Length);
            Array.Copy(i8254Hz, i8254HzBackup, i8254Hz.Length);
#endregion

            Array.Sort(tscHz);
            Array.Sort(i8254Hz);

            bool noisyClock = false;

            // Re-measure if values are obviously bogus as can occur with
            // VPC.  Check is minimum value is less than n% of maximum
            // value.
            bool tscFailed   = tscHz[0] < 3 * tscHz[testRuns - 1] / 4;
            bool i8254Failed = i8254Hz[0] < 3 * i8254Hz[testRuns - 1] / 4;

            if (tscFailed || i8254Failed) {
                if (attempts < 10) {
                    noisyClock = true;
                    DebugStub.Print("CLOCK CALIBRATION FAILED");
                    if (tscFailed && i8254Failed) {
                        DebugStub.Print(" (tsc and i2854) ");
                    }
                    else if (tscFailed) {
                        DebugStub.Print(" (tsc only) " );
                    }
                    else {
                        DebugStub.Print(" (i8254 only) " );
                    }
                    DebugStub.Print("RETRYING.\n");
                    for (int i = 0; i < tscHzBackup.Length; i++) {
                        DebugStub.Print("tscHz {0} i8254Hz {1} pmGoal {2} pmActual {3}\n",
                                        __arglist(tscHzBackup[i],
                                                  i8254HzBackup[i],
                                                  pmGoal[i],
                                                  pmActual[i]));
                    }
                    goto measure;
                }
                else {
                    DebugStub.Print("ALL CLOCK CALIBRATION ATTEMPTS FAILED.\n");
                    // TODO:
                    //   Try to calibrate with rtClock
                    //     SlowCalibration(rtClock, timer8254);
                    Processor.CyclesPerSecond = 1800 * 1000 * 1000;
                    i8254.SetTicksPerSecond(1193180);
                    return true;
                }
            }

            ulong tscHzEstimate   = tscHz[MinSpread(tscHz, 3)];
            int   i8254HzEstimate = (int) i8254Hz[MinSpread(i8254Hz, 3)];

            DisplayResults(tscHzEstimate, i8254HzEstimate);

            // Set measured frequencies in appropriate places.
            Processor.CyclesPerSecond = tscHzEstimate;
            i8254.SetTicksPerSecond(i8254HzEstimate);

            //
            // Range of measurements is a pretty good indicator of VPCness
            // since it may have been descheduled during these measurements
            // so timer measurements will be poor.
            //
            int oValue = ApproxLog10(tscHzEstimate);
            int oRange = ApproxLog10(tscHz[testRuns - 1] - tscHz[0]);
            if (oValue - oRange < 5) {
                DebugStub.Print("*** Noisy timing measurements.  Looks like measurement on VPC or bad hardware. ***\n");
                noisyClock = true;
            }
            return noisyClock;
        }

        internal static void Run(RTClockLegacyPC rtc, Timer8254LegacyPC i8254)
        {
            // This test uses the RTC's update-in-progress bit, UIP, as
            // a measure of 1 second of time.  The UIP set period is
            // around 240us which means we can safely read the
            // i8254 in a loop without worrying about missing the
            // bit being set / cleared because of i/o operations.
            //
            // This test fails horribly on VPC.  It has problems with the
            // update-in-progress bit in the RTC.  Fortunately we should
            // not get here on VPC.
            //
            // NB This routine does not try to be as rigorous as
            // the PM Timer version as each calibration run
            // takes much longer.

            const int testRuns = 2;

            int i8254Last  = 0;
            int i8254Now   = 0;
            int i8254Accum = 0;
            int [] i8254Hz = new int [testRuns];

            ulong tscLast = 0;
            ulong tscNow  = 0;
            ulong [] tscHz = new ulong[testRuns];

            i8254.Timer2Start();

            do
            {
                tscLast   = Processor.CycleCount;
                i8254Last = i8254.Timer2Read();
            } while (rtc.UpdateInProgress() == false);

            for (int i = 0; i < testRuns; i++) {
                while (rtc.UpdateInProgress() == true)
                    ;

                do
                {
                    tscNow = Processor.CycleCount;

                    i8254Now    = i8254.Timer2Read();
                    i8254Accum += (0x10000 + i8254Last - i8254Now) & 0xffff;
                    i8254Last   = i8254Now;
                }
                while (rtc.UpdateInProgress() == false);

                tscHz[i] = (tscNow + 0x1000000000000 - tscLast)&0xffffffffffff;
                tscLast = tscNow;

                i8254Hz[i] = i8254Accum;
                i8254Accum = 0;
            }

            DisplayResults(tscHz[testRuns - 1], i8254Hz[testRuns - 1]);

            Processor.CyclesPerSecond = tscHz[testRuns - 1];
            i8254.SetTicksPerSecond(i8254Hz[testRuns - 1]);
        }
    }
}
