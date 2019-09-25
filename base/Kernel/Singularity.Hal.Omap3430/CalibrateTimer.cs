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

namespace Microsoft.Singularity.Hal
{
    [CLSCompliant(false)]
    internal sealed class CalibrateTimers
    {
        internal static void Run(HalClockNull clock, TimerOmap3430 gpTimer1)
        {
            DebugStub.Print("CLOCK CALIBRATION NOT ATTEMPTED.\n");
            // hacked, should calibrate
            Processor.CyclesPerSecond = 687 * 1000 * 1000; // MPU runs @ 687Mhz in OPP1
            gpTimer1.SetTicksPerSecond(32768);
            return;
        }
    }
}
