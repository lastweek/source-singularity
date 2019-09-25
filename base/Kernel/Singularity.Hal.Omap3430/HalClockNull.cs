///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: HalClockNull.cs
//
//  Note:
//
//  This file is an pretty bogus implementation of Interfaces/Hal/HalClock.csi
//

using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Hal
{
    public class HalClockNull : HalClock
    {
        long ticks;

        public HalClockNull()
        {
            ticks = 1;
        }

        public byte Initialize()
        {
            ticks = 1;
            return 254;
        }

        public void Finalize()
        {
        }

        [NoHeapAllocation]
        public override void ClearInterrupt()
        {
        }

        [NoHeapAllocation]
        public override long GetKernelTicks()
        {
            return ticks;
        }

        [NoHeapAllocation]
        public override void CpuResumeFromHaltEvent()
        {
            ticks++;
        }

        [NoHeapAllocation]
        public override long GetRtcTime()
        {
            return ticks;
        }

        public override void SetRtcTime(long rtcTicks)
        {
            ticks = rtcTicks;
        }
    }
}
