///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: HalClock.cs
//
//  Note:
//

using System;
using System.Collections;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

using Microsoft.Singularity;

namespace Microsoft.Singularity.Hal
{
    public abstract class HalClock
    {

        /// <summary>
        /// Notification that system has received and processed clock
        /// interrupt.
        /// </summary>
        [NoHeapAllocation]
        public abstract void ClearInterrupt();

        /// <summary>Get the time elapsed since booting.
        /// <returns>Ticks of 100ns of uptime. </returns>
        /// </summary>
        [NoHeapAllocation]
        public abstract long GetKernelTicks();

        /// <summary>
        /// Notification that processor is resuming from halted state.
        /// Provides clock to re-sync if it uses the CPU timestamp counter.
        /// </summary>
        [NoHeapAllocation]
        public abstract void CpuResumeFromHaltEvent();

        /// <summary>Get time from Real-Time Clock.</summary>
        /// <returns>The number of 100-nanosecond intervals that
        /// have elapsed since 12:00 A.M., January 1, 0001.
        /// </returns>
        [NoHeapAllocation]
        public abstract long GetRtcTime();

        /// <summary>Set time of Real-Time Clock.</summary>
        /// <param name="rtcTicks">The number of 100-nanosecond intervals
        /// that have elapsed since 12:00 A.M., January 1, 0001.
        /// </param>
        public abstract void SetRtcTime(long rtcTicks);
    }
}
