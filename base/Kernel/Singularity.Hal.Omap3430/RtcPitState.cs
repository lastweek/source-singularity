///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   RtcPitState.cs
//
//  Useful reference URLs:
//    http://developer.intel.com/design/archives/periphrl/index.htm
//    http://developer.intel.com/design/archives/periphrl/docs/7203.htm
//    http://developer.intel.com/design/archives/periphrl/docs/23124406.htm
//
// The basic ideas for this driver come from the MMOSA code,
// though the implementation differs.  This is partly because
// the code needs to run on Virtual PC and it isn't able to do
// a very accurate emulation of the i8254.
//
// There are two source available for timing - the Real-Time
// Clock (RTC) and the programmable interval timer (PIT).  The
// standard PC RTC is based on derivatives of the Motorola
// MC146818A.  It's able to provide the time with a resolution
// of 1 second and also has a programmable periodic interrupt.
//
// The programmable interrupt timer is based on the i8254.  It
// can be programmed in a variety of modes - we use it to
// generate an interrupt at a configurable time in the future
// and then reprogram it each interrupt.  The maximum interrupt
// period is 65535 ticks of a 1.193MHz clock.
//
// We use both of the RTC and the programmable interrupt timer to
// maintain our estimate of the current time.  The RTC provides granularity
// to with 1/64 seconds and the time is used to get an estimate to within
// 1/1.193 * 10e-6 seconds within each RTC interval.
//
// The key variables are:
//
// upTime -   the time the system has been up.  This variable gets
//            updated during the periodic RTC interrupt handling
//            (delta = 1/64Hz).
//
// pitLast -  the last value programmed into the PIT.  The PIT counts down
//            and generates an interrupt at (or shortly after) the instant
//            the current PIT value reaches zero.
//
// pitAccum - the accumulated time measured by the PIT since upTime
//            was updated.
//
// The current kernel time is always:
//      upTime + pitAccum + (pitLast - pitCurrent)
//
// The PIT is always programmed to run, either by the consumer of the timer
// interface or by the timer itself.
//
//    Timer::SetNextInterrupt(t)
//      pitAccum += (pitLast - pitCurrent)
//      // program PIT (not shown)
//      pitLast = t
//
//    Timer::Interrupt()
//      pitAccum += pitLast;
//      // But PIT time may accumulate between interrupt dispatch and crossing
//      // Zero so.
//      if (pitCurrent != 0)
//           pitAccum += (MaxPitValue - pitCurrent)
//      // Inform user of interrupt
//      if (userNotScheduledInterrupt)
//           SetNextInterrupt(MaxInterruptInterval)
//
//    RTC::Interrupt()
//      pitLast = pitNow
//      pitAccum = 0
//      upTime += RTCInterruptPeriod
//
// All of these methods are atomic interrupt-wise.
//
// Note: if we want to test the accuracy of the timer over a
// period we can set RTC::Interrupt to just return without
// touching any variables.  All of the time accumulated will end
// up in pitAccum.
//
// Conditionals
//
// TIMER_NO_GO  - disables timer and scheduling of timer interrupts.
//
// RTC_NO_GO    - disable RTC.
//
// DEBUG_TIMER  - enable timer debug messages and boot-time diagnostics.
//
// DEBUG_CLOCK  - enable clock debug messages
//
// LOG_CLOCK    - log adjustments to clock time and dump out later.
//
// LOG_SNI      - log calls to SetNextInterrupt to see what's being thrown in.
//
// Tip: When this code does not behave useful things to check
// are the interrupt rate and the rate of calls to
// SetNextInterrupt.
//

// #define VERBOSE

using Microsoft.Singularity.Io;

using System;
using System.Runtime.CompilerServices;
using System.Diagnostics;
using System.Threading;

namespace Microsoft.Singularity.Hal
{
    // Shared time state between RTClock and Programmable Timer
    [ CLSCompliant(false) ]
    internal sealed class RtcPitState
    {
        /// <remarks>
        /// System up time as measured by the <see>RTClock</see>.  This value
        /// is only updated by the RTClock.
        /// </remarks>
        internal long upTime = 0;

        internal volatile int pitLastClock;

        /// <remarks>
        /// Last time returned by GetKernelTicks.  Used to check for time
        /// going backwards.  This can occur in PIT value updates in the
        /// scaling between PIT timebase and kernel time base.
        /// </remarks>
        internal long lastKernelTicks = 0;

        internal RtcPitState()
        {
            this.pitLastClock = 0xffff;
            this.upTime       = 0;
        }

        [NoHeapAllocation]
        internal static int ComputePitOffset(int pitPrev, int pitNow)
        {
            if (pitPrev >= pitNow) {
                return pitPrev - pitNow;
            }
            return pitPrev + 0xffff - pitNow;
        }

        [NoHeapAllocation]
        internal long GetKernelTicks(int pitNow)
        {
            int  pitOffset = ComputePitOffset(this.pitLastClock, pitNow);
            long delta = 0; // Timer8254LegacyPC.PitTicksToTimeSpanTicks(pitOffset);
            long r = this.upTime + delta;

            if (r < this.lastKernelTicks) {
                // This should only be by a few ticks.
                // Something to look for if you are ever
                // working on this code.
                r = this.lastKernelTicks;
            }
            else {
                this.lastKernelTicks = r;
            }
            return r;
        }
    }
}
