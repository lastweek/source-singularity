///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ClockLogger.cs
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
using System.Threading;
using System.Diagnostics;

namespace Microsoft.Singularity.Hal
{
    [ CLSCompliant(false) ]
    internal sealed class ClockLogger
    {
        public struct Record
        {
            public int who;
            public ulong when;
            public ulong currentTime;
            public long upTime;
            public int  pitLastClock;
            public int  pitNow;
            public long cookie;
        };
        private static int currentRecord = 0;
        private static Record [] entries = null;
        private static int ignoreCount = 20000;

        static ClockLogger()
        {
            InitializeEntries();
#if LOG_CLOCK
            DebugStub.Print("Initializing ClockLogger.\n");
#endif // LOG_CLOCK
        }

        [System.Diagnostics.Conditional("LOG_CLOCK")]
        internal static void InitializeEntries()
        {
            entries = new Record[10000];
        }

        [System.Diagnostics.Conditional("LOG_CLOCK")]
        [NoHeapAllocation]
        internal static void AddEntry(int who, RtcPitState rps, TimerOmap3430 timer, long cookie)
        {
            if (ignoreCount != 0) {
                ignoreCount--;
                return;
            }

            if (currentRecord == entries.Length)
                return;

            entries[currentRecord].who = who;
            entries[currentRecord].cookie = cookie;
            entries[currentRecord].when = Processor.CycleCount;
//            int pitNow = timer.Timer2Read();
            int pitNow = 0;
            entries[currentRecord].currentTime =
                (ulong)rps.GetKernelTicks(pitNow);
            entries[currentRecord].upTime = rps.upTime;
            entries[currentRecord].pitLastClock = rps.pitLastClock;
            entries[currentRecord].pitNow = pitNow;

            currentRecord = currentRecord + 1;

            if (currentRecord == entries.Length) {
                bool iflag = Processor.DisableInterrupts();
                try {
                    DumpEntries();
                    DebugStub.Assert(false);
                }
                finally {
                    Processor.RestoreInterrupts(iflag);
                }
            }
        }

        [System.Diagnostics.Conditional("LOG_CLOCK")]
        [NoHeapAllocation]
        internal static void AddEntry(int who, RtcPitState rps, TimerOmap3430 timer)
        {
            AddEntry(who, rps, timer, 0);
        }

        [System.Diagnostics.Conditional("LOG_CLOCK")]
        [NoHeapAllocation]
        internal static void SetCookie(long cookie)
        {
            if (currentRecord < entries.Length)
                entries[currentRecord].cookie = cookie;
        }

        [NoHeapAllocation]
        static ulong ToMicros(ulong t, ulong t0, ulong tps)
        {
            return ((t - t0) * 10000000) / tps;
        }

        [System.Diagnostics.Conditional("LOG_CLOCK")]
        [NoHeapAllocation]
        static void DumpEntries()
        {
            DebugStub.Print("# Clock column 1 who\n");
            DebugStub.Print("# Clock column 2 time in cpu cycles\n");
            DebugStub.Print("# Clock column 3 time from clock\n");
            DebugStub.Print("# Clock column 4 pitLastClock\n");
            DebugStub.Print("# Clock column 5 pitNow\n");
            DebugStub.Print("# Clock column 6 upTime\n");
            DebugStub.Print("# Clock column 7 currentTime\n");
            DebugStub.Print("# Clock column 8 cookie\n");
            DebugStub.Print("# Clock column 9 record number\n");

            for (int i = 0; i != currentRecord; i++) {
                DebugStub.Print("Clock {0:d6} {1:d6} {2} {3} {4} {5} {6} {7}\n",
                                __arglist(
                                    ToMicros(entries[i].when,
                                             entries[0].when,
                                             Processor.CyclesPerSecond),
                                    ToMicros(entries[i].currentTime, 0, 10000000),
                                    entries[i].pitLastClock,
                                    entries[i].pitNow,
                                    entries[i].upTime,
                                    entries[i].currentTime,
                                    entries[i].cookie,
                                    i));
            }
        }
    }
}
