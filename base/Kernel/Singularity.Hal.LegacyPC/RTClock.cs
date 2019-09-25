///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   RTClock.cs
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
using System.Threading;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Configuration;

namespace Microsoft.Singularity.Hal
{
    // declare resources for the kernel manifest
    [DriverCategory]
    [Signature("/pnp/PNP0B00")]
    public sealed class RtcResourcesLegacyPC : DriverCategoryDeclaration
    {
        [IoPortRange(0, Default = 0x70, Length = 0x02)]
        public IoPortRange port1;

        [IoIrqRange(1, Default = 0x08)]
        public IoIrqRange irq1;
    }

    /// <remarks>
    /// Class <c>RTClock</c> represents the system
    /// Real-Time Clock.  RTC chips in PCs are based on the
    /// Motorola MC1461818A.  It provides timing resolution of 1
    /// second, but can generate periodic interrupts more
    /// frequently.  By combining information from
    /// <c>Timer8254</c> programmable timer time can be read
    /// with a resolution of 0.838 microseconds.
    /// </remarks>
    [ CLSCompliant(false) ]
    internal sealed class RTClockLegacyPC : HalClock
    {
        private PnpConfig   config;
        private byte        irq;
        private Pic         pic;

        // Real time clock registers - for calibration   
        private IoPort rtcadd;
        private IoPort rtcdat;

        // Data registers
        private const byte DS1287_SECONDS       = 0x00;
        private const byte DS1287_SECONDS_ALARM = 0x01;
        private const byte DS1287_MINUTES       = 0x02;
        private const byte DS1287_MINUTES_ALARM = 0x03;
        private const byte DS1287_HOURS         = 0x04;
        private const byte DS1287_HOURS_ALARM   = 0x05;
        private const byte DS1287_DAY_OF_WEEK   = 0x06; // 1 is Sunday
        private const byte DS1287_DAY_OF_MONTH  = 0x07;
        private const byte DS1287_MONTH         = 0x08;
        private const byte DS1287_YEAR          = 0x09;
        private const byte DS1287_USERDATA      = 0x32; // Randomly chosen user reg.
        // Control registers and masks
        private const byte DS1287_A             = 0x0a;
        private const byte DS1287_A_UIP         = 0x80; // Update Cycle Status
        private const byte DS1287_A_DIVON       = 0x20; // Osc and Freq Div on
        private const byte DS1287_A_8KHZ        = 0x03;
        private const byte DS1287_A_4KHZ        = 0x04;
        private const byte DS1287_A_2KHZ        = 0x05;
        private const byte DS1287_A_1KHZ        = 0x06;
        private const byte DS1287_A_64HZ        = 0x0a;
        private const byte DS1287_A_2HZ         = 0x0f;
        private const byte DS1287_B             = 0x0b;
        private const byte DS1287_B_UTI         = 0x80; // Update Transfer Inhibit
        private const byte DS1287_B_PIE         = 0x40; // Periodic Interrupt Enable
        private const byte DS1287_B_24H         = 0x20; // Alarm Interrupt Enable
        private const byte DS1287_B_UIE         = 0x10; // Update Cycle Inter. Enable
        private const byte DS1287_B_SQWE        = 0x08; // Square-Wave Enable
        private const byte DS1287_B_DF          = 0x04; // Data Format
        private const byte DS1287_B_DF_BINARY   = 0x04; //   Binary
        private const byte DS1287_B_DF_BCD      = 0x00; //   Binary Coded Decimal (BCD)
        private const byte DS1287_B_HF          = 0x02; // Hour Format
        private const byte DS1287_B_HF_24H      = 0x02; //   24-hour format
        private const byte DS1287_B_HF_12H      = 0x00; //   12-hour format
        private const byte DS1287_B_DSE         = 0x01; // Daylight Saving Enable
        private const byte DS1287_C             = 0x0c;
        private const byte DS1287_C_UF          = 0x10; // Update Event Flag
        private const byte DS1287_C_AF          = 0x20; // Alarm Event Flag
        private const byte DS1287_C_PF          = 0x40; // Periodic Event Flag
        private const byte DS1287_C_INTF        = 0x80; // Interrupt Request Flag
        private const byte DS1287_D             = 0x0d;
        private const byte DS1287_D_VRT         = 0x80; // Valid RAM and Time

        // Rate if rtc used for generating profiling interrupts
        const byte DS1287_A_SAMPLING_HZ = DS1287_A_1KHZ;

        const int InterruptGapTicks    = 156250;   // units of 100ns

        const uint maxAttempts = 1000000;

        private RtcPitState rps   = null;
        private Timer8254LegacyPC   timer = null;
        private long        rtcBootTime;
        private volatile uint irqCount = 0;

        // Variables for fast GetKernelTicks implementation that uses
        // TSC when it is deemed safe.
        bool  noisyTimer;               // Running on VPC? Disable optimization
        long  tscSnapshot;              // TSC value at sync point
        long  ticksSnapshot;            // Kernel ticks at sync point
        long  lastKernelTicks;          // Last kernel ticks reported
        bool  tscSnapshotValid = false;
        bool  initedFastTime   = false;
        int   tickScale;
        const int tickRoll = 24;

        // Constructor
        internal RTClockLegacyPC(PnpConfig config, Pic pic, Timer8254LegacyPC timer)
        {
            DebugStub.Print("RTClock: create\n");

            // /pnp/08/03/01/PNP0B00 0003 cfg dis : ISA RTC Controller : AT RTC
            // IRQ mask=0100 type=47
            // I/O Port inf=01 min=0070 max=0070 aln=01 len=02 0070..0071

            this.config = config;
            this.pic    = pic;
            this.irq    = ((IoIrqRange)config.DynamicRanges[1]).Irq;
            this.timer  = timer;

            rtcadd = ((IoPortRange)config.DynamicRanges[0])
                .PortAtOffset(0, 1, Access.ReadWrite);
            rtcdat = ((IoPortRange)config.DynamicRanges[0])
                .PortAtOffset(1, 1, Access.ReadWrite);

        }

        [NoHeapAllocation]
        private byte ReadRtc(byte addr)
        {
            IoResult result;
            byte value;

            result = rtcadd.Write8NoThrow(addr);
            DebugStub.Assert(IoResult.Success == result);

            result = rtcdat.Read8NoThrow(out value);
            DebugStub.Assert(IoResult.Success == result);

            return value;
        }

        [NoHeapAllocation]
        private void WriteRtc(byte addr, byte val)
        {
            IoResult result;

            result = rtcadd.Write8NoThrow(addr);
            DebugStub.Assert(IoResult.Success == result);

            result = rtcdat.Write8NoThrow(val);
            DebugStub.Assert(IoResult.Success == result);
        }

        [NoHeapAllocation]
        public override void ClearInterrupt()
        {
#if RTC_NO_GO
            DebugStub.Print("Unwanted RTC interrupt! (b = {0})\n",
                            __arglist(ReadRtc(DS1287_B)));
            return;
#endif // RTC_NO_GO

            byte status = ReadRtc(DS1287_C);
            if ((status & 0x40) != 0x40) {
                // We may get Update-Ended interrupts even though we've
                // not requested them.
                pic.AckIrq(irq);
                return;
            }

            ClockLogger.AddEntry(4, rps, timer);
            rps.pitLastClock  = timer.Timer2Read();
            rps.upTime       += InterruptGapTicks;

            ClockLogger.AddEntry(5, rps, timer);
            irqCount++;

            if (timer.InterruptPending == false) {
                // This is to keep time progressing if the user has
                // not set an interrupt
                timer.SetKeepAliveInterrupt();
            }
            pic.AckIrq(irq);

            // Invalidate TSC snapshot to force clock synchronization
            this.tscSnapshotValid = false;
        }

        internal byte Initialize()
        {
            DebugStub.Print("RTClock: initialize\n");

            rps = timer.rps;

            // Turn oscillator on, but disable and clear interrupts
            if (Processor.SamplingEnabled()) {
                WriteRtc(DS1287_A, DS1287_A_DIVON | DS1287_A_SAMPLING_HZ);
            }
            else {
                WriteRtc(DS1287_A, DS1287_A_DIVON | DS1287_A_64HZ);
            }
            WriteRtc(DS1287_B, DS1287_B_24H | DS1287_B_DF_BCD);
            ReadRtc(DS1287_C);  // Clear any update bits

            if ((ReadRtc(DS1287_D) & DS1287_D_VRT) == 0) {
                DebugStub.Print("RTClock weak or defective power source.\n");
            }

            rtcBootTime = PullRtcTime().Ticks;

            // Enable and clear interrupts
            // NB it may take 500ms for first interrupt to be generated.
            pic.EnableIrq(irq);
            return pic.IrqToInterrupt(irq);
        }

        internal void Start()
        {
            DebugStub.Print("RTClock::Start()\n");
#if RTC_NO_GO
            WriteRtc(DS1287_B, DS1287_B_24H | DS1287_B_UTI);
#endif
            // XXX A #else does not work here with sgc (!)
#if !RTC_NO_GO
            if (Processor.SamplingEnabled()) {
                WriteRtc(DS1287_A, DS1287_A_DIVON | DS1287_A_SAMPLING_HZ);
            }
            else {
                WriteRtc(DS1287_A, DS1287_A_DIVON | DS1287_A_64HZ);
            }
            WriteRtc(DS1287_B, DS1287_B_24H | DS1287_B_PIE);
            ReadRtc(DS1287_C);
#endif
        }

        internal void ReleaseResources()
        {
            pic.DisableIrq(irq);
        }

        [NoHeapAllocation]
        bool InitializeFastTime()
        {
            const ulong KernelTicksPerSecond = 10000000;
            ulong cps = Processor.CyclesPerSecond;
            if (cps >= KernelTicksPerSecond) {
                this.tscSnapshot   = 0;
                this.ticksSnapshot = 0;
                this.tickScale =
                    (int)((1 << tickRoll) * KernelTicksPerSecond / cps);
#if VERBOSE
                DebugStub.Print(
                    "tick scale = {0} (actual {1:d}, fast {2:d})",
                    __arglist(this.tickScale,
                              cps,
                              ((1 << tickRoll) * KernelTicksPerSecond /
                               (ulong)this.tickScale))
                    );
#endif // VERBOSE
                return true;
            }
            return false;
        }

        internal void SetNoisyTimer(bool noisy)
        {
            this.noisyTimer = noisy;
        }

        [NoHeapAllocation]
        private long GetKernelTicksFromHW()
        {
            bool iflag = Processor.DisableInterrupts();
            try {
                ClockLogger.AddEntry(100, rps, timer);
                long r = rps.GetKernelTicks(timer.Timer2Read());
                return r;
            }
            finally {
                Processor.RestoreInterrupts(iflag);
            }
        }

        [NoHeapAllocation]
        private long GetKernelTicksFromTsc()
        {
            long now = unchecked((long)Processor.CycleCount);
            long tscDelta = now - this.tscSnapshot;
            long tickDelta = (tscDelta * tickScale) >> tickRoll;
            DebugStub.Assert(tickDelta >= 0);
            return ticksSnapshot + tickDelta;
        }

        [NoHeapAllocation]
        private long InternalGetKernelTicks()
        {
            if (!initedFastTime) {
                initedFastTime = InitializeFastTime();
            }

            if (this.noisyTimer || !initedFastTime) {
                // Looks like Virtual PC or one not suited to
                // fast time calculation.  Always pull time from
                // the hardware as the TSC is not virtualized
                // and is not to be trusted.
                return GetKernelTicksFromHW();
            }
            else {
                if (!tscSnapshotValid) {
                    // When waking up from a processor halt
                    // event or from a clock interrupt, sync
                    // with the fixed h/w's concept of time.
                    this.ticksSnapshot = GetKernelTicksFromHW();
                    this.tscSnapshot   = unchecked((long)Processor.CycleCount);
                    this.tscSnapshotValid = true;
                    return ticksSnapshot;
                }
                else {
                    return GetKernelTicksFromTsc();
                }
            }
        }

        [NoHeapAllocation]
        public override long GetKernelTicks()
        {
#if DEBUG_TIMER
            {
                long cpuT = GetKernelTicksFromTsc();
                long hwT = GetKernelTicksFromHW();

                if (cpuT - hwT > 5000 || hwT - cpuT < -5000) {
                    DebugStub.Print("Delta = {0:d} (hw {1:d} cpu {2:d})\n",
                                    __arglist(cpuT - hwT, hwT, cpuT));
                }
            }
#endif // DEBUG_TIMER

            // We use the TSC to provide fast kernel ticks as
            // far as possible, and periodically sync against an
            // off-chip clock.  Because there are different time
            // sources and we don't ever want to report time
            // going backwards, we need to check that time would
            // reported to have advanced or remained the same,
            // and that the clock has not wrapped.
            long kernelTicks = InternalGetKernelTicks();

            if (kernelTicks >= lastKernelTicks) {
                lastKernelTicks = kernelTicks;
                return kernelTicks;
            }
            else if (kernelTicks < 0 && lastKernelTicks > 0) {
                    // clock wrap
                return kernelTicks;
            }
#if DEBUG_TIMER
            // Skew from switching between tsc and underlying clock
            DebugStub.Print("Backwards delta = {0} (HW {1} TSC {2})\n",
                            __arglist(kernelTicks - lastKernelTicks,
                                      GetKernelTicksFromHW(),
                                      GetKernelTicksFromTsc())
                            );
#endif // DEBUG_TIMER
            return lastKernelTicks;
        }

        [NoHeapAllocation]
        public override void CpuResumeFromHaltEvent()
        {
            tscSnapshotValid = false;
        }

        [NoHeapAllocation]
        public override long GetRtcTime()
        {
            return rtcBootTime + GetKernelTicks();
        }

        public override void SetRtcTime(long rtcTime)
        {
            long delta = rtcTime - GetRtcTime();
            rtcBootTime = rtcBootTime + delta;
            PushRtcTime(new DateTime(rtcTime));
        }

        [NoHeapAllocation]
        internal static byte BcdToHex(byte bcd)
        {
            return (byte) (10 * (bcd >> 4) + (bcd & 0x0f));
        }

        [NoHeapAllocation]
        internal static byte HexToBcd(int hex)
        {
            int h = hex / 10;
            return (byte) ((h << 4) | (hex - h * 10));
        }

        internal bool UpdateInProgress()
        {
            return (ReadRtc(DS1287_A) & DS1287_A_UIP) == DS1287_A_UIP;
        }

        private DateTime PullRtcTime()
        {
            for (uint iters = 0; iters < maxAttempts; iters++) {
                bool iflag = Processor.DisableInterrupts();

                try {
                    ReadRtc(DS1287_C); // Clear update flag if set

                    if ((ReadRtc(DS1287_A) & DS1287_A_UIP) != 0) {
                        // Update is in progress, try again
                        continue;
                    }

                    // There is no update
                    // pending.  The specs suggest at least
                    // ~244us to read values (T_BUC)...
                    byte second  = BcdToHex(ReadRtc(DS1287_SECONDS));
                    byte minute  = BcdToHex(ReadRtc(DS1287_MINUTES));
                    byte hour    = BcdToHex(ReadRtc(DS1287_HOURS));
                    byte day     = BcdToHex(ReadRtc(DS1287_DAY_OF_MONTH));
                    byte month   = BcdToHex(ReadRtc(DS1287_MONTH));
                    byte year    = BcdToHex(ReadRtc(DS1287_YEAR));
                    byte century = BcdToHex(ReadRtc(DS1287_USERDATA));

                    // ...but we don't
                    // trust the specs, particularly as we may
                    // be running on emulated hardware.  Retry
                    // if an update is pending or appears to
                    // have completed whilst reading the time.
                    if ((ReadRtc(DS1287_A) & DS1287_A_UIP) != 0 ||
                        (ReadRtc(DS1287_C) & DS1287_C_UF)  != 0) {
                        continue;
                    }

                    DebugStub.Print("PullRtcTime: " +
                                    "{0:d4}-{1:d2}-{2:d} {3:2}:{4:d2}:{5:d2}" +
                                    "\n",
                                    __arglist(100*century+year, month, day,
                                              hour, minute, second));
                    // There appears to be an issue with the timer that
                    // doesn't clear/zero out the most significant digit
                    // when a value can be represented by a single digit.
                    // Attempt to recover from this scenario.
                    second = (second < 60) ? second : (byte) (second % 10);
                    minute = (minute < 60) ? minute : (byte) (minute % 10);
                    hour = (hour < 24) ? hour : (byte) (hour % 10);
                    day = (day <= 31) ? day : (byte) (day % 10);
                    month = (month <= 12) ? month : (byte) (month % 10);
                    year = (year < 100) ? year : (byte) (year % 100);

                    return new DateTime(century * 100 + year,
                                        month, day, hour, minute,
                                        second);
                }
                catch (ArgumentOutOfRangeException e) {
                    DebugStub.Print("PullRtcTime failed: {0} "+
                                    "(1:x}:{2:x}:{3:x} {4:x}/{5:x} "+
                                    "100*{6:x}+{7:x})\n",
                                    __arglist(e,
                                              ReadRtc(DS1287_HOURS),
                                              ReadRtc(DS1287_MINUTES),
                                              ReadRtc(DS1287_SECONDS),
                                              ReadRtc(DS1287_MONTH),
                                              ReadRtc(DS1287_DAY_OF_MONTH),
                                              ReadRtc(DS1287_USERDATA),
                                              ReadRtc(DS1287_YEAR)));
                    if (iters > (maxAttempts >> 1)) {
                        DebugStub.Break();
                    }
                }
                finally {
                    Processor.RestoreInterrupts(iflag);
                }
            }
            return new DateTime(2005, 1, 1, 0, 0, 0);
        }

        private void PushRtcTime(DateTime dt)
        {
            bool iflag = Processor.DisableInterrupts();
            byte saved = ReadRtc(DS1287_B);

            try {
                // Set UTI bit to stop transfers between RTC
                // bytes and user buffer.
                WriteRtc(DS1287_B, (byte)(saved | DS1287_B_UTI));
                // Write new values
                WriteRtc(DS1287_SECONDS,      HexToBcd(dt.Second));
                WriteRtc(DS1287_MINUTES,      HexToBcd(dt.Minute));
                WriteRtc(DS1287_HOURS,        HexToBcd(dt.Hour));
                WriteRtc(DS1287_DAY_OF_MONTH, HexToBcd(dt.Day));
                WriteRtc(DS1287_MONTH,        HexToBcd(dt.Month));

                int century = dt.Year / 100;
                WriteRtc(9, HexToBcd(dt.Year - century * 100));
                WriteRtc(DS1287_YEAR,         HexToBcd(dt.Year - century*100));
                WriteRtc(DS1287_USERDATA,     HexToBcd(century));
                // Clear UTI bit to enable transfers again
                DebugStub.Print("PushRtcTime {3:2}:{4:d2}:{5:d2} {0}/{1}-{2:d4}\n",
                                __arglist(dt.Month, dt.Day,
                                          100*century + dt.Year, dt.Hour,
                                          dt.Minute, dt.Second));
            }
            finally {
                WriteRtc(DS1287_B, saved);
                Processor.RestoreInterrupts(iflag);
            }
        }
    }
}
