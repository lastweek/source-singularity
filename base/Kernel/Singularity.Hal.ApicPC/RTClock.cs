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
//    http://www.cebix.net/downloads/bebox/bq3285.pdf
//

//#define SAMPLE_PC

using Microsoft.Singularity.Io;

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity.Configuration;

namespace Microsoft.Singularity.Hal
{
    [DriverCategory]
    [Signature("/pnp/PNP0B00")]
    public sealed class RtcResources : DriverCategoryDeclaration
    {
        [IoPortRange(0, Default = 0x0070, Length = 0x02)]
        public IoPortRange port1;

        [IoIrqRange(1, Default = 0x08)]
        public IoIrqRange irq1;
    }

    /// <remarks>
    /// Class <c>RTClock</c> represents the system
    /// Real-Time Clock.  RTC chips in PCs are based on the
    /// Motorola MC146818A.  It provides timing resolution
    /// of 1 second, but can generate periodic interrupts
    /// more frequently.
    /// </remarks>
    [ CLSCompliant(false) ]
    public sealed class RTClockApic
    {
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

        private PnpConfig config;
        private IoPort    rtcadd;
        private IoPort    rtcdat;

        private Apic apic;
        private byte irq;
        private byte interrupt;
        internal volatile uint irqCount = 0;

        private SpinLock rtcSpinLock;  // Protects rtcBootTime and rtc update
        private long rtcBootTime;

        private byte firstStatus;

        // Constructor
        internal RTClockApic(PnpConfig config, Apic apic)
        {

            int  cpuId;
            Microsoft.Singularity.Hal.Platform p = Microsoft.Singularity.Hal.Platform.ThePlatform;
            cpuId = p.ApicId;

            DebugStub.Print("RTClock: create\n");

            // /pnp/08/03/01/PNP0B00 0003 cfg dis : ISA RTC Controller : AT RTC
            // IRQ mask=0100 type=47
            // I/O Port inf=01 min=0070 max=0070 aln=01 len=02 0070..0071

            this.config      = config;
            this.irq         = ((IoIrqRange)config.DynamicRanges[1]).Irq;
            this.apic        = apic;
            this.rtcSpinLock = new SpinLock(SpinLock.Types.RTClock);

            rtcadd = ((IoPortRange)config.DynamicRanges[0])
                .PortAtOffset(0, 1, Access.ReadWrite);
            rtcdat = ((IoPortRange)config.DynamicRanges[0])
                .PortAtOffset(1, 1, Access.ReadWrite);

            if (cpuId == 0) {
                this.interrupt = Initialize();
                DebugStub.Print("RTClock: interrupt {0:x2}\n",
                                __arglist(this.interrupt));
            }
        }

        [NoHeapAllocation]
        private byte ReadRtc(byte addr)
        {
            IoResult result;

            result = rtcadd.Write8NoThrow(addr);
            DebugStub.Assert(IoResult.Success == result);

            byte value;
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

        private byte Initialize()
        {
            if ((ReadRtc(DS1287_D) & DS1287_D_VRT) == 0) {
                DebugStub.Print("RTClock weak or defective power source.\n");
            }

            rtcBootTime = PullRtcTime();

            DebugStub.Print("RTClock::Start()\n");

            // Enable and clear interrupts
            // NB it may take 500ms for first interrupt to be generated.

            WriteRtc(DS1287_B, DS1287_B_UTI);
            WriteRtc(DS1287_A, DS1287_A_2HZ);
            WriteRtc(DS1287_A, DS1287_A_DIVON | DS1287_A_2HZ);
            WriteRtc(DS1287_B, DS1287_B_HF_24H | DS1287_B_DF_BCD | DS1287_B_PIE | DS1287_B_SQWE);

            // apic.SetIrqPriority(irq, IrqPriority.High);
            apic.EnableIrq(irq);

            // Here we wait for the first interrupt to be
            // raised, which might be upto 0.5 seconds.  This
            // wait is based on experience, ie not waiting with
            // some boxes (the infamous Ryan's TPM machine for
            // instance) leads to the clock interrupt never being
            // raised.

            while ((ReadRtc(DS1287_C) & DS1287_C_PF) != DS1287_C_PF) {
                // TODO: Break out after 1 second and
                // report an error.
            }
            firstStatus = DS1287_C_PF;

            byte ivValue = apic.IrqToInterrupt(irq);

            return ivValue;
        }

        private int Log2(uint value)
        {
            int l = 0;
            if ((value & 0xffff0000u) != 0) {
                l += 16; value >>= 16;
            }
            if ((value & 0x0000ff00u) != 0) {
                l += 8; value >>= 8;
            }
            if ((value & 0x000000f0u) != 0) {
                l += 4; value >>= 4;
            }
            if ((value & 0x0000000cu) != 0) {
                l += 2; value >>= 2;
            }
            if ((value & 0x0000000au) != 0) {
                l += 1; value >>= 1;
            }
            return l;
        }

        internal bool SetFrequency(uint frequency)
        {
            if (frequency > 8192 || frequency < 2) {
                return false;
            }

            if (Processor.SamplingEnabled()) {
                frequency = 8192;
            }

            int a = DS1287_A_DIVON;
            a |= (0xf - (Log2(frequency) - 1)) & 0xf;
            DebugStub.Assert((a & 0xf0) == DS1287_A_DIVON);

            WriteRtc(DS1287_A, (byte) a);
            WriteRtc(DS1287_B, DS1287_B_HF_24H | DS1287_B_DF_BCD | DS1287_B_PIE | DS1287_B_SQWE);

            return true;
        }

        public void ReleaseResources()
        {
            apic.DisableIrq(irq);
        }

        [NoHeapAllocation]
        public void ClearInterrupt()
        {
            byte status = ReadRtc(DS1287_C);
            status |= firstStatus;
            firstStatus = 0;

            const byte CMask = DS1287_C_INTF | DS1287_C_PF;

            DebugStub.Assert((status & CMask) == CMask);

            if ((status & DS1287_C_PF) != 0) {
                this.irqCount++;
            }
            apic.AckIrq(apic.InterruptToIrq(this.interrupt));
        }

        public byte Interrupt
        {
            [NoHeapAllocation]
            get { return this.interrupt; }
        }

        ///////////////////////////////////////////////////////////////////////

        [ System.Diagnostics.Conditional("SINGULARITY_MP") ]
        [NoHeapAllocation]
        private void AcquireLock()
        {
            rtcSpinLock.Acquire();
        }

        [ System.Diagnostics.Conditional("SINGULARITY_MP") ]
        [NoHeapAllocation]
        private void ReleaseLock()
        {
            rtcSpinLock.Release();
        }

        [NoHeapAllocation]
        public long GetBootTime()
        {
            bool en = Processor.DisableInterrupts();
            try {
                AcquireLock();
                long bootTime = rtcBootTime;
                ReleaseLock();
                return bootTime;
            }
            finally {
                Processor.RestoreInterrupts(en);
            }
        }

        public void SetRtcTime(long newRtcTime, long kernelTicks)
        {
            bool en = Processor.DisableInterrupts();
            try {
                AcquireLock();
                long currentRtcTime = rtcBootTime + kernelTicks;
                long delta  = newRtcTime - currentRtcTime;
                rtcBootTime = rtcBootTime + delta;
                PushRtcTime(newRtcTime);
                ReleaseLock();
            }
            finally {
                Processor.RestoreInterrupts(en);
            }
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

        private long PullRtcTime()
        {
            for (uint iters = 0; iters < 1000000; iters++) {
                bool iflag = Processor.DisableInterrupts();

                try {
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
                    if ((ReadRtc(DS1287_A) & DS1287_A_UIP) != 0) {
                        continue;
                    }

                    DebugStub.Print("PullRtcTime: " +
                                    "{0:d4}-{1:d2}-{2:d} {3:2}:{4:d2}:{5:d2}" +
                                    "\n",
                                    __arglist(100*century+year, month, day,
                                              hour, minute, second));

                    DateTime d = new DateTime(century * 100 + year, month, day,
                                              hour, minute, second);
                    return d.Ticks;
                }
                catch (ArgumentOutOfRangeException e) {
                    DebugStub.Print("PullRtcTime failed: {0}\n",
                                    __arglist(e));
                }
                finally {
                    Processor.RestoreInterrupts(iflag);
                }
            }
            return (new DateTime(2005, 1, 1, 0, 0, 0)).Ticks;
        }

        private void PushRtcTime(long dtTicks)
        {
            DateTime dt = new DateTime(dtTicks);

            bool iflag = Processor.DisableInterrupts();
            try {
                byte saved = ReadRtc(DS1287_B);

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
                WriteRtc(DS1287_YEAR,         HexToBcd(dt.Year - century*100));
                WriteRtc(DS1287_USERDATA,     HexToBcd(century));
                // Clear UTI bit to enable transfers again
                WriteRtc(DS1287_B, saved);
                DebugStub.Print("PushRtcTime {3:2}:{4:d2}:{5:d2} {0}/{1}-{2:d4}\n",
                                __arglist(dt.Month, dt.Day,
                                          100*century + dt.Year, dt.Hour,
                                          dt.Minute, dt.Second));
            }
            finally {
                Processor.RestoreInterrupts(iflag);
            }
        }
    }
}
