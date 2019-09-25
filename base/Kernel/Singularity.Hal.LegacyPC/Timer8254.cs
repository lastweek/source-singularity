///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
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

using Microsoft.Singularity.Configuration;

namespace Microsoft.Singularity.Hal
{
    // declare resources for the kernel manifest
    [DriverCategory]
    [Signature("/pnp/PNP0100")]
    public sealed class TimerResourcesLegacyPC : DriverCategoryDeclaration
    {
        [IoPortRange(0, Default = 0x40, Length = 0x04)]
        public IoPortRange port1;

        [IoIrqRange(1, Default = 0x00, Length = 0x01)]
        public IoIrqRange irq1;

        [IoFixedPortRange(Base = 0x0061, Length = 0x01)]
        public IoPortRange port2;
    }

    //
    // Note on the i8254 timer:
    //
    // The clock is driven by a 14.318 MHz clock through a divide-by-12
    // counter.
    // This gives a clock frequency of 1.193 MHz.
    // Each tick is therefore 0.838 microseconds long.
    // Thus a 16 bit timer gives us a maximum delay of 0.05 seconds.
    // 
    [CLSCompliant(false)]
    public sealed class Timer8254LegacyPC : HalTimer
    {
        // Registers
        const byte  i8254_C0     = 0x00;    // counter 0       
        const byte  i8254_C1     = 0x01;    // counter 1       
        const byte  i8254_C2     = 0x02;    // counter 2       
        const byte  i8254_CW     = 0x03;    // control word      

        // The control word to the 8254 is composed of four fields:
        // bits 6-7: select the counter
        // bits 4-5: select read/write
        // bits 1-3: mode to use
        // bit  0  : BCD mode

        // bits 6-7 select the counter.
        const byte i8254_CW_SEL0      = 0x00;  // select counter 0         
        const byte i8254_CW_SEL1      = 0x40;  // select counter 1         
        const byte i8254_CW_SEL2      = 0x80;  // select counter 2         
        const byte i8254_CW_RBC       = 0xc0;  // read-back command        

        // bits 4-5 select transaction type.
        const byte i8254_CW_CLC       = 0x00;  // counter latch comm.      
        const byte i8254_CW_LSB       = 0x10;  // r/w lsb only             
        const byte i8254_CW_MSB       = 0x20;  // r/w msb only             
        const byte i8254_CW_BOTH      = 0x30;  // r/w lsb, then msb        

        // bits 1-3 select the mode. bit 3 is sometimes a don't care.
        const byte i8254_CW_MODE0     = 0x00;  // int. on term. count      
        const byte i8254_CW_MODE1     = 0x02;  // h/w retrig. one-shot     
        const byte i8254_CW_MODE2     = 0x04;  // rate generator           
        const byte i8254_CW_MODE3     = 0x06;  // square wave mode         
        const byte i8254_CW_MODE4     = 0x08;  // s/w trig. strobe         
        const byte i8254_CW_MODE5     = 0x0a;  // h/w trig. strobe         

        // bit 0 sets BCD mode, if you really must.
        const byte i8254_CW_BCD       = 0x01;  // set BCD operation        

        // read-back commands use bits 4 and 5 to return status these
        // are the wrong way round since the bits are inverted (RTFDS).
        // 
        const byte i8254_RB_NOSTATUS  = 0xd0;  // Don't get latched count   
        const byte i8254_RB_NOCOUNT   = 0xe0;  // Don't get status         
        const byte i8254_RB_ALL       = 0xc0;  // Get status and count     

        // read-back commands use bits 3-1 to select counter   
        const byte i8254_RB_SEL0      = 0x02;  // counter 0                
        const byte i8254_RB_SEL1      = 0x04;  // counter 1                
        const byte i8254_RB_SEL2      = 0x08;  // counter 2                

        // status from read-back is returned in bits 6-7   
        const byte i8254_RB_OUT       = 0x80;  // out pin value            
        const byte i8254_RB_NULL      = 0x40;  // 1 = count null           

        private PnpConfig config;
        private Pic       pic;
        private byte      irq;

        // IOPorts.
        private IoPort C0Port;
        private IoPort C2Port;
        private IoPort CWPort;

        internal static readonly int PitInterruptThreshold = 0xffff;
        internal static readonly int PitMaxWrite           = 0xffff;

        // Timer State.
        private volatile bool interruptPending = false;

        internal volatile uint irqCount = 0;
        internal RtcPitState rps;

        internal void SetTicksPerSecond(int count)
        {
#if DYNAMIC_TICKS
            ticksPerSecond = count;
            unchecked {
                Tracing.Log(Tracing.Audit, "i8254 Frequency {0} Hz.",
                            (UIntPtr)(uint)ticksPerSecond);
            }
#endif // DYNAMIC_TICKS
        }

        // Constructor
        internal Timer8254LegacyPC(PnpConfig config, Pic pic)
        {
#if VERBOSE
            Tracing.Log(Tracing.Debug, "Timer8254: create");
#endif

            // /pnp/08/02/01/PNP0100 0003 cfg dis : ISA 8254 Timer : AT Timer
            // IRQ mask=0001 type=47
            // I/O Port inf=01 min=0040 max=0040 aln=01 len=04 0040..0043
            this.config = config;
            this.pic    = pic;
            this.irq    = ((IoIrqRange)config.DynamicRanges[1]).Irq;
            IoPortRange ioPorts = (IoPortRange) config.DynamicRanges[0];
            C0Port = ioPorts.PortAtOffset(i8254_C0, 1, Access.ReadWrite);
            C2Port = ioPorts.PortAtOffset(i8254_C2, 1, Access.ReadWrite);
            CWPort = ioPorts.PortAtOffset(i8254_CW, 1, Access.ReadWrite);

            // Enable Timer2
            // Lower 2 bits of port 61 are described in:
            // The Indispensable PC Hardware Book (3rd Edition) p.724
            ioPorts = (IoPortRange) config.FixedRanges[0];
            IoPort p = ioPorts.PortAtOffset(0, 1, Access.ReadWrite);

            //
            // Also clear the NMI RAM parity error to enable the PCI card
            // to generate NMI if the button is depressed
            //

            p.Write8((byte) ((p.Read8() & 0xf8) | 0x01));
        }

        public byte Initialize()
        {
#if VERBOSE
            Tracing.Log(Tracing.Debug, "Timer.Initialize()");
#endif

            rps = new RtcPitState();
            Stop();
            DoPitPerformanceTests();

            pic.EnableIrq(irq);
            return pic.IrqToInterrupt(irq);
        }

        public void ReleaseResources()
        {
            pic.DisableIrq(irq);
            Stop();
        }

        internal void Start()
        {
#if !TIMER_NO_GO
            bool iflag = Processor.DisableInterrupts();
            try {
                PitWrite(0xffff);
                Timer2Start();
                SetKeepAliveInterrupt();
            }
            finally {
                Processor.RestoreInterrupts(iflag);
            }
#endif // TIMER_NO_GO
        }

        internal void Stop()
        {
            // Half-program counter to stop counter running.  Trick copied
            // from MMOSA i386 timer code
            CWPort.Write8(i8254_CW_MODE0 | i8254_CW_BOTH | i8254_CW_SEL0);
            C0Port.Write8((byte)(0));    // LSB
            // C0Port.Write8((byte)(0));  MSB DON'T!
        }

        internal void Timer2Start()
        {
            CWPort.Write8(i8254_CW_MODE2 | i8254_CW_BOTH | i8254_CW_SEL2);
            C2Port.Write8((byte)0xff);
            C2Port.Write8((byte)0xff);
        }

        [NoHeapAllocation]
        internal static int TimeSpanTicksToPitTicks(int ts)
        {
            // We should calculate scaling
            // factors based on ticksPerSecond.

            // Ticks = ts * 1193182 / 10000000
            //       = ts * (0x1e/0x100 + 0x8ba/0x100000)
            DebugStub.Assert(ts < 960000); // Limit for 0x8ba factor
            return ((ts * 0x1e) >> 8) + ((ts * 0x8ba) >> 20);
        }

        [NoHeapAllocation]
        internal static int PitTicksToTimeSpanTicks(int pit)
        {
            // We should calculate scaling
            // factors based on ticksPerSecond.

            // Ticks = pit * 10000000 / 1193182
            //       = pit * (0x86 / 0x10) + (0x186 / 0x10000)
            DebugStub.Assert(pit < 5500000); // Limit for 0x186 factor
            return ((pit * 0x86) >> 4) + ((pit * 0x186) >> 16);
        }

        private readonly TimeSpan maxInterruptInterval = new TimeSpan(500000);     // 50ms
        private readonly TimeSpan minInterruptInterval = new TimeSpan(1000);       // 1ms
        private readonly TimeSpan interruptGranularity = new TimeSpan(17);         // 1.7us

        /// <value>
        /// Maximum value accepted by SetNextInterrupt (in units of 100ns).
        /// </value>
        public override TimeSpan MaxInterruptInterval
        {
            [NoHeapAllocation]
            get { return maxInterruptInterval; }
        }

        /// <value>
        /// Minimum value accepted by SetNextInterrupt (in units of 100ns).
        /// </value>
        public override TimeSpan MinInterruptInterval
        {
            [NoHeapAllocation]
            get { return minInterruptInterval; }
        }

        [NoHeapAllocation]
        public override void SetNextInterrupt(TimeSpan delta)
        {
            DebugStub.Assert(Processor.InterruptsDisabled());
            DebugStub.Assert(delta >= minInterruptInterval);
            DebugStub.Assert(delta <= maxInterruptInterval);

#if TIMER_NO_GO
            return;
#endif
            ClockLogger.AddEntry(2, rps, this, delta.Ticks);

            PitWrite(TimeSpanTicksToPitTicks((int)delta.Ticks));
            this.interruptPending = true;

            ClockLogger.AddEntry(3, rps, this, delta.Ticks);
        }

        /// <remarks> Set timer interrupt to start or keep timer running.
        /// The user is expected to call SetNextInterrupt regularly during
        /// normal operation.  This method is invoked at start-up and if
        /// we find the timer interrupt is not programmed during the clock
        /// interrupt.
        /// </remarks>
        [NoHeapAllocation]
        internal void SetKeepAliveInterrupt()
        {
            ClockLogger.AddEntry(0, rps, this);
            PitWrite(PitMaxWrite);
            ClockLogger.AddEntry(1, rps, this);
            this.interruptPending = true;
        }

        internal bool InterruptPending
        {
            [NoHeapAllocation]
            get { return interruptPending; }
        }

        [NoHeapAllocation]
        public override void ClearInterrupt()
        {
#if VERBOSE
            Tracing.Log(Tracing.Debug, "Timer.ClearInterrupt()");
#endif
#if TIMER_NO_GO
            Tracing.Log(Tracing.Notice, "Unwanted timer interrupt!");
#endif // TIMER_NO_GO

            ClockLogger.AddEntry(10, rps, this);

            long currentTime = rps.GetKernelTicks(Timer2Read());

            this.interruptPending = false;

            irqCount++;
            ClockLogger.AddEntry(11, rps, this);
            pic.AckIrq(irq);
        }

        [NoHeapAllocation]
        private void PitAccessError()
        {
            DebugStub.Break();
        }


        [NoHeapAllocation]
        internal void PitWrite(int pt)
        {
#if TIMER_NO_GO
            return;
#endif // TIMER_NO_GO
            IoResult result;

            result = CWPort.Write8NoThrow(i8254_CW_MODE0 | i8254_CW_BOTH | i8254_CW_SEL0);
            DebugStub.Assert(IoResult.Success == result);

            result = C0Port.Write8NoThrow((byte)(pt & 0xff));
            DebugStub.Assert(IoResult.Success == result);

            result = C0Port.Write8NoThrow((byte)(pt >> 8));
            DebugStub.Assert(IoResult.Success == result);
            byte v;
            do {
                result = CWPort.Write8NoThrow(i8254_RB_NOCOUNT | i8254_RB_SEL0);
                DebugStub.Assert(IoResult.Success == result);

                result = C0Port.Read8NoThrow(out v);
                DebugStub.Assert(IoResult.Success == result);
            } while ((v & i8254_RB_NULL) == i8254_RB_NULL);
        }

        volatile int timer2reads = 0;

        [NoHeapAllocation]
        internal int Timer2Read()
        {
            timer2reads++;
            DebugStub.Assert(timer2reads == 1);

            IoResult result = CWPort.Write8NoThrow(i8254_RB_NOSTATUS | i8254_RB_SEL2);
            DebugStub.Assert(IoResult.Success == result);

            byte lo, hi;

            result = C2Port.Read8NoThrow(out lo);
            DebugStub.Assert(IoResult.Success == result);

            result = C2Port.Read8NoThrow(out hi);
            DebugStub.Assert(IoResult.Success == result);

            timer2reads--;
            DebugStub.Assert(timer2reads == 0);

            return (int)lo | ((int)hi << 8);
        }

        internal int PitRead()
        {
            CWPort.Write8(i8254_RB_ALL | i8254_RB_SEL0);
            byte status = C0Port.Read8();
            int pit1 = (int)C0Port.Read8() | ((int)C0Port.Read8() << 8);

            // Extend pit value using i8254 output bit
            if ((status & i8254_RB_OUT) == 0 ||
                (pit1 == 0 && interruptPending == true)) {
                pit1 += PitInterruptThreshold;
            }

            return pit1;
        }

        [ Conditional("DEBUG_TIMER") ]
        private void PitDirectReadTest()
        {
            uint[] p = new uint [6];

            PitWrite(0xffff);

            for (int i = 0; i < p.Length; i++) {
                CWPort.Write8(i8254_RB_NOSTATUS | i8254_RB_SEL0);
                p[i] = C0Port.Read8();
                p[i] += (uint) (((int)C0Port.Read8()) << 8);
            }
            Stop();

            DebugStub.Print("Direct back to back reads in pit ticks:" +
                            "{0} {1} {2} {3} {4} {5}\n",
                            __arglist(
                                p[0] - p[1],
                                p[1] - p[2],
                                p[2] - p[3],
                                p[3] - p[4],
                                p[4] - p[5]));
        }

        [ Conditional("DEBUG_TIMER") ]
        private void PitWriteReadTest()
        {
            DebugStub.Print("PitWriteRead() test...\n");
            int pitLast = 0x4fff;
            int pitNow;
            int pitEnd = 0x3fff;

            PitWrite(pitLast);
            do {
                pitNow = PitRead();
                if (pitNow > pitLast) {
                    DebugStub.Print("({0} > {1})\n",
                                    __arglist(pitNow, pitLast));
                    break;
                }
                pitLast = pitNow;
            } while (pitNow > pitEnd);

            DebugStub.Print((pitNow <= pitEnd) ? "PASSED\n" : "FAILED\n");
        }

        [Conditional("DEBUG_TIMER")]
        private void DoPitPerformanceTests()
        {
            PitWriteReadTest();

            ulong tsc0 = 0;
            ulong tsc1 = 0;

            for (int i = 0; i < 3; i++) {
                tsc0 = Processor.CycleCount;
                tsc0 = Processor.CycleCount;
                tsc0 = Processor.CycleCount;
                tsc0 = Processor.CycleCount;
                tsc1 = Processor.CycleCount;
                tsc1 = Processor.CycleCount;
                DebugStub.Print("Kernel.GetCpuCycleCount took {0} cycles\n",
                                __arglist(tsc1 - tsc0));
                ulong overhead = (tsc1 - tsc0) / 2;
                // On VPC this figure varies wildly
                // So it's set to zero and the measurement below include
                // the cost of measuring the cycles.
                overhead = 0;

                DebugStub.Print("PitTicksToTimeSpanTicks() in cycles...\n");
                for (int j = 0; j < 10; j++) {
                    tsc0 = Processor.CycleCount;
                    PitTicksToTimeSpanTicks(0);
                    tsc1 = Processor.CycleCount;
                    DebugStub.Print("{0}\n", __arglist(tsc1 - tsc0 - overhead));
                }

                DebugStub.Print("TimeSpanTicksToPitTicks() in cycles...\n");
                for (int j = 0; j < 10; j++) {
                    tsc0 = Processor.CycleCount;
                    TimeSpanTicksToPitTicks(0);
                    tsc1 = Processor.CycleCount;
                    DebugStub.Print("{0}\n", __arglist(tsc1 - tsc0 - overhead));
                }

                DebugStub.Print("PitWrite() in cycles...\n");
                for (uint n = 0; n < 10; n++) {
                    tsc0 = Processor.CycleCount;
                    PitWrite(0xffff);
                    tsc1 = Processor.CycleCount;
                    DebugStub.Print("{0}\n", __arglist(tsc1 - tsc0 - overhead));
                }
                Stop();

                PitWrite(0xffff);
                DebugStub.Print("PitRead() in cycles...\n");
                for (uint n = 0; n < 10; n++) {
                    tsc0 = Processor.CycleCount;
                    PitRead();
                    tsc1 = Processor.CycleCount;
                    DebugStub.Print("{0}\n", __arglist(tsc1 - tsc0));
                }
                Stop();

                DebugStub.Print("Pit Direct Read Test\n");
                PitDirectReadTest();

                // Eliminate spurious warnings from SSC
                tsc0 = tsc1;
                tsc1 = tsc0;
            }
        }
    }
}
