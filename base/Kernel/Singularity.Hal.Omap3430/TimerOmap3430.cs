///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TimerOmap3430.cs
//
//
// The OMAP platform has a plethora of timers to choose from,
// including 12 general-purpose timers, three watchdog timers,
// a 32-kHz synchronised timer and a frame adjustment counter
// for USB applications.
//
// Each of the general-purpose timers are free-running upward
// counters which can be run from either a 32-kHz clock or the
// system clock (12, 13, 19.2, 24, 26, or 38.4 MHz), with the
// option of passing the system clock through a pre-scaler to
// divide it by 2^0 -> 2^8 as desired.
//
// Each of the general purpose timers also provides the option
// of operating in three modes: timer, capture and compare.
//
// The compare mode allows an interrupt and counter value reload
// to happen at an arbitrary counter value. The capture  mode
// allows the value of the timer to be captured and an interrupt
// possibly generated the next time the counter reaches that
// value. The timer mode allows standard periodic and one-shot
// timer behaviour, with value reload and interrupts happening
// when the counter value transitions from 0xffffffff -> 0x0.
//
// The 32-bit width of the timer admits a wide degree of
// flexibility in the use of general-purpose timers, and so for
// our present purposes it is sufficient to use the GP timer in
// the basic timer mode with the 32 kHz clock, giving a minimum
// period of 1/32,768 s = 30.5us and a maximum period of
// (2^32 - 1) / 2^15 s ~= 131,072s = 36hrs 24mins 32s.
//
// As the maximum interval is expressed as a long in units of
// 100ns, the maximum interval for a timer which can be
// expressed is comfortably larger than this (0x7fffffffffffffff
// / 365 / 24 / 60 / 60 / 1000 / 1000 / 10) = ~29,247 years
//
#define VERBOSE

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
    [Signature("/arm/ti/3430/GPTIMER1")]
    public sealed class TimerResources : DriverCategoryDeclaration
    {
        // register block
        [IoMemoryRange(0, Default = 0x48318000, Length = 0x1000)]
        internal readonly IoMemoryRange registers;

        // interrupt
        [IoIrqRange(1, Default = 37)]
        internal readonly IoIrqRange irq;

        // CTR will create the rest of this class:
        public TimerResources(IoConfig config)
        {
            // dynamic resources
            registers = (IoMemoryRange)config.DynamicRanges[0];
            irq = (IoIrqRange)config.DynamicRanges[1];
        }
    }

    [CLSCompliant(false)]
    public sealed class TimerOmap3430 : HalTimer
    {
        // size of registers in block
        const int Omap3430_TIMER1_RegisterSize      = 0x0000005c; // size of registers in block

        // clock frequency
        const uint Omap3430_TIMER1_Freq             = 32768;

        // registers
        const uint Omap3430_TISR                    = 0x00000018; // interrupt status
        const uint Omap3430_TIER                    = 0x0000001c; // interrupt enable
        const uint Omap3430_TCLR                    = 0x00000024; // control
        const uint Omap3430_TCRR                    = 0x00000028; // timer counter
        const uint Omap3430_TLDR                    = 0x0000002c; // timer load

        // interrupt status register fields
        const uint Omap3430_TISR_TCAR_IT_FLAG       = 0x00000001; // capture interrupt
        const uint Omap3430_TISR_OVF_IT_FLAG        = 0x00000002; // overflow interrupt
        const uint Omap3430_TISR_MAT_IT_FLAG        = 0x00000004; // match interrupt

        // interrupt enable register fields
        const uint Omap3430_TIER_TCAR_IT_ENA        = 0x00000001; // capture interrupt
        const uint Omap3430_TIER_OVF_IT_ENA         = 0x00000002; // overflow interrupt
        const uint Omap3430_TIER_MAT_IT_ENA         = 0x00000004; // match interrupt

        // timer control register fields
        const uint Omap3430_TCLR_ST                 = 0x00000001; // start timer
        const uint Omap3430_TCLR_AR                 = 0x00000002; // auto-reload
        const uint Omap3430_TCLR_PTV_Mask           = 0x0000001c; // prescaler trigger value
        const uint Omap3430_TCLR_PTV_Shift          = 2;          // prescaler trigger value
        const uint Omap3430_TCLR_PRE                = 0x00000020; // prescale enable
        const uint Omap3430_TCLR_CE                 = 0x00000040; // compare enable
        const uint Omap3430_TCLR_SCPWM              = 0x00000080; // PWM value when stopped
        const uint Omap3430_TCLR_TCM_Rising         = 0x00000100; // trigger capture mode
        const uint Omap3430_TCLR_TCM_Falling        = 0x00000200; // trigger capture mode
        const uint Omap3430_TCLR_TCM_Both =                       // trigger capture mode
            (Omap3430_TCLR_TCM_Rising | Omap3430_TCLR_TCM_Falling);
        const uint Omap3430_TCLR_TRG_Overflow       = 0x00000002; // trigger output mode
        const uint Omap3430_TCLR_TRG_OvrMatch       = 0x00000002; // trigger output mode
        const uint Omap3430_TCLR_PT                 = 0x00000004; // PWM toggle select
        const uint Omap3430_TCLR_CAPT_MODE          = 0x00000001; // capture mode
        const uint Omap3430_TCLR_GPO_CFG            = 0x00000002; // PWM config

        // resource allocation
        private PnpConfig   config;
        private Pic         pic;
        private byte        irq;

        // registers
        private IoMappedPort tisr;
        private IoMappedPort tier;
        private IoMappedPort tclr;
        private IoMappedPort tcrr;
        private IoMappedPort tldr;

        // timer state
        private volatile bool interruptPending = false;
        internal volatile uint irqCount = 0;

        int ticksPerSecond = 0;

        // Constructor
        internal TimerOmap3430(PnpConfig config, Pic pic)
        {
#if VERBOSE
            DebugStub.WriteLine("TimerOmap3430: create");
#endif
            TimerResources tr = new TimerResources(config);

            this.config = config;
            this.pic    = pic;
            this.irq    = tr.irq.Irq;

            IoMemory timerRegisters = tr.registers
                .MemoryAtOffset(0, Omap3430_TIMER1_RegisterSize, Access.ReadWrite);

            tisr = timerRegisters.MappedPortAtOffset(Omap3430_TISR, 4, Access.ReadWrite);
            tier = timerRegisters.MappedPortAtOffset(Omap3430_TIER, 4, Access.ReadWrite);
            tclr = timerRegisters.MappedPortAtOffset(Omap3430_TCLR, 4, Access.ReadWrite);
            tcrr = timerRegisters.MappedPortAtOffset(Omap3430_TCRR, 4, Access.ReadWrite);
            tldr = timerRegisters.MappedPortAtOffset(Omap3430_TLDR, 4, Access.ReadWrite);

            // _ARM_ERRATA problem with how functional clock is unstuck
            tcrr.Write32(0, 0);
        }

        public byte Initialize()
        {
#if VERBOSE
            DebugStub.WriteLine("Timer.Initialize()");
#endif

            SetOneShot();
            SetInterruptEnabled(false);
            Stop();

            pic.EnableIrq(irq);
            return pic.IrqToInterrupt(irq);
        }

        public void Finalize()
        {
            pic.DisableIrq(irq);
            Stop();
        }

        internal void SetTicksPerSecond(int count)
        {
#if FALSE
            ticksPerSecond = count;
#endif
#if VERBOSE
            DebugStub.WriteLine("gptimer1 frequency {0} Hz.", __arglist(count));
#endif
        }

        [NoHeapAllocation]
        internal uint Read(IoMappedPort register)
        {
            uint outValue;
            IoResult result = register.Read32NoThrow(0, out outValue);
            DebugStub.Assert(IoResult.Success == result);
            return outValue;
        }

        [NoHeapAllocation]
        internal void Write(IoMappedPort register, uint value)
        {
            IoResult result = register.Write32NoThrow(0, value);
            DebugStub.Assert(IoResult.Success == result);
        }

        [NoHeapAllocation]
        internal uint GetCurrentCount()
        {
            return Read(tcrr);
        }

        [NoHeapAllocation]
        internal void SetInitialCount(uint value)
        {
            // Write current counter & reload values
            Write(tcrr, value);
            Write(tldr, value);
        }

        [NoHeapAllocation]
        internal void SetInterruptEnabled(bool enabled)
        {
            uint ie = Read(tier) & ~Omap3430_TIER_OVF_IT_ENA;

            if (enabled) {
                ie |= Omap3430_TIER_OVF_IT_ENA;
            }
            Write(tier, ie);
        }

        [NoHeapAllocation]
        internal bool InterruptEnabled()
        {
            return (Read(tier) & Omap3430_TIER_OVF_IT_ENA) != 0;
        }

        [NoHeapAllocation]
        internal void Start()
        {
            bool iflag = Processor.DisableInterrupts();
            try {

                // Start counter running
                Write(tclr, Omap3430_TCLR_ST);

            }
            finally {
                Processor.RestoreInterrupts(iflag);
            }
        }

        [NoHeapAllocation]
        internal void Stop()
        {
            bool iflag = Processor.DisableInterrupts();
            try {

                // Stop counter running
                uint val = Read(tclr) & ~Omap3430_TCLR_ST;
                Write(tclr, val);

            }
            finally {
                Processor.RestoreInterrupts(iflag);
            }
        }

        [NoHeapAllocation]
        internal void SetPeriodic()
        {
            uint val = Read(tclr) | Omap3430_TCLR_AR;
            Write(tclr, val);
        }

        [NoHeapAllocation]
        internal void SetOneShot()
        {
            uint val = Read(tclr) & ~Omap3430_TCLR_AR;
            Write(tclr, val);
        }

        private readonly TimeSpan maxInterruptInterval
        = new TimeSpan((((1 << 32) - 1) * (1000 * 1000 * 10)) / Omap3430_TIMER1_Freq); // 36.4 hours
        private readonly TimeSpan minInterruptInterval
        = new TimeSpan(((1000 * 1000 * 10) + Omap3430_TIMER1_Freq) / Omap3430_TIMER1_Freq); // 30.5us, rounded up
        private readonly TimeSpan interruptGranularity
        = new TimeSpan((1000 * 1000 * 10) / Omap3430_TIMER1_Freq); // 30.5us

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
#if VERBOSE
            DebugStub.WriteLine("Timer.SetNextInterrupt({0})", __arglist(delta.Ticks));
#endif
            DebugStub.Assert(Processor.InterruptsDisabled());
            DebugStub.Assert(delta >= minInterruptInterval);
            DebugStub.Assert(delta <= maxInterruptInterval);

            bool iflag = Processor.DisableInterrupts();
            try {
                // NB: cast is safe as (delta <= MaxInterruptInterval)
                uint timerIntervals = (uint)((delta.Ticks * Omap3430_TIMER1_Freq)
                                             / (1000 * 1000 * 10));
                uint count = (0xffffffff - timerIntervals) + 1;

                Write(tldr, count);
                SetPeriodic();
                SetInterruptEnabled(true);
                Start();

                interruptPending = true;
            }
            finally {
                Processor.RestoreInterrupts(iflag);
            }
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
            DebugStub.WriteLine("Timer.ClearInterrupt()");
#endif

            interruptPending = false;
            irqCount++;

            Write(tisr, Omap3430_TISR_OVF_IT_FLAG);
        }
    }
}


//
// Definitions for registers in GPTIMERx that we aren't currently using
//

//      // timer register base
//      const uint Omap3430_TIMER1_Base = 0x48318000; // GPTIMER1
//      const uint Omap3430_TIMER2_Base = 0x49032000; // GPTIMER2

//        // registers
//        private IoMemory tidr;
//        private IoMemory tiocp_cfg;
//        private IoMemory tistat;
//        private IoMemory tisr;
//        private IoMemory tier;
//        private IoMemory twer;
//        private IoMemory tclr;
//        private IoMemory tcrr;
//        private IoMemory tldr;
//        private IoMemory ttgr;
//        private IoMemory twps;
//        private IoMemory tmar;
//        private IoMemory tcar1;
//        private IoMemory tsicr;
//        private IoMemory tcar2;
//        private IoMemory tpir;
//        private IoMemory tnir;
//        private IoMemory tcvr;
//        private IoMemory tocr;
//        private IoMemory towr;


        // ID register fields
        //const uint Omap3430_TIDR_TID_REV                  = 0x000000ff; // whole id
        //const uint Omap3430_TIDR_TID_REV_Major            = 0x000000f0; // major revision
        //const uint Omap3430_TIDR_TID_REV_Minor            = 0x0000000f; // minor revision

        // L4 interface config register fields
        //const uint Omap3430_TIOCP_CFG_AUTOIDLE            = 0x00000001; // auto L4 clk gating
        //const uint Omap3430_TIOCP_CFG_SOFTRESET           = 0x00000002; // software reset
        //const uint Omap3430_TIOCP_CFG_ENAWAKEUP           = 0x00000004; // wake-up enable
        //const uint Omap3430_TIOCP_CFG_IDLEMODE_Mask       = 0x00000018; // idle mask
        //const uint Omap3430_TIOCP_CFG_IDLEMODE_Force      = 0x00000000; // force idle
        //const uint Omap3430_TIOCP_CFG_IDLEMODE_None       = 0x00000008; // deny idle
        //const uint Omap3430_TIOCP_CFG_IDLEMODE_Smart      = 0x00000010; // smart idle
        //const uint Omap3430_TIOCP_CFG_EMUFREE             = 0x00000020; // timer is free-running under emulation (debug)
        //const uint Omap3430_TIOCP_CFG_CLOCKACTIVITY_Mask  = 0x00000300; // wake-up mode clock activity
        //const uint Omap3430_TIOCP_CFG_CLOCKACTIVITY_L4    = 0x00000100; // maintain L4 clk in wake-up
        //const uint Omap3430_TIOCP_CFG_CLOCKACTIVITY_Func  = 0x00000200; // maintain functional clks in wake-up

        // Registers
        //const uint Omap3430_TIDR          = 0x00000000; // ID
        //const uint Omap3430_TIOCP_CFG     = 0x00000010; // L4 interface config
        //const uint Omap3430_TISTAT        = 0x00000014; // timer status
        //const uint Omap3430_TISR          = 0x00000018; // interrupt status
        //const uint Omap3430_TIER          = 0x0000001c; // interrupt enable
        //const uint Omap3430_TWER          = 0x00000020; // wake-up enable
        //const uint Omap3430_TCLR          = 0x00000024; // control
        //const uint Omap3430_TCRR          = 0x00000028; // timer counter
        //const uint Omap3430_TLDR          = 0x0000002c; // timer load
        //const uint Omap3430_TTGR          = 0x00000030; // timer trigger
        //const uint Omap3430_TWPS          = 0x00000034; // write-posted status
        //const uint Omap3430_TMAR          = 0x00000038; // match value
        //const uint Omap3430_TCAR1         = 0x0000003c; // counter capture 1
        //const uint Omap3430_TSICR         = 0x00000040; // L4 interface sync control
        //const uint Omap3430_TCAR2         = 0x00000044; // counter capture 2
        //const uint Omap3430_TPIR          = 0x00000048; // +ve increment
        //const uint Omap3430_TNIR          = 0x0000004c; // -ve increment
        //const uint Omap3430_TCVR          = 0x00000050; // counter value
        //const uint Omap3430_TOCR          = 0x00000054; // overflow counter
        //const uint Omap3430_TOWR          = 0x00000058; // overflow wrapping
