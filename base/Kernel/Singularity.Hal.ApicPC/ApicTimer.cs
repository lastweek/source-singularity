///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ApicTimer.cs
//
using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Hal
{
    public class ApicTimer : HalTimer
    {
        //
        // Constants
        //
        private readonly byte [] divisors = new byte [] {
            11 /*   1 */, 0 /*   2 */, 1 /*   4 */,  2 /*   8 */,
             3 /*  16 */, 8 /*  32 */, 9 /*  64 */, 10 // 128   
        };

        private const uint TimerPending  = 1u << 12;
        private const uint TimerMasked   = 1u << 16;
        private const uint TimerPeriodic = 1u << 17;

        private const uint TimeSpanHz = 10 * 1000 * 1000;
        private readonly TimeSpan maxInterruptInterval = new TimeSpan(TimeSpanHz / 10);     // 100ms
        private readonly TimeSpan minInterruptInterval = new TimeSpan(TimeSpanHz / 2000);   // 500us
        private readonly TimeSpan interruptGranularity = new TimeSpan(TimeSpanHz / 100000); //  10us

        //
        // Members
        //
        private Apic apic;
        private uint divisor      = 1;
        private uint busFrequency = 100000000;
        private uint frequency;     // == busFrequency / divisor
        private byte interrupt;

        //
        // Methods
        //
        internal ApicTimer(Apic apic)
        {
            this.apic = apic;
            SetDivisor(1);
            SetOneShot();
            SetInterruptEnabled(false);
            interrupt = apic.IrqToInterrupt(Apic.TimerIrq);
        }

        internal void ReleaseResources()
        {
        }

        internal byte Initialize()
        {
            SetInterruptVector(interrupt);
            SetDivisor(1);
            SetOneShot();
            SetBusFrequency(busFrequency);
            DebugStub.Print("ApicTimer interrupt is {0}\n", __arglist(interrupt));
            return interrupt;
        }

        internal void Start()
        {
            SetInterruptEnabled(true);
            SetNextInterrupt(maxInterruptInterval);
        }

        [NoHeapAllocation]
        internal void SetBusFrequency(uint measuredFrequency)
        {
            busFrequency = measuredFrequency;
            for (divisor = 1; divisor <= 128; divisor *= 2) {
                frequency = busFrequency / divisor;
                if (frequency < 100 * 1000 * 1000) {
                    break;
                }
            }
            SetDivisor(divisor);
        }

        /// <summary>
        /// Set processor clock bus divider.
        /// </summary>
        ///
        /// <param name ="amount">
        /// Amount to divide by.  Must be a power of 2 between 1 and 128.
        /// </param>
        [NoHeapAllocation]
        internal void SetDivisor(uint amount)
        {
            for (int i = 0; i < divisors.Length; i++) {
                if (amount <= (1u << i)) {
                    uint v = apic.Read(ApicOffset.TimerDivideConf) & ~0xfu;
                    v |= (uint)divisors[i];
                    apic.Write(ApicOffset.TimerDivideConf, v);
                    divisor = 1u << i;
                    return;
                }
            }
        }

        /// <summary>
        /// Get processor clock bus divider.
        /// </summary>
        [NoHeapAllocation]
        internal uint GetDivisor()
        {
            uint v = apic.Read(ApicOffset.TimerDivideConf) & 0xbu;
            for (int i = 0; i < divisors.Length; i++) {
                if ((uint)divisors[i] == v) {
                    return 1u << i;
                }
            }
            return ~0u;
        }

        [NoHeapAllocation]
        internal uint GetCurrentCount()
        {
            return apic.Read(ApicOffset.TimerCurrentCount);
        }

        internal uint Value
        {
            [NoHeapAllocation]
            get { return GetCurrentCount(); }
        }

        [NoHeapAllocation]
        internal void SetInitialCount(uint value)
        {
            apic.Write(ApicOffset.TimerInitialCount, value);
        }

        [NoHeapAllocation]
        internal void SetInterruptEnabled(bool enabled)
        {
            uint r = apic.Read(ApicOffset.LvtTimer) & ~TimerMasked;
            if (enabled == false) {
                r |= TimerMasked;
            }
            apic.Write(ApicOffset.LvtTimer, r);
        }

        [NoHeapAllocation]
        internal bool InterruptEnabled()
        {
            return (apic.Read(ApicOffset.LvtTimer) & TimerMasked) == 0;
        }

        [NoHeapAllocation]
        private void SetInterruptVector(byte interrupt)
        {
            uint r = (apic.Read(ApicOffset.LvtTimer) & ~0xffu) | interrupt;
            apic.Write(ApicOffset.LvtTimer, r);
        }

        [NoHeapAllocation]
        internal void SetPeriodic()
        {
            uint r = apic.Read(ApicOffset.LvtTimer) & ~TimerPeriodic;
            apic.Write(ApicOffset.LvtTimer, r | TimerPeriodic);
        }

        [NoHeapAllocation]
        internal void SetOneShot()
        {
            uint r = apic.Read(ApicOffset.LvtTimer) & ~TimerPeriodic;
            apic.Write(ApicOffset.LvtTimer, r);
        }

        internal byte Interrupt
        {
            [NoHeapAllocation]
            get { return interrupt; }
        }

        [NoHeapAllocation]
        public override void ClearInterrupt()
        {
            Microsoft.Singularity.Hal.Platform p = Microsoft.Singularity.Hal.Platform.ThePlatform;
            apic.AckIrq(Apic.TimerIrq);
	    SetNextInterrupt(maxInterruptInterval);
        }

        /// <summary>
        /// Set relative time of next interrupt.
        ///
        /// <param name="delta">
        /// Relative time of next interrupt.
        /// The time should be with the range between from <c>SetNextInterruptMinDelta</c> to
        /// <c>SetNextInterruptMaxDelta</c></param>.
        /// </summary>
        [NoHeapAllocation]
        public override void SetNextInterrupt(TimeSpan delta)
        {
            DebugStub.Assert(Processor.InterruptsDisabled());
            DebugStub.Assert(delta >= minInterruptInterval);
            DebugStub.Assert(delta <= maxInterruptInterval);

            SetInitialCount(TimeSpanToTimerTicks(delta));
        }

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
        public TimeSpan TimerToTimeSpanTicks(uint timerTicks)
        {
            return new TimeSpan(((long) TimeSpanHz * (long) timerTicks) / frequency);
        }

        [NoHeapAllocation]
        public uint TimeSpanToTimerTicks(TimeSpan timeSpan)
        {
            return (uint) (((long) frequency) * timeSpan.Ticks / TimeSpanHz);
        }
    }
}
