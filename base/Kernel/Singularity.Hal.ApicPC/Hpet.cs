///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    Based on IA-PC HPET (High Precision Event Timers) Specification
//    Revision 1.0, June 2004.
//
//    The HPET code includes unchecked I/O memory operations so
//    methods can be marked as NoHeapAllocation.  CreateDevice()
//    must verify that there is at least enough memory for the
//    MainTimer.

namespace Microsoft.Singularity.Hal
{
    using Microsoft.Singularity.Io;
    using Microsoft.Singularity.Configuration;

    using System;
    using System.Runtime.CompilerServices;

    internal struct HpetTimerCaps
    {
        internal const uint FsbDelivery     = 1u << 15;
        internal const uint Width64         = 1u << 5;
        internal const uint PeriodicSupport = 1u << 4;

        internal const uint Mask = FsbDelivery | Width64 | PeriodicSupport;
    }

    internal struct HpetTimerConf
    {
        internal const uint LevelTriggered  = 1u << 1;
        internal const uint InterruptEnable = 1u << 2;
        internal const uint PeriodicMode    = 1u << 3;
        internal const uint Force32Bit      = 1u << 8;
    }

    [DriverCategory]
    [Signature("/pnp/PNP0103")]
    public sealed class HpetResources : DriverCategoryDeclaration
    {
        [IoMemoryRange(0, Default = 0, Length = 0x400)]
        public IoMemoryRange mem1;
    }

    internal sealed class Hpet : IDevice
    {
        private PnpConfig config;
        private IoMemory  region;

        private const int MainCounterOffset = 0xf0;

        internal const int MinRegionBytes = 0xf8;

        uint periodFs;              // femtoseconds
        uint capabilities;          // bits 0-31 at offset 0

        internal Hpet(PnpConfig config)
        {
            int  cpuId;
            Microsoft.Singularity.Hal.Platform p = Microsoft.Singularity.Hal.Platform.ThePlatform;
            cpuId = p.ApicId;

            this.config = config;
            IoMemoryRange imr = (IoMemoryRange) config.DynamicRanges[0];
            this.region = imr.MemoryAtOffset(0, (int) imr.Length.ToUInt32(),
                                             Access.ReadWrite);

            capabilities = region.Read32(0x00);
            periodFs     = region.Read32(0x04);

            if (cpuId == 0) {
                DebugStub.Print("new Hpet writing regions\n");
                // Disable interrupts on timers
                for (uint i = 0; i <= MaxCounterIndex; i++) {
                    DisableInterrupt(i);
                }

                uint gc = region.Read32(0x10) & ~3u;    // Clear legacy bits
                region.Write32(0x10, gc | 1);           // Enable main counter
            }
        }

        private bool MainCounterWorks()
        {
            uint first = this.MainCounterValue32;
            for (int i = 0; i < 50; i++) {
                if (this.MainCounterValue32 != first) {
                    return true;
                }
            }
            return false;
        }

        void IDevice.Initialize()
        {
        }

        void IDevice.Finalize()
        {
        }

        /// <summary> Period in femptoseconds (10^-15) </summary>
        internal uint PeriodFs
        {
            [NoHeapAllocation]
            get { return periodFs; }
        }

        internal ushort VendorId
        {
            [NoHeapAllocation]
            get { return (ushort) (capabilities >> 16); }
        }

        internal uint Width
        {
            [NoHeapAllocation]
            get { return ((capabilities & 0x2000) != 0) ? 64u : 32u; }
        }

        internal uint MaxCounterIndex
        {
            [NoHeapAllocation]
            get { return ((capabilities >> 8) & 0xf); }
        }

        internal uint AvailableCounters
        {
            [NoHeapAllocation]
            get { return MaxCounterIndex + 1; }
        }

        internal uint Revision
        {
            [NoHeapAllocation]
            get { return capabilities & 0xff; }
        }

        internal ulong MainCounterValue
        {
            [NoHeapAllocation]
            get {
                ulong value;
                uint hi;
                do {
                    IoResult r;
                    r = region.Read64NoThrow(MainCounterOffset, out value);
                    DebugStub.Assert(IoResult.Success == r);
                    r = region.Read32NoThrow(MainCounterOffset + 4, out hi);
                    DebugStub.Assert(IoResult.Success == r);
                } while ((uint)(value >> 32) != hi);
                return value;
            }
        }

        internal uint MainCounterValue32
        {
            [NoHeapAllocation]
            get {
                uint value;
                IoResult r = region.Read32NoThrow(MainCounterOffset,
                                                  out value);
                DebugStub.Assert(IoResult.Success == r);
                return value;
            }
        }

        [NoHeapAllocation]
        internal void ClearInterrupt(uint timer)
        {
            if (timer <= MaxCounterIndex) {

                uint value;
                IoResult result = region.Read32NoThrow(0x20, out value);
                DebugStub.Assert(IoResult.Success == result);
                value = value & ~(1u << (int)timer);

                result = region.Write32NoThrow(0x20, value);
                DebugStub.Assert(IoResult.Success == result);
            }
        }

        [NoHeapAllocation]
        private int TimerOffset(uint timer)
        {
            return 0x100 + 0x20 * (int)timer;
        }

        internal void DisableInterrupt(uint timer)
        {
            if (timer <= MaxCounterIndex) {
                uint m = region.Read32(TimerOffset(timer));
                m &= ~HpetTimerConf.InterruptEnable;
                region.Write32(TimerOffset(timer), m);
            }
        }

        internal static IDevice CreateDevice(IoConfig config, string name)
        {
            PnpConfig pnpConfig = config as PnpConfig;
            if (pnpConfig == null) {
                return null;
            }

            IoMemoryRange imr = config.DynamicRanges[0] as IoMemoryRange;
            if (imr == null) {
                return null;
            }

            int imrBytes = (int)imr.Length.ToUInt32();
            if (imrBytes < Hpet.MinRegionBytes) {
                DebugStub.Write(
                    "HPET failed as region too small ({0} bytes).\n",
                    __arglist(imrBytes));
                return null;
            }

            Hpet hpet = new Hpet(pnpConfig);

            if (hpet.MainCounterWorks()) {
                HalDevicesApic.SwitchToHpetClock(hpet);
            }
            else {
                DebugStub.Print("WARNING: HPET main counter does not work!\n");
            }

            return hpet;
        }
    }
}
