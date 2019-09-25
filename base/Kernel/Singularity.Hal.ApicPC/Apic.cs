///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Apic.cs
//
//  Note:
//    Intel MP Specification 1.4
//    IA-32 Intel Architecture Software Developers Manual
//       Volume 3: Systems Programming Guide
//
//  Caution:
//    This code has not been well tested on multi I/O apic systems.

// #define DEBUG_FIXED_IPI
// #define PRINT_IO_APICS
// #define DEBUG_IO_APIC_IRQ_MASK

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity.Hal
{
    internal struct ApicOffset
    {
        internal const uint Id                      = 0x0020;
        internal const uint Version                 = 0x0030;
        internal const uint TaskPriority            = 0x0080;
        internal const uint ArbitrationPriority     = 0x0090;
        internal const uint ProcessorPriority       = 0x00a0;
        internal const uint EoiRegister             = 0x00b0;
        internal const uint LocalDestination        = 0x00d0;
        internal const uint DestinationFormat       = 0x00e0;
        internal const uint SpuriousIntVector       = 0x00f0;
        internal const uint IsrBase                 = 0x0100;
        internal const uint TmrBase                 = 0x0180;
        internal const uint IrrBase                 = 0x0200;
        internal const uint ErrorStatus             = 0x0280;
        internal const uint IcrLo                   = 0x0300;
        internal const uint IcrHi                   = 0x0310;
        internal const uint LvtTimer                = 0x0320;
        internal const uint LvtThermalSensor        = 0x0330;
        internal const uint LvtPerfCounts           = 0x0340;
        internal const uint LvtLint0                = 0x0350;
        internal const uint LvtLint1                = 0x0360;
        internal const uint LvtError                = 0x0370;
        internal const uint TimerInitialCount       = 0x0380;
        internal const uint TimerCurrentCount       = 0x0390;
        internal const uint TimerDivideConf         = 0x03e0;
        internal const uint Max                     = 0x0400;
    };

    internal struct LvtFlags
    {
        internal const uint TimerBit      = 1 << 17;
        internal const uint      Periodic    = TimerBit;
        internal const uint      OneShot     = 0;
        internal const uint MaskedBit     = 1 << 16;
        internal const uint      Masked      = MaskedBit;
        internal const uint      Unmasked    = 0;
        internal const uint TriggerBit    = 1 << 15;
        internal const uint      Level        = TriggerBit;
        internal const uint      Edge         = 0;
        internal const uint RIRRBit       = 1 << 14;
        internal const uint PolarityBit   = 1 << 13;
        internal const uint      ActiveLow    = PolarityBit;
        internal const uint      ActiveHigh   = 0;
        internal const uint StatusBit     = 1 << 12;
        internal const uint      Pending      = StatusBit;
        internal const uint      Idle         = 0;
        internal const uint DeliveryBits = 7 << 8;
        internal const uint      Fixed        = 0 << 8;
        internal const uint      SMI          = 2 << 8;
        internal const uint      NMI          = 4 << 8;
        internal const uint      INIT         = 5 << 8;
        internal const uint      ExtInt       = 7 << 8;
    }

    internal struct IcrFlags
    {
        internal const uint ShorthandBits   = 3 << 18;
        internal const uint     NoShortHand     = 0 << 18;
        internal const uint     Self            = 1 << 18;
        internal const uint     All             = 2 << 18;
        internal const uint     AllBarSelf      = 3 << 18;
        internal const uint TriggerBit      = 1 << 15;
        internal const uint     Edge            = 0;
        internal const uint     Level           = TriggerBit;
        internal const uint LevelBit        = 1 << 14;
        internal const uint     DeAssert        = 0;
        internal const uint     Assert          = LevelBit;
        internal const uint StatusBit       = 1 << 12;
        internal const uint     Idle            = 0;
        internal const uint     Pending         = StatusBit;
        internal const uint ModeBit         = 1 << 11;
        internal const uint     Physical        = 0;
        internal const uint     Logical         = ModeBit;
        internal const uint DeliveryBits    = 7 << 8;
        internal const uint      Fixed          = 0 << 8;
        internal const uint      SMI            = 2 << 8;
        internal const uint      NMI            = 4 << 8;
        internal const uint      INIT           = 5 << 8;
        internal const uint      StartUp        = 6 << 8;
    }

    [CLSCompliant(false)]
    public class Apic : HalPic
    {
        const ushort ImcrAddressPort   = 0x22;
        const ushort ImcrDataPort      = 0x23;
        const byte   ImcrAddressSelect = 0x70;
        const byte   ImcrData8259      = 0x00;
        const byte   ImcrDataApic      = 0x01;

        const byte   ApicMSR           = 0x1b;

        public const byte RtClockIrq = 8;
        public const byte TimerIrq   = 0;

        static uint baseAddr;
        // Table of Apic Ids before changed to cpu-id.
        static byte [] initialIdTable;

        IoMemory  apicRegion;
        IoApic [] ioApics;
        byte      baseVector;
        byte      maxIrq;

        public Apic(IoApic[] ioApics)
        {
            ulong msr = Isa.ReadMsr(0x1b);
            baseAddr  = ((uint) msr) & 0xfffff000u;

            this.apicRegion =
                IoMemory.MapPhysicalMemory(baseAddr,
                                           new UIntPtr(ApicOffset.Max),
                                           true, true);
            this.ioApics = ioApics;

            DebugStub.Assert(initialIdTable == null); // Check Single Apic instance
            initialIdTable = new byte [256];
        }

        public Apic()
        {
            ulong msr = Isa.ReadMsr(0x1b);
            baseAddr  = ((uint) msr) & 0xfffff000u;

            this.apicRegion =
                IoMemory.MapPhysicalMemory(baseAddr,
                                           new UIntPtr(ApicOffset.Max),
                                           true, true);
        }


        internal void ReleaseResources()
        {
        }

        [NoHeapAllocation]
        internal uint Read(uint offset)
        {
            uint outValue;
            IoResult result = apicRegion.Read32NoThrow((int) offset,
                                                       out outValue);
            DebugStub.Assert(IoResult.Success == result);
            return outValue;
        }

        [NoHeapAllocation]
        internal void Write(uint offset, uint value)
        {
            IoResult result = apicRegion.Write32NoThrow((int) offset, value);
            DebugStub.Assert(IoResult.Success == result);
        }

        internal byte Id
        {
            [NoHeapAllocation]
            get { return (byte)(Read(ApicOffset.Id) >> 24); }
        }

        [NoHeapAllocation]
        private void SetId(byte cpuId)
        {
            uint v = Read(ApicOffset.Id);
            initialIdTable[cpuId] = (byte)(v >> 24);
            v = (v & 0xffffff) | (((uint)cpuId) << 24);
            Write(ApicOffset.Id, v);
        }

        private bool IsBsp
        {
            [NoHeapAllocation]
            get { return (Isa.ReadMsr(0x1b) & 0x100) == 0x100; }
        }

        [NoHeapAllocation]
        private IoApic GetIoApic(int id)
        {
            for (int i = 0; i < ioApics.Length; i++) {
                if (ioApics[i].GetId() == id) {
                    return ioApics[i];
                }
            }
            return null;
        }

        internal void Initialize(byte baseVector)
        {
            DebugStub.Assert(255 - baseVector >= 48);
            this.baseVector = baseVector;

            Write(ApicOffset.LvtTimer, LvtFlags.Masked);
            Write(ApicOffset.LvtThermalSensor, LvtFlags.Masked);
            Write(ApicOffset.LvtPerfCounts, LvtFlags.Masked);
            Write(ApicOffset.LvtError, LvtFlags.Masked);
            Write(ApicOffset.SpuriousIntVector, 0xdfu);

            // set task priority to 0 so that it can
            // receive all interrupts from IPI
            // Write(ApicOffset.TaskPriority, 0x20u);
            Write(ApicOffset.TaskPriority, 0);

            Write(ApicOffset.LvtLint0, LvtFlags.Masked);
            Write(ApicOffset.LvtLint1, LvtFlags.Masked);

            SetId((byte) Processor.GetCurrentProcessorId());

            if (this.IsBsp) {
                InitializeRouteableEntries();
                InitializeMpResourceEntries();
            }

            // Enable in s/w
            SetEnabled(true);

            // Enable in h/w
            Isa.WriteMsr(ApicMSR, Isa.ReadMsr(ApicMSR) | (1 << 11));

            // Watch out for the uniprocessor case where the
            // FloatingPointer may be null.
            MpFloatingPointer floatingPointer = MpResources.FloatingPointer;

            if (floatingPointer != null && floatingPointer.ImcrPresent && this.IsBsp) {
                IoPort addrPort = new IoPort(ImcrAddressPort, 1, Access.Write);
                IoPort dataPort = new IoPort(ImcrDataPort, 1, Access.Write);
                addrPort.Write8(ImcrAddressSelect);
                dataPort.Write8(ImcrDataApic);
            }

            Write(ApicOffset.LvtLint0, LvtFlags.Level | LvtFlags.ExtInt);
            Write(ApicOffset.LvtLint1, LvtFlags.NMI | 0x02);

            for (int z = 0; z <= maxIrq; z++) {
                byte m = IrqToInterrupt((byte) z);
                byte n = InterruptToIrq(m);
                DebugStub.Assert((byte) z == n);
            }
        }

        internal void Initialize()
        {
            Initialize(0x70);
        }

        [NoHeapAllocation]
        private void PrintIoApics()
        {
#if PRINT_IO_APICS
            for (int i = 0; i < ioApics.Length; i++) {
                IoApicInspector.PrintApic(ioApics[i]);
            }
            DebugStub.Print("--------------------------------\n");
#endif
        }

        private void InitializeRouteableEntries()
        {
            DebugStub.Print("Initializing Apic routeable entries\n");
            // Initialize entries that may not be part of MP set
            // configuration, but might be utilizable via a
            // programmable interrupt routing on PCI-LPC bridge
            // or elsewhere.
            byte   irq = 16;
            IoBits stdPciBits = (IoBits.DstPhysical | IoBits.DelModFixed     |
                                 IoBits.IrqMask     | IoBits.IntPolActiveLow |
                                 IoBits.TriggerModeLevel);
            for (int id = 0; id < ioApics.Length; id++) {
                uint start = (id == 0) ? 16u : 0u;
                uint end   = ioApics[id].RedirectionEntryCount;
                for (uint index = start; index < end; index++) {
                    RedirectionEntry re =
                        new RedirectionEntry(this.Id, stdPciBits,
                                             IrqToInterrupt(irq));
                    ioApics[id].SetRedirectionEntry(index, ref re);
                    irq++;
#if PRINT_IO_APICS
                    DebugStub.Print("Added routeable entry for apic 0x{0:x}: IRQ 0x{1:x} => 0x{2:x}\n",
                                    __arglist(id, irq, IrqToInterrupt(irq)));
#endif
                }
            }
            maxIrq = (byte) (irq - 1);
            PrintIoApics();
        }

        private void InitializeMpResourceEntries()
        {
            if (MpResources.FloatingPointer != null) {
                DebugStub.Print("Initializing Apic redirections from MpResources\n");
                foreach (MpInterruptEntry e in MpResources.IoInterruptEntries) {
                    IoApic ioApic = GetIoApic(e.ApicId);
                    if (ioApic == null) {
                        DebugStub.Print("Could not find I/O Apic with id {0}\n",
                                        __arglist(e.ApicId));
                        continue;
                    }

                    MpBusEntry be = MpResources.GetBusEntryById(e.BusId);
                    if (be == null) {
                        DebugStub.Print("Unknown bus device id {0:x2}\n",
                                        __arglist(e.BusId));
                        continue;
                    }

                    if (be.BusType == BusType.ISA) {
                        ConfigureIsaInterrupt(ioApic, e);
                    }
                    else if (be.BusType == BusType.PCI) {
                        ConfigurePciInterrupt(ioApic, e);
                    }
                    else {
                        DebugStub.Print("Unhandled device on bus {0:x2}\n",
                                        __arglist(e.BusId));
                        continue;
                    }
                }
            }
            else {
                DebugStub.Print("Initializing Apic redirections to defaults\n");
                // If there are no MP tables, set up a standard mapping for the IRQs on CPU 0
                uint   end = 16;
                IoBits stdBits = (IoBits.DstPhysical | IoBits.DelModFixed     |
                                  IoBits.IrqMask     | IoBits.IntPolActiveLow |
                                  IoBits.TriggerModeEdge);

                for (uint z = 0; z < end; z++) {
                    RedirectionEntry re = new RedirectionEntry(this.Id, stdBits, IrqToInterrupt((byte) z));
                    ioApics[0].SetRedirectionEntry((byte) z, ref re);
                }
            }
            PrintIoApics();
        }

        internal void ConfigureIsaInterrupt(IoApic ioApic, MpInterruptEntry e)
        {
            byte vector = IrqToInterrupt(e.BusIrq);

            IoBits iobits = (e.PolarityType == Polarity.ActiveLow) ?
                IoBits.IntPolActiveLow : IoBits.IntPolActiveHigh;

            iobits |= (e.TriggerType == Trigger.Level) ?
                IoBits.TriggerModeLevel : IoBits.TriggerModeEdge;
            iobits |= IoBits.DstPhysical;
            iobits |= IoBits.DelModFixed;
            iobits |= IoBits.IrqMask;

            RedirectionEntry r = new RedirectionEntry(this.Id, iobits, vector);
            ioApic.SetRedirectionEntry(e.ApicLine, ref r);

#if PRINT_IO_APICS
            DebugStub.Print("Added ISA interrupt for apic 0x{0:x}: Line 0x{1:x} => 0x{2:x}\n",
                            __arglist(ioApic.GetId(), e.ApicLine, vector));
#endif
        }

        internal void ConfigurePciInterrupt(IoApic ioApic, MpInterruptEntry e)
        {
            byte vector = IrqToInterrupt(e.ApicLine);

            IoBits iobits = (e.PolarityType == Polarity.ActiveHigh) ?
                IoBits.IntPolActiveHigh : IoBits.IntPolActiveLow;
            iobits |= (e.TriggerType == Trigger.Edge) ?
                IoBits.TriggerModeEdge : IoBits.TriggerModeLevel;
            iobits |= IoBits.DstPhysical;
            iobits |= IoBits.DelModFixed;
            iobits |= IoBits.IrqMask;
            RedirectionEntry r = new RedirectionEntry(this.Id, iobits, vector);
            ioApic.SetRedirectionEntry(e.ApicLine, ref r);

#if PRINT_IO_APICS
            DebugStub.Print("Added PCI interrupt for apic 0x{0:x}: Line 0x{1:x} => 0x{2:x}\n",
                            __arglist(ioApic.GetId(), e.ApicLine, vector));
#endif
        }

        [NoHeapAllocation]
        public override byte InterruptToIrq(byte interrupt)
        {
            DebugStub.Assert(interrupt >= baseVector);

            return (byte)(interrupt - (baseVector + 32));
        }

        [NoHeapAllocation]
        public override byte IrqToInterrupt(byte irq)
        {
            byte interrupt = (byte) (baseVector + 32 + irq);

            DebugStub.Assert(interrupt >= baseVector);

            return interrupt;
        }

        public override byte MaximumIrq
        {
            [NoHeapAllocation]
            get { return maxIrq; }
        }

        [NoHeapAllocation]
        public void SetEnabled(bool enabled)
        {
            uint v = Read(ApicOffset.SpuriousIntVector);
            v &= ~(1u << 8);
            if (enabled)
                v |= 1u << 8;
            Write(ApicOffset.SpuriousIntVector, v);
        }

        [NoHeapAllocation]
        public bool GetEnabled()
        {
            return (Read(ApicOffset.SpuriousIntVector) & (1u << 8)) != 0;
        }

        [NoHeapAllocation]
        public override void AckIrq(byte irq)
        {
            // XXX should not ack spurious interrupt
            uint interrupt = IrqToInterrupt(irq);
            DebugStub.Assert(IsrIsSet((byte)interrupt));

            Write(ApicOffset.EoiRegister, 0);
        }

        [NoHeapAllocation]
        public override void EnableIrq(byte irq)
        {
#if DEBUG_IO_APIC_IRQ_MASK
            DebugStub.Print("Enabling IRQ 0x{0:x}\n", __arglist(irq));
#endif

            foreach (IoApic ioApic in ioApics)
            {
#if DEBUG_IO_APIC_IRQ_MASK
                DebugStub.Print("Found IoApic 0x{0:x}; interrupt base 0x{1:x}, entry count 0x{2:x}\n",
                    __arglist(ioApic.GetId(), ioApic.InterruptBase, ioApic.RedirectionEntryCount));
#endif

                if ((ioApic.InterruptBase <= irq) &&
                    (irq < (ioApic.InterruptBase + ioApic.RedirectionEntryCount)))
                {
#if DEBUG_IO_APIC_IRQ_MASK
                    DebugStub.Print("Enabling IRQ 0x{0:x} as 0x{1:x} on ioApic 0x{2:x}\n",
                        __arglist(irq, irq - ioApic.InterruptBase, ioApic.GetId()));
#endif
                    ioApic.SetEntryMask(irq - ioApic.InterruptBase, false);
                    break;
                }
            }

#if DEBUG_IO_APIC_IRQ_MASK
            PrintIoApics();
#endif
        }

        [NoHeapAllocation]
        public override void DisableIrq(byte irq)
        {
#if DEBUG_IO_APIC_IRQ_MASK
            DebugStub.Print("Disabling IRQ 0x{0:x}\n", __arglist(irq));
#endif

            foreach (IoApic ioApic in ioApics)
            {
#if DEBUG_IO_APIC_IRQ_MASK
                DebugStub.Print("Found IoApic 0x{0:x}; interrupt base 0x{1:x}, entry count 0x{2:x}\n",
                    __arglist(ioApic.GetId(), ioApic.InterruptBase, ioApic.RedirectionEntryCount));
#endif

                if ((ioApic.InterruptBase <= irq) &&
                    (irq < (ioApic.InterruptBase + ioApic.RedirectionEntryCount)))
                {
#if DEBUG_IO_APIC_IRQ_MASK
                    DebugStub.Print("Disabling IRQ 0x{0:x} as 0x{1:x} on ioApic 0x{2:x}\n",
                        __arglist(irq, irq - ioApic.InterruptBase, ioApic.GetId()));
#endif
                    ioApic.SetEntryMask(irq - ioApic.InterruptBase, true);
                    break;
                }
            }

#if DEBUG_IO_APIC_IRQ_MASK
            PrintIoApics();
#endif
        }

        [NoHeapAllocation]
        public override void ClearInterrupt(byte interrupt)
        {
            byte irq = InterruptToIrq(interrupt);
            Tracing.Log(Tracing.Debug, "Clearing interrupt {0} (irq {1})",
                        (UIntPtr)interrupt, (UIntPtr)irq);
            //            byte isrInterrupt = (byte) ActiveIsrInterrupt();
            if (interrupt >= baseVector) {
                //                DebugStub.Assert(interrupt == isrInterrupt);
                DisableIrq(irq);
            } else {
                DebugStub.Break();
            }
            AckIrq(irq);
        }

        [NoHeapAllocation]
        private bool SendIPI(uint icrHi, uint icrLo)
        {
            //
            // DebugStub.Print is not permitted here.  We may be
            // invoked from within DebugStub.Trap with the
            // non-recursive communication lock held.
            //
            Tracing.Log(Tracing.Audit,
                        "Sending IPI {0:x8}{1:x8}\n", icrHi, icrLo);

            icrLo &= ~IcrFlags.Pending;

            // Clear ESR
            Write(ApicOffset.ErrorStatus, 0);
            Write(ApicOffset.ErrorStatus, 0);

            // Send IPI
            Write(ApicOffset.IcrHi, icrHi);
            Write(ApicOffset.IcrLo, icrLo);

            do {
                Write(ApicOffset.ErrorStatus, 0);        // Trigger ESR update
                uint esr = Read(ApicOffset.ErrorStatus);
                if (esr != 0) {
                    Tracing.Log(Tracing.Warning,
                                "APIC SendIPI Error (esr = {0})\n", esr);
                    return false;
                }
            } while ((Read(ApicOffset.IcrLo) & IcrFlags.Pending) != 0);
            return true;
        }

        [NoHeapAllocation]
        private static void Delay(uint micros)
        {
            HalDevicesApic.StallProcessor(micros);
        }

        [NoHeapAllocation]
        internal void BroadcastStartupIPI(byte vector)
        {
            Write(ApicOffset.IcrHi, 0);

            // Per AP initialization in IA-32 Vol 3
            // Init IPI     // ICR.Lo = 00c4500h
            SendIPI(0, IcrFlags.AllBarSelf | IcrFlags.Assert | IcrFlags.INIT | (uint)vector);

            // ...delay 10ms
            Delay(10000);

            // Startup IPI  // ICR.Lo = 00c46XXh
            SendIPI(0, IcrFlags.AllBarSelf | IcrFlags.Assert | IcrFlags.StartUp | (uint)vector);

            // ...delay 200us
            Delay(200);
            SendIPI(0, IcrFlags.AllBarSelf | IcrFlags.Assert | IcrFlags.StartUp | (uint)vector);
        }

        //Version of the startup IPI which does not use boradcast.
        internal void SendSingleStartupIPI(uint to, byte vector)
        {
            Write(ApicOffset.IcrHi, 0);

            // Per AP initialization in IA-32 Vol 3
            // Init IPI     // ICR.Lo = 00c4500h
            SendIPI((((uint)to & 0x0ff) << 24), IcrFlags.NoShortHand | IcrFlags.Assert | IcrFlags.INIT  | IcrFlags.Physical | (uint)vector);

            // ...delay 10ms
            Delay(10000);

            // Startup IPI  // ICR.Lo = 00c46XXh
            SendIPI((((uint)to & 0x0ff) << 24), IcrFlags.NoShortHand | IcrFlags.Assert | IcrFlags.StartUp  | IcrFlags.Physical | (uint)vector);

            // ...delay 200us
            Delay(200);
            SendIPI((((uint)to & 0x0ff) << 24), IcrFlags.NoShortHand | IcrFlags.Assert | IcrFlags.StartUp  | IcrFlags.Physical | (uint)vector);
        }

        [NoHeapAllocation]
        internal void BroadcastFreezeIPI()
        {
            unsafe {
                Microsoft.Singularity.Hal.Platform p = Microsoft.Singularity.Hal.Platform.ThePlatform;
                int  cpuId = p.ApicId;

                for (uint i = 0; i < Processor.GetProcessorCount(); i++) {
                    uint to = i;
                    if (to != cpuId) {
                        Write(ApicOffset.IcrHi, 0);
                        SendIPI((((uint)to & 0x0ff) << 24),
                                IcrFlags.NoShortHand | IcrFlags.Assert |
                                IcrFlags.NMI  | IcrFlags.Physical);
                    }
                }
            }
        }

        //
        // This allows us to reset AP processors to ensure they do not
        // wakeup on us and do damage as a result of a debug NMI during
        // shutdown/warmboot.
        //
        [NoHeapAllocation]
        internal void BroadcastResetIPI()
        {

            Write(ApicOffset.IcrHi, 0);

            //
            // This will cause the CPU to reset, flush all internal state, and
            // start back up again in real mode, and wait in the BIOS for further
            // startup commands. The BIOS is the system ROM and the CPU is no longer
            // going to execute any of our system code.
            //
            SendIPI(0, IcrFlags.AllBarSelf | IcrFlags.Assert | IcrFlags.INIT | (uint)0);
        }

        [NoHeapAllocation]
        internal void SendFixedIPI(byte vector, int from, int to)
        {
#if DEBUG_FIXED_IPI
            DebugStub.WriteLine("SendFixedIPI vec={0} cpu{1} to cpu{2}\n",
                                __arglist(vector, from, to));
#endif // DEBUG_FIXED_IPI

            uint icrHi = ((uint)to & 0x0ff) << 24;
            uint icrLo =
                IcrFlags.NoShortHand | IcrFlags.Assert |
                IcrFlags.Fixed  |
                IcrFlags.Physical    | (uint)vector;

            Write(ApicOffset.IcrHi, 0);

            if (!SendIPI(icrHi, icrLo)) {
                DebugStub.Break();
            }
        }

        [NoHeapAllocation]
        internal void BroadcastFixedIPI(byte vector, bool includeSelf)
        {
            uint icrHi = 0;
            uint icrLo = includeSelf ? IcrFlags.All : IcrFlags.AllBarSelf;
            icrLo |= (IcrFlags.Assert | IcrFlags.Fixed |
                      (uint)vector);

            Write(ApicOffset.IcrHi, 0);

            if (!SendIPI(icrHi, icrLo)) {
                DebugStub.Break();
            }
        }

        [NoHeapAllocation]
        internal void ClearFixedIPI(int interrupt)
        {
            DebugStub.Assert(IsrIsSet((byte)interrupt));
            Write(ApicOffset.EoiRegister, 0);
        }

        [NoHeapAllocation]
        private bool IrrIsSet(byte interrupt)
        {
            // Read() is 4 bytes wide.
            // Each DWORD is aligned on 16-byte boundaries.
            //    IsrBase + 0x00 = interrupts   0-31
            //    IsrBase + 0x10 = interrupts  32-63
            //    IsrBase + 0x20 = interrupts  64-95
            //    ...
            //    IsrBase + 0x70 = interrupts 224-255
            uint d = (uint)interrupt / 32u;
            uint o = ApicOffset.IrrBase + d * 16u;
            uint m = 1u << (int) ((int)interrupt - d * 32);
            return (Read(o) & m) == m;
        }

        [NoHeapAllocation]
        private bool IsrIsSet(byte interrupt)
        {
            // Read() is 4 bytes wide.
            // Each DWORD is aligned on 16-byte boundaries.
            //    IsrBase + 0x00 = interrupts   0-31
            //    IsrBase + 0x10 = interrupts  32-63
            //    IsrBase + 0x20 = interrupts  64-95
            //    ...
            //    IsrBase + 0x70 = interrupts 224-255
            uint d = (uint)interrupt / 32u;
            uint o = ApicOffset.IsrBase + d * 16u;
            uint m = 1u << (int) ((int)interrupt - d * 32);
            return (Read(o) & m) == m;
        }

        [NoHeapAllocation]
        private uint Log2(uint value)
        {
            uint l = 0;
            if ((value & 0xffff0000u) != 0) l += 16u;
            if ((value & 0xff00ff00u) != 0) l += 8u;
            if ((value & 0xf0f0f0f0u) != 0) l += 4u;
            if ((value & 0xccccccccu) != 0) l += 2u;
            if ((value & 0xaaaaaaaau) != 0) l += 1u;
            return l;
        }

        private uint lastByte;
        private int  lastByteValue;
        private uint lastIsr;

        [NoHeapAllocation]
        private uint ActiveIsrInterrupt()
        {
            uint isr = ~0u;
            uint i;
            for (i = 0; i < 0x80; i += 0x10) {
                uint value = Read(ApicOffset.IsrBase + i);
                if (value != 0) {
                    lastByteValue = (int) value;
                    lastByte = i;
                    DebugStub.Assert((value & (value - 1)) == 0);
                    isr = i * 2 + Log2(value);
                    lastIsr = isr;
                    break;
                }
            }
            i += 0x10;
            for (; i < 0x80; i += 0x10) {
                uint value = Read(ApicOffset.IsrBase + i);
                DebugStub.Assert(value == 0);
            }
            DebugStub.Assert(isr != ~0u);
            return isr;
        }

        [Conditional("DEBUG_APIC")]
        [NoHeapAllocation]
        internal void DumpState()
        {
            ulong msr      = Isa.ReadMsr(0x1b);
            uint  baseAddr = ((uint) msr) & 0xfffff000u;
            uint  en       = (((uint) msr) >> 11) & 0x1;
            uint  bsp      = (((uint) msr) >>  8) & 0x1;

            DebugStub.Print("Apic Base {0:x8} MSR Enabled {1} BSP {2}\n",
                            __arglist(baseAddr, en, bsp));

            DebugStub.Print("Id {0:x} Version {1:x} TaskPriority {2:x} " +
                            "ArbitrationPriority {3:x} ProcessorPriority {4:x}\n",
                            __arglist(
                                Read(ApicOffset.Id),
                                Read(ApicOffset.Version),
                                Read(ApicOffset.TaskPriority),
                                Read(ApicOffset.ArbitrationPriority),
                                Read(ApicOffset.ProcessorPriority)));

            DebugStub.Print("Timer LVT        {0:x8}  Thermal LVT      {1:x8}  " +
                            "PerfCounts LVT   {2:x8}\n",
                            __arglist(
                                Read(ApicOffset.LvtTimer),
                                Read(ApicOffset.LvtThermalSensor),
                                Read(ApicOffset.LvtPerfCounts)));

            DebugStub.Print("Lint0 LVT        {0:x8}  Lint1 LVT        {1:x8}\n",
                            __arglist(
                                Read(ApicOffset.LvtLint0),
                                Read(ApicOffset.LvtLint1)));

            DebugStub.Print("LvtError LVT     {0:x8}  Spurious LVT     {1:x8}  ESR {2:x2}\n",
                            __arglist(
                                Read(ApicOffset.LvtError),
                                Read(ApicOffset.SpuriousIntVector),
                                Read(ApicOffset.ErrorStatus) & 0xef));
        }

        // print IRR and ISR register
#if FALSE
        // This method is commented out because
        // it allocates memory.  The fix is trivial.
        internal void PrintIrrAndIsr(bool debug)
        {
            uint addr, a;
            uint [] c = new uint [8];
            uint [] b = new uint [8];

            if (debug) {
                DebugStub.Print("HSG: IRR  ");
                for (int i = 0; i < 8; i++) {
                    addr = ApicOffset.IrrBase+(uint)(i*32);
                    a = Read(addr);
                    DebugStub.Print("{0}.{1:x08}  ", __arglist(i,a));
                }
                DebugStub.WriteLine("");
                DebugStub.Print("HSG: ISR  ");
                for (int i = 0; i < 8; i++) {
                    addr = ApicOffset.IsrBase+(uint)(i*32);
                    a = Read(addr);
                    DebugStub.Print("{0}.{1:x08}  ", __arglist(i,a));
                }
                DebugStub.WriteLine("");
            }


            for (int i = 0; i < 8; i++) {
                addr = ApicOffset.IrrBase+(uint)(i*32);
                c[i] = Read(addr);
            }
            for (int i = 0; i < 8; i++) {
                addr = ApicOffset.IsrBase+(uint)(i*32);
                b[i] = Read(addr);
            }

            Tracing.Log(Tracing.Debug, "************************************");
            Tracing.Log(Tracing.Debug, "IRR lo: {0:x08} {1:x08} {2:x08} {3:x08}",
                        c[0], c[1], c[2], c[3]);
            Tracing.Log(Tracing.Debug, "IRR hi: {0:x08} {1:x08} {2:x08} {3:x08}",
                        c[4], c[5], c[6], c[7]);
            Tracing.Log(Tracing.Debug, "ISR lo: {0:x08} {1:x08} {2:x08} {3:x08}",
                        b[0], b[1], b[2], b[3]);
            Tracing.Log(Tracing.Debug, "ISRb hi: {0:x08} {1:x08} {2:x08} {3:x08}",
                        b[4], b[5], b[6], b[7]);

        }
#endif // FALSE
    }
}
