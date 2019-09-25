///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoApic.cs
//
//  Note:
//    Intel MP Specification 1.4
//    82093AA I/O Advanced Programmable Interrupt Controller

namespace Microsoft.Singularity.Hal
{
    using System;
    using System.Collections;
    using System.Diagnostics;
    using System.Runtime.CompilerServices;
    using System.Threading;

    using Microsoft.Singularity.Io;
    using Microsoft.Singularity.Hal.Acpi;

    public enum IoBits : ushort
    {
        IrqMask          = 0x0100,
        TriggerModeMask  = 0x0080,
            TriggerModeLevel = TriggerModeMask,
            TriggerModeEdge  = 0,
        RemoteIRR        = 0x0040,
        IntPolMask       = 0x0020,
            IntPolActiveLow  = IntPolMask,
            IntPolActiveHigh = 0,
        DeliveryStatus   = 0x0010,
        DstMask          = 0x0008,         // Destination Mask
            DstLogical       = DstMask,
            DstPhysical      = 0,
        DelModMask       = 0x0007,         // Delivery Mode Mask
            DelModFixed      = 0x0000,
            DelModLowest     = 0x0001,
            DelModSMI        = 0x0002,
            DelModReserved1  = 0x0003,
            DelModNMI        = 0x0004,
            DelModINIT       = 0x0005,
            DelModReserved2  = 0x0006,
            DelModExtINT     = 0x0007,
    };

    [CLSCompliant(false)]
    public struct RedirectionEntry
    {
        public byte        Destination;
        public IoBits      IoBits;
        public byte        InterruptVector;

        [NoHeapAllocation]
        public RedirectionEntry(byte   destination,
                                IoBits ioBits,
                                byte   interruptVector)
        {
            this.Destination     = destination;
            this.IoBits          = ioBits;
            this.InterruptVector = interruptVector;
        }

        [NoHeapAllocation]
        public RedirectionEntry(byte        destination,
                                ushort      ioBits,
                                byte        interruptVector)
        {
            this.Destination     = destination;
            this.IoBits          = (IoBits)ioBits;
            this.InterruptVector = interruptVector;
        }
    }

    [CLSCompliant(false)]
    public class IoApic
    {
        private const uint MaskBit   = 1 << 16;
        private const uint RedHiBase = 0x11;
        private const uint RedLoBase = 0x10;
        private const uint IdLimit   = 0x0f;
        private const uint IndexLimit = 24;
        private const uint RegisterLimit = 0x3f;

        IoMemory ioRegSel;
        IoMemory ioWin;
        uint     entries;
        uint     interruptBase;

        SpinLock ioLock;

        public IoApic(UIntPtr memoryBase, uint interruptBase)
        {
            ioRegSel = IoMemory.MapPhysicalMemory(memoryBase,
                                                  new UIntPtr(4u), true, true);
            ioWin    = IoMemory.MapPhysicalMemory(memoryBase + new UIntPtr(0x10u),
                                                  new UIntPtr(4u), true, true);
            entries = ((ReadRegister(1) & 0xff0000u) >> 16) + 1;

            for (uint i = 0; i < entries; i++) {
                SetEntryMask(i, true);
            }

            ioLock = new SpinLock(SpinLock.Types.IoApic);

            this.interruptBase = interruptBase;
        }

        [NoHeapAllocation]
        private bool AcquireLock()
        {
            bool irqRestore = Processor.DisableInterrupts();
#if SINGULARITY_MP
            this.ioLock.Acquire();
#endif // SINGULARITY_MP
            return irqRestore;
        }

        [NoHeapAllocation]
        private void ReleaseLock(bool irqRestore)
        {
#if SINGULARITY_MP
            this.ioLock.Release();
#endif // SINGULARITY_MP
            Processor.RestoreInterrupts(irqRestore);
        }

        [ Conditional("DEBUG_APIC") ]
        [NoHeapAllocation]
        [HalLock]
        internal void DumpRedirectionEntries()
        {
            bool enabled = AcquireLock();
            try {
                for (uint i = 0; i < entries; i++) {
                    uint hi = ReadRegister(RedHiBase + i * 2);
                    uint lo = ReadRegister(RedLoBase + i * 2);
                    Tracing.Log(Tracing.Debug,
                                "IoApic Entry {0:x2} {1:x8} {2:x8}",
                                i, hi, lo);
                }
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        [NoHeapAllocation]
        private void RangeCheck(uint value, uint max, string name)
        {
            if (value > max) {
                DebugStub.Break();
            }
        }

        [NoHeapAllocation]
        private uint ReadRegister(uint offset)
        {
            RangeCheck(offset, RegisterLimit, "offset");
            DebugStub.Assert(Processor.InterruptsDisabled());

            IoResult result = ioRegSel.Write32NoThrow(0, offset);
            DebugStub.Assert(IoResult.Success == result);

            uint outValue;
            result = ioWin.Read32NoThrow((byte)0, out outValue);
            DebugStub.Assert(IoResult.Success == result);
            return outValue;
        }

        [NoHeapAllocation]
        private void WriteRegister(uint offset, uint value)
        {
            RangeCheck(offset, RegisterLimit, "offset");
            DebugStub.Assert(Processor.InterruptsDisabled());

            IoResult result = ioRegSel.Write32NoThrow(0, offset);
            DebugStub.Assert(IoResult.Success == result);

            result = ioWin.Write32NoThrow((byte)0, value);
            DebugStub.Assert(IoResult.Success == result);
        }

        [NoHeapAllocation][HalLock]
        public byte GetId()
        {
            bool enabled = AcquireLock();
            try {
                return (byte)((ReadRegister(0) & 0x0f000000u) >> 24);
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        [NoHeapAllocation][HalLock]
        public void SetId(byte id)
        {
            bool enabled = AcquireLock();
            try {
                RangeCheck(id, IdLimit, "id");
                uint reserved = ReadRegister(0) & 0xf0ffffffu;
                WriteRegister(0, reserved | ((uint)id << 24));
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        [NoHeapAllocation][HalLock]
        public byte GetVersion()
        {
            bool enabled = AcquireLock();
            try {
                return (byte)ReadRegister(1);
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        [NoHeapAllocation][HalLock]
        public byte GetArbitrationId()
        {
            bool enabled = AcquireLock();
            try {
                return (byte)((ReadRegister(2) & 0x0f000000u) >> 24);
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        [NoHeapAllocation][HalLock]
        public void SetArbitrationId(byte id)
        {
            RangeCheck(id, IdLimit, "id");

            bool enabled = AcquireLock();
            try {
                uint reserved = ReadRegister(0) & 0xf0ffffffu;
                WriteRegister(2, reserved | ((uint)id << 24));
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        public uint RedirectionEntryCount
        {
            [NoHeapAllocation]
            get { return entries; }
        }

        public uint InterruptBase
        {
            [NoHeapAllocation]
            get { return interruptBase; }
        }

        [NoHeapAllocation][HalLock]
        public RedirectionEntry GetRedirectionEntry(uint index)
        {
            bool enabled = AcquireLock();
            try {
                RangeCheck(index, IndexLimit, "offset");

                uint hi = ReadRegister(RedHiBase + index * 2);
                uint lo = ReadRegister(RedLoBase + index * 2);

                return new RedirectionEntry((byte) (hi >> 24),
                                            (ushort) ((lo >> 8) & 0x1ff),
                                            (byte) (lo & 0xff));
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        [NoHeapAllocation][HalLock]
        public void SetRedirectionEntry(uint index, ref RedirectionEntry entry)
        {
            bool enabled = AcquireLock();
            try {
                RangeCheck(index, IndexLimit, "offset");
                WriteRegister(RedLoBase + index * 2, MaskBit);

                uint hi = ReadRegister(RedHiBase + index * 2) & 0xffffffu;
                hi |= ((uint)entry.Destination) << 24;
                WriteRegister(RedHiBase + index * 2, hi);

                uint lo = ReadRegister(RedLoBase + index * 2) & 0x1ffffu;
                lo |= ((uint)entry.IoBits) << 8;
                lo |= (uint)entry.InterruptVector;
                WriteRegister(RedLoBase + index * 2, lo);
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        [NoHeapAllocation][HalLock]
        public void SetEntryMask(uint index, bool masked)
        {
            bool enabled = AcquireLock();
            try {
                uint lo = ReadRegister(RedLoBase + index * 2) & ~MaskBit;
                if (masked) {
                    lo |= MaskBit;
                }
                WriteRegister(RedLoBase + index * 2, lo);
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        [NoHeapAllocation][HalLock]
        public bool GetEntryMask(uint index)
        {
            bool enabled = AcquireLock();
            try {
                uint lo = ReadRegister(RedLoBase + index * 2) & MaskBit;
                return lo == MaskBit;
            }
            finally {
                ReleaseLock(enabled);
            }
        }

        internal static IoApic [] CreateIOApics()
        {
            // Prefer to get the list of IoApics from the MADT
            Madt madt = AcpiTables.GetMadt();
            if (madt != null) {
                ArrayList alist = madt.GetIoApics();
                if (alist.Count > 0) {
                    IoApic [] apics = new IoApic[alist.Count];
                    for (int i = 0; i < alist.Count; i++) {
                        // Have to convert from a ...Hal.Acpi.IoApic into a Hal.IoApic:
                        Microsoft.Singularity.Hal.Acpi.IoApic sourceEntry = (Microsoft.Singularity.Hal.Acpi.IoApic) alist[i];
                        IoApic destEntry = new IoApic(sourceEntry.Address, sourceEntry.InterruptBase);
                        destEntry.SetId(sourceEntry.Id);
                        apics[i] = destEntry;
                    }
                    DebugStub.Print("Created IoApics from MADT table\n");
                    return apics;
                }
            }
            DebugStub.Print("Created IoApics from MpResources table table\n");
            // Otherwise, create from Mp tables
            return CreateFromMpResources();
        }

        internal static IoApic [] CreateFromMpResources()
        {
            ArrayList ioApicEntries = MpResources.IoApicEntries;

            if (ioApicEntries == null) {
                DebugStub.Print("No I/O APICs found\n");
                return null;
            }

            // Scan IoApic entries and remove those that are marked unusable
            int usable = ioApicEntries.Count;
            foreach (MpIoApicEntry entry in ioApicEntries) {
                if (((int)entry.Flags & 0x1) != 0x1) usable--;
            }

            if (usable == 0) {
                DebugStub.Print("No usable I/O APICs found\n");
                return null;
            }

            IoApic [] apics = new IoApic[usable];
            int i = 0;
            foreach (MpIoApicEntry entry in ioApicEntries) {
                if (((int)entry.Flags & 0x1) != 0x1)
                    continue;

                apics[i] = new IoApic(new UIntPtr(entry.BaseAddress), 0);
                apics[i].SetId(entry.Id);
                i++;
            }
            return apics;
        }
    }

    public class IoApicInspector
    {
        [NoHeapAllocation]
        public static void DescribeModMask(IoBits ioBits)
        {
            ioBits = (IoBits) ((ushort)ioBits & (ushort)IoBits.DelModMask);
            switch (ioBits) {
                case IoBits.DelModFixed:
                    DebugStub.Print("Fixed\n");
                    return;
                case IoBits.DelModLowest:
                    DebugStub.Print("Lowest\n");
                    return;
                case IoBits.DelModSMI:
                    DebugStub.Print("SMI\n");
                    return;
                case IoBits.DelModReserved1:
                    DebugStub.Print("Reserved1\n");
                    return;
                case IoBits.DelModNMI:
                    DebugStub.Print("NMI\n");
                    return;
                case IoBits.DelModINIT:
                    DebugStub.Print("INIT\n");
                    return;
                case IoBits.DelModReserved2:
                    DebugStub.Print("Reserved2\n");
                    return;
                case IoBits.DelModExtINT:
                    DebugStub.Print("ExtINT\n");
                    return;
                default:
                    DebugStub.Print("ERROR\n");
                    return;
            }
        }

        [NoHeapAllocation]
        public static void PrintApic(IoApic ioApic)
        {
            DebugStub.Print("Io Apic\n");
            DebugStub.Print("  Id: {0:x2} Version: {1:x4} ArbitrationId: {2:x2}\n",
                            __arglist(
                                ioApic.GetId(),
                                ioApic.GetVersion(),
                                ioApic.GetArbitrationId()));

            for (uint i = 0; i < ioApic.RedirectionEntryCount; i++) {
                RedirectionEntry e = ioApic.GetRedirectionEntry(i);
                IoBits ib = (IoBits) ((int)e.IoBits & ~(int)IoBits.DelModMask);

                DebugStub.Print("  IoRedTbl[{0:x2}]" +
                                "Dst: {1:x2} IntVec: {2:x2} Control: {3} {4} {5} {6} {7} {8}" +
                                "Delivery Mode ",
                                __arglist(
                                    i,
                                    e.Destination,
                                    e.InterruptVector,
                                    ((ib & IoBits.DstLogical) != 0) ? "Logical" : "Physical",
                                    ((ib & IoBits.IrqMask) != 0) ? "Masked" : "Unmasked",
                                    ((ib & IoBits.TriggerModeMask) != 0) ? "Level" : "Edge",
                                    ((ib & IoBits.RemoteIRR) != 0) ? "Accept" : "Recv",
                                    ((ib & IoBits.IntPolMask) != 0) ? "Hi active" : "Lo active",
                                    ((ib & IoBits.DeliveryStatus) != 0) ? "Pending" : "Idle"));
                DescribeModMask(e.IoBits);
            }
        }
    }
}
