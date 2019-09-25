///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MpResources.cs
//
//  Note:
//    Intel MP Specification 1.4


namespace Microsoft.Singularity.Hal
{
    using Microsoft.Singularity.Io;
    using Microsoft.Singularity;
    using Microsoft.Singularity.Hal;
    using System;
    using System.Collections;
    using System.Diagnostics;

    [CLSCompliant(false)]
    internal class MpFloatingPointer
    {
        private const uint Signature = 0x5f504d5f;

        internal uint ConfTableBase;
        internal byte Revision;
        internal byte [] Feature;

        internal byte ConfigurationType
        {
            get { return Feature[0]; }
        }

        internal bool MpConfTablePresent
        {
            get { return Feature[0] == 0; }
        }

        internal bool ImcrPresent
        {
            get { return (Feature[1] & 0x80) != 0; }
        }

        internal bool MultipleClockSources
        {
            get { return (Feature[1] & 0x40) != 0; }
        }

        internal static MpFloatingPointer Parse(IoMemory region)
        {
            uint signature = region.Read32(0);
            if (signature != Signature) {
                return null;
            }

            int length = region.Read8(8) * 16;
            if (length != 16) {
                return null;
            }

            byte checksum = 0;
            for (int i = 0; i < length; i++) {
                checksum += region.Read8((int) i);
            }

            if (checksum != 0) {
                return null;
            }

            MpFloatingPointer m = new MpFloatingPointer();
            m.ConfTableBase = region.Read32(4);
            m.Revision      = region.Read8(9);
            m.Feature       = new byte [5];
            for (int i = 0; i < m.Feature.Length; i++) {
                m.Feature[i] = region.Read8(0xb + i);
            }

            return m;
        }
    }

    [CLSCompliant(false)]
    internal class MpConfTable
    {
        private const uint Signature   = 0x504d4350;
        private const uint FixedLength = 0x2c;

        internal ushort BaseTableLength;
        internal byte   Revision;
        internal uint   OemTableBase;
        internal ushort OemTableSize;
        internal ushort EntryCount;
        internal uint   LocalApicBase;
        internal ushort ExtendedTableLength;
        internal byte   ExtendedTableChecksum;
        internal string OemId;
        internal string ProductId;

        internal static MpConfTable Parse(IoMemory region)
        {
            if (region.Read32(0) != Signature) {
                return null;
            }

            int  length = region.Read16(4);
            DebugStub.Print("MP Conf Table length {0}\n", __arglist(length));

#if NOTYET
            byte checksum = 0;
            for (int i = 0; i < length; i++) {
                checksum += region.Read8(i);
            }

            if (checksum != 0) {
                return null;
            }
#endif

            MpConfTable confTable = new MpConfTable();
            confTable.BaseTableLength       = region.Read16(4);
            confTable.Revision              = region.Read8(7);
            confTable.OemTableBase          = region.Read32(0x1c);
            confTable.OemTableSize          = region.Read16(0x20);
            confTable.EntryCount            = region.Read16(0x22);
            confTable.LocalApicBase         = region.Read32(0x24);
            confTable.ExtendedTableLength   = region.Read16(0x28);
            confTable.ExtendedTableChecksum = region.Read8(0x2a);
            confTable.OemId     = region.ReadAsciiZeroString(8, 8);
            confTable.ProductId = region.ReadAsciiZeroString(0x10, 0x0c);
            return confTable;
        }
    }

    [CLSCompliant(false)]
    internal class MpProcessorEntry
    {
        internal const byte EntryType = 0x00;
        internal const int  Length    = 0x14;

        internal byte LocalApicId;
        internal byte LocalApicVersion;
        internal byte CpuFlags;
        internal uint CpuSignature;
        internal uint FeatureFlags;

        internal bool Enabled
        {
            get { return (CpuFlags & 0x01) != 0; }
        }

        internal bool BootStrapProcessor
        {
            get { return (CpuFlags & 0x02) != 0; }
        }

        [Conditional("MP_TABLE_DEBUG")]
        internal void DebugPrint()
        {
            DebugStub.Print("CPU Apic Id {0:x2} Version {1:x2} CpuFlags {2:x2} " +
                            "Signature {3:x8} Features {4:x8}\n",
                            __arglist(
                                LocalApicId,
                                LocalApicVersion,
                                CpuFlags,
                                CpuSignature,
                                FeatureFlags));
        }

        internal static MpProcessorEntry Parse(IoMemory region,
                                               int      length,
                                               ref int  offset)
        {
            Debug.Assert(length >= offset + Length);
            Debug.Assert(region.Read8(offset + 0) == EntryType);

            MpProcessorEntry e = new MpProcessorEntry();
            e.LocalApicId      = region.Read8(offset + 1);
            e.LocalApicVersion = region.Read8(offset + 2);
            e.CpuFlags         = region.Read8(offset + 3);
            e.CpuSignature     = region.Read32(offset + 4);
            e.FeatureFlags     = region.Read32(offset + 8);
            e.DebugPrint();
            offset += Length;
            return e;
        }
    }

    internal enum BusType : byte
    {
        CBUS    = 0,
        CBUSII  = 1,
        EISA    = 2,
        FUTURE  = 3,
        INTERN  = 4,
        ISA     = 5,
        MBI     = 6,
        MBII    = 7,
        MCA     = 8,
        MPI     = 9,
        MPSA    = 10,
        NUBUS   = 11,
        PCI     = 12,
        PCMCIA  = 13,
        TC      = 14,
        VL      = 15,
        VME     = 16,
        XPRESS  = 17,
        LAST    = 17,
        UNKNOWN = 255,
    }

    [CLSCompliant(false)]
    internal class MpBusEntry
    {
        internal const byte EntryType = 0x01;
        internal const int  Length    = 0x08;

        // Bus type names 1-1 correspondence with BusType enum.
        private static string [] busNames = new string [(int)BusType.LAST + 1]
        {
            "CBUS  ", "CBUSII", "EISA  ", "FUTURE", "INTERN", "ISA   ",
            "MBI   ", "MBII  ", "MCA   ", "MPI   ", "MPSA  ", "NUBUS ",
            "PCI   ", "PCMCIA", "TC    ", "VL    ", "VME   ", "XPRESS"
        };

        internal byte    BusId;
        internal BusType BusType;

        [Conditional("MP_TABLE_DEBUG")]
        internal void DebugPrint()
        {
            DebugStub.Print("BusId {0:x2} BusType {1:x2}\n", __arglist(BusId, BusName));
        }

        internal string BusName
        {
            get
            {
                if (BusType == BusType.UNKNOWN) {
                    return "UNKNOWN";
                }
                return busNames[(int)BusType];
            }
        }

        internal static MpBusEntry Parse(IoMemory region,
                                         int      length,
                                         ref int  offset)
        {
            Debug.Assert(length >= offset + Length);
            Debug.Assert(region.Read8(offset + 0) == EntryType);

            MpBusEntry e = new MpBusEntry();
            e.BusId      = region.Read8(offset + 1);
            e.BusType    = BusType.UNKNOWN;

            string name = region.ReadAsciiZeroString(offset + 2, 6);
            e.BusType = BusType.UNKNOWN;

            for (int i = 0; i <= (int)BusType.LAST; i++) {
                if (name == busNames[i]) {
                    e.BusType = (BusType)i;
                    break;
                }
            }

            e.DebugPrint();
            offset += Length;
            return e;
        }
    }

    [CLSCompliant(false)]
    internal class MpIoApicEntry
    {
        internal const byte EntryType = 0x02;
        internal const int Length     = 0x08;

        internal byte Id;
        internal byte Version;
        internal byte Flags;
        internal uint BaseAddress;

        internal bool Enabled { get { return (Flags & 0x01) == 0x01; } }

        [Conditional("MP_TABLE_DEBUG")]
        internal void DebugPrint()
        {
            DebugStub.Print("Id {0:x2} Version {1:x2} Flags {2:x2} BaseAddress {3:x8}\n",
                            __arglist(Id, Version, Flags, BaseAddress));
        }

        internal static MpIoApicEntry Parse(IoMemory region,
                                            int      length,
                                            ref int  offset)
        {
            Debug.Assert(length >= offset + Length);
            Debug.Assert(region.Read8(offset + 0) == EntryType);

            MpIoApicEntry e = new MpIoApicEntry();
            e.Id          = region.Read8(offset + 1);
            e.Version     = region.Read8(offset + 2);
            e.Flags       = region.Read8(offset + 3);
            e.BaseAddress = region.Read32(offset + 4);
            e.DebugPrint();
            offset += Length;
            return e;
        }
    }

    internal enum InterruptType : byte
    {
        INT    = 0,
        NMI    = 1,
        SMI    = 2,
        ExtINT = 3,
    }

    internal enum Polarity : ushort
    {
        Bus        = 0,
        ActiveHigh = 1,
        Reserved   = 2,
        ActiveLow  = 3,
    }

    internal enum Trigger : ushort
    {
        Bus      = 0,
        Edge     = 4,
        Reserved = 8,
        Level    = 12,
    }

    [CLSCompliant(false)]
    internal class MpInterruptEntry
    {
        internal const byte IoEntryType    = 0x03;
        internal const byte LocalEntryType = 0x04;
        internal const int  Length         = 0x08;

        internal byte   EntryType;
        internal byte   Interrupt;
        internal ushort Flags;
        internal byte   BusId;
        internal byte   BusIrq;
        internal byte   ApicId;
        internal byte   ApicLine;

        internal bool ApicRedirect
        {
            get { return Interrupt == (byte)InterruptType.INT; }
        }

        internal Polarity PolarityType
        {
            get { return (Polarity) (Flags & 0x3); }
        }

        internal Trigger TriggerType
        {
            get { return (Trigger) (Flags & 0xc); }
        }

        [Conditional("MP_TABLE_DEBUG")]
        internal void DebugPrint()
        {
            DebugStub.Print("{0} Interrupt {1:x2} Flags {2:x4} BusId {3:x2} " +
                            "BusIrq {4:x2} ApicId {5:x2} ApicLine {6:x2}\n",
                            __arglist(
                                EntryType == IoEntryType ? "Io" : "Local",
                                Interrupt,
                                Flags,
                                BusId,
                                BusIrq,
                                ApicId,
                                ApicLine));
        }

        internal static MpInterruptEntry Parse(IoMemory region,
                                             int      length,
                                             ref int  offset)
        {
            Debug.Assert(length >= offset + Length);
            byte entry = region.Read8(offset + 0);
            Debug.Assert(entry == IoEntryType || entry == LocalEntryType);

            MpInterruptEntry e = new MpInterruptEntry();
            e.EntryType = entry;
            e.Interrupt = region.Read8(offset + 1);
            e.Flags     = region.Read16(offset + 2);
            e.BusId     = region.Read8(offset + 4);
            e.BusIrq    = region.Read8(offset + 5);
            e.ApicId    = region.Read8(offset + 6);
            e.ApicLine  = region.Read8(offset + 7);
            e.DebugPrint();
            offset += Length;
            return e;
        }
    }

    [CLSCompliant(false)]
    internal class MpResources
    {
        static IoMemory mpFloatRegion;
        static IoMemory mpConfTableRegion;

        internal static MpFloatingPointer FloatingPointer;
        internal static MpConfTable       ConfTable;

        internal static ArrayList ProcessorEntries;
        internal static ArrayList BusEntries;
        internal static ArrayList IoApicEntries;
        internal static ArrayList IoInterruptEntries;
        internal static ArrayList LocalInterruptEntries;

        internal static void Parse(IoMemory region,
                                 int      length,
                                 uint     entryCount)
        {
            int offset = 0;
            for (int i = 0; i < entryCount; i++) {
                switch (region.Read8(offset)) {
                    case MpProcessorEntry.EntryType:
                        ProcessorEntries.Add(
                            MpProcessorEntry.Parse(region, length, ref offset)
                            );
                        break;
                    case MpBusEntry.EntryType:
                        BusEntries.Add(
                            MpBusEntry.Parse(region, length, ref offset)
                            );
                        break;
                    case MpIoApicEntry.EntryType:
                        IoApicEntries.Add(
                            MpIoApicEntry.Parse(region, length, ref offset)
                            );
                        break;
                    case MpInterruptEntry.IoEntryType:
                        IoInterruptEntries.Add(
                            MpInterruptEntry.Parse(region, length, ref offset)
                            );
                        break;
                    case MpInterruptEntry.LocalEntryType:
                        LocalInterruptEntries.Add(
                            MpInterruptEntry.Parse(region, length, ref offset)
                            );
                        break;
                }
            }
        }

        private static UIntPtr GetMpFloatBase()
        {
            unsafe
              {
                return new UIntPtr (Platform.ThePlatform.MpFloat32);
            }
        }

        internal static MpBusEntry GetBusEntryById(byte id)
        {
            foreach (MpBusEntry be in BusEntries) {
                if (be.BusId == id) {
                    return be;
                }
            }
            return null;
        }

        internal static void ParseMpTables()
        {
            UIntPtr mpFloat = GetMpFloatBase();
            if (mpFloat == UIntPtr.Zero) {
                DebugStub.Print("MP Floating Pointer Structure not found.\n");
                return;
            }

            mpFloatRegion =
                IoMemory.MapPhysicalMemory(mpFloat, new UIntPtr(16), true, false);

            FloatingPointer = MpFloatingPointer.Parse(mpFloatRegion);
            if (FloatingPointer == null) {
                DebugStub.Print("Failed to parse MP Floating Pointer " +
                                "Structure.\n");
                return;
            }

            if (FloatingPointer.MpConfTablePresent) {
                mpConfTableRegion = IoMemory.MapPhysicalMemory(
                    new UIntPtr(FloatingPointer.ConfTableBase),
                    new UIntPtr(0x2c), true, false);

                DebugStub.Print("Found MP Conf Table\n");

                ConfTable = MpConfTable.Parse(mpConfTableRegion);
                if (ConfTable == null) {
                    DebugStub.Print("Failed to parse MP Configuration table.\n");
                }

                IoMemory mpResourceRegion =
                    IoMemory.MapPhysicalMemory(
                        new UIntPtr(FloatingPointer.ConfTableBase + 0x2c),
                        new UIntPtr(ConfTable.BaseTableLength - 0x2c),
                        true, false);
                DebugStub.Print("Parsing MP Conf Table Resources\n");
                MpResources.Parse(mpResourceRegion,
                                  ConfTable.BaseTableLength - 0x2c,
                                  ConfTable.EntryCount);
            }
            else {
                DebugStub.Print("MP Configuration table not present.\n");
                DebugStub.Print("MP Floating Pointer features: " +
                                "{0:x8} {1:x8} {2:x8} {3:x8} {4:x8}\n",
                                __arglist(
                                    FloatingPointer.Feature[0],
                                    FloatingPointer.Feature[1],
                                    FloatingPointer.Feature[2],
                                    FloatingPointer.Feature[3],
                                    FloatingPointer.Feature[4]));
            }
        }

        static MpResources()
        {
            ProcessorEntries      = new ArrayList();
            BusEntries            = new ArrayList();
            IoApicEntries         = new ArrayList();
            IoInterruptEntries    = new ArrayList();
            LocalInterruptEntries = new ArrayList();
        }
    }
}
