///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   AcpiTables.cs
//
//  Note:
//    Pages of 111-121 ACPI 3.0 Spec.

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using System.Collections;
    using System.Diagnostics;
    using Microsoft.Singularity.Io;

    public struct MadtFlags
    {
        public const uint PCAT_COMPAT_FLAG = 0x01;
    }

    public class Madt
    {
        public const string Signature = "APIC";

        private IoMemory region;
        private SystemTableHeader header;

        uint localApicAddress;
        uint flags;             // Values per MadtFlags

        private Madt(IoMemory region, SystemTableHeader header)
        {
            this.region = region;
            this.header = header;

            localApicAddress = region.Read32(0);
            flags            = region.Read32(4);

            // XXX Just for debugging
            GetLocalApics();
            GetIoApics();
            GetInterruptSourceOverrides();
            GetNmis();
            GetApicNmis();
            GetLocalApicAddressOverrides();
            GetIoSApics();
            GetLocalSApics();
            GetPlatformInterruptSources();
        }


        ///////////////////////////////////////////////////////////////////////
        // Structure and method to get MADT table items generically

        private delegate object ItemCreateDelegate(IoMemory mem, int offset);

        private ArrayList GetStructures(byte typeId,
                                        ItemCreateDelegate createMethod)
        {
            ArrayList l = new ArrayList();

            int offset = 8;
            while (offset < region.Length) {
                if (region.Read8(offset) == typeId) {
                    object entry = createMethod(region, offset);
                    if (entry != null) {
                        l.Add(entry);
                    }
                }
                offset +=  region.Read8(offset + 1);
            }
            return l;
        }


        ///////////////////////////////////////////////////////////////////////
        // Methods to get MADT items of particular types

        public ArrayList GetLocalApics()
        {
            return GetStructures(LocalApic.TypeId,
                                 new ItemCreateDelegate(LocalApic.Create));
        }

        public ArrayList GetIoApics()
        {
            return GetStructures(IoApic.TypeId,
                                 new ItemCreateDelegate(IoApic.Create));
        }

        public ArrayList GetInterruptSourceOverrides()
        {
            return GetStructures(InterruptSourceOverride.TypeId,
                                 new ItemCreateDelegate(InterruptSourceOverride.Create));
        }

        public ArrayList GetNmis()
        {
            return GetStructures(Nmi.TypeId,
                                 new ItemCreateDelegate(Nmi.Create));
        }

        public ArrayList GetApicNmis()
        {
            return GetStructures(ApicNmi.TypeId,
                                 new ItemCreateDelegate(ApicNmi.Create));
        }

        public ArrayList GetLocalApicAddressOverrides()
        {
            return GetStructures(LocalApicAddressOverride.TypeId,
                                 new ItemCreateDelegate(LocalApicAddressOverride.Create));
        }

        public ArrayList GetIoSApics()
        {
            return GetStructures(IoSApic.TypeId,
                                 new ItemCreateDelegate(IoSApic.Create));
        }

        public ArrayList GetLocalSApics()
        {
            return GetStructures(LocalSApic.TypeId,
                                 new ItemCreateDelegate(LocalSApic.Create));
        }

        public ArrayList GetPlatformInterruptSources()
        {
            return GetStructures(PlatformInterruptSource.TypeId,
                                 new ItemCreateDelegate(PlatformInterruptSource.Create));
        }


        ///////////////////////////////////////////////////////////////////////
        //

        internal static Madt Create(SystemTableHeader header)
        {
            IoMemory region = IoMemory.MapPhysicalMemory(header.PostHeaderAddress,
                                                         header.PostHeaderLength,
                                                         true, false);
            int sum = (header.Checksum + AcpiChecksum.Compute(region)) & 0xff;
            if (sum != 0) {
                return null;
            }
            return new Madt(region, header);
        }
    }


    ///////////////////////////////////////////////////////////////////////////
    // MADT APIC Structure Constants

    public struct ApicFlags
    {
        public const uint Enabled = 0x01;
    }

    public struct MpsIntiFlags
    {
        public const ushort PolarityBus        = 0;
        public const ushort PolarityActiveHigh = 1;
        public const ushort PolarityActiveLow  = 3;
        public const ushort PolarityMask       = 3;

        public const ushort TriggerBus         = 0;
        public const ushort TriggerEdge        = 4;
        public const ushort TriggerLevel       = 6;
        public const ushort TriggerMask        = 6;
    }

    public struct PlatformInterruptType
    {
        public const uint PMI                             = 1;
        public const uint INIT                            = 2;
        public const uint CorrectedPlatformErrorInterrupt = 3;
    }

    public struct PlatformInterruptSourceFlags
    {
        public const uint CpeiProcessorOverride = 1;
    }


    ///////////////////////////////////////////////////////////////////////////
    // MADT APIC Structures

    public class LocalApic
    {
        internal const byte TypeId = 0x00;
        internal const byte Length = 8;

        public byte AcpiProcessorId;
        public byte ApicId;
        public uint Flags;              // Values per ApicFlags

        internal LocalApic(IoMemory region, int offset)
        {
            Debug.Assert(region.Read8(offset + 0) == TypeId);
            Debug.Assert(region.Read8(offset + 1) == Length);

            AcpiProcessorId = region.Read8(offset  + 2);
            ApicId          = region.Read8(offset  + 3);
            Flags           = region.Read32(offset + 4);

            // DebugStub.Print("{0:x4}:{1:x4} type {2:x1} AcpiProcId {3:x2} ApicId {4:x2} Flags {5:x8} (LocalApic)\n", __arglist(offset, offset + Length, TypeId, AcpiProcessorId, ApicId, Flags));
        }

        internal static object Create(IoMemory region, int offset)
        {
            LocalApic entry = new LocalApic(region, offset);

            // Only return usable entries
            return ((entry.Flags & 1) == 1
                    ? entry
                    : null);
        }
    }

    public class IoApic
    {
        internal const byte TypeId = 0x01;
        internal const byte Length = 12;

        public byte Id;
        public uint Address;
        public uint InterruptBase;

        internal IoApic(IoMemory region, int offset)
        {
            Debug.Assert(region.Read8(offset + 0) == TypeId);
            Debug.Assert(region.Read8(offset + 1) == Length);

            Id            = region.Read8(offset + 2);
            // reserved   = region.Read8(offset + 3);
            Address       = region.Read32(offset + 4);
            InterruptBase = region.Read32(offset + 8);

            // DebugStub.Print("{0:x4}:{1:x4} type {2:x1} Id {3:x2} Address {4:x8} InterruptBase {5:x8} (IoApic)\n", __arglist(offset, offset + Length, TypeId, Id, Address, InterruptBase));
        }

        internal static object Create(IoMemory region, int offset)
        {
            return new IoApic(region, offset);
        }
    }

    public class InterruptSourceOverride
    {
        internal const byte TypeId = 0x02;
        internal const byte Length = 10;

        public byte   Bus;
        public byte   Source;
        public uint   GlobalSystemInterrupt;
        public ushort Flags;    // Values per MpsIntiFlags

        internal InterruptSourceOverride(IoMemory region, int offset)
        {
            Debug.Assert(region.Read8(offset + 0) == TypeId);
            Debug.Assert(region.Read8(offset + 1) == Length);

            Bus                   = region.Read8(offset + 2);
            Source                = region.Read8(offset + 3);
            GlobalSystemInterrupt = region.Read32(offset + 4);
            Flags                 = region.Read16(offset + 8);

            // DebugStub.Print("{0:x4}:{1:x4} type {2:x1} Bus {3:x2} Source {4:x2} GlobalSystemInterrupt {5:x8} Flags {6:x2} (InterruptSourceOverride)\n", __arglist(offset, offset + Length, TypeId, Bus, Source, GlobalSystemInterrupt, Flags));
        }

        internal static object Create(IoMemory region, int offset)
        {
            return new InterruptSourceOverride(region, offset);
        }
    }

    public class Nmi
    {
        internal const byte TypeId = 0x03;
        internal const byte Length = 8;

        public ushort Flags;    // Values per MpsIntiFlags
        public uint   GlobalSystemInterrupt;

        internal Nmi(IoMemory region, int offset)
        {
            Debug.Assert(region.Read8(offset + 0) == TypeId);
            Debug.Assert(region.Read8(offset + 1) == Length);

            Flags                 = region.Read16(offset + 2);
            GlobalSystemInterrupt = region.Read32(offset + 4);

            // DebugStub.Print("{0:x4}:{1:x4} type {2:x1} Flags {3:x2} GlobalSystemInterrupt {4:x8} (Nmi)\n", __arglist(offset, offset + Length, TypeId, Flags, GlobalSystemInterrupt));
        }

        internal static object Create(IoMemory region, int offset)
        {
            return new Nmi(region, offset);
        }
    }

    public class ApicNmi
    {
        internal const byte TypeId = 0x04;
        internal const byte Length = 6;

        public byte   AcpiProcessorId;
        public ushort Flags;              // Values per MpsIntiFlags
        public byte   LocalApicLint;

        internal ApicNmi(IoMemory region, int offset)
        {
            Debug.Assert(region.Read8(offset + 0) == TypeId);
            Debug.Assert(region.Read8(offset + 1) == Length);

            AcpiProcessorId = region.Read8(offset + 2);
            Flags           = region.Read16(offset + 3);
            LocalApicLint   = region.Read8(offset + 5);

            // DebugStub.Print("{0:x4}:{1:x4} type {2:x1} ApicProcessorId {3:x2} Flags {4:x4} LocalApicLint {5:x2} (ApicNmi)\n", __arglist(offset, offset + Length, TypeId, AcpiProcessorId, Flags, LocalApicLint));
        }

        internal static object Create(IoMemory region, int offset)
        {
            return new ApicNmi(region, offset);
        }
    }

    public class LocalApicAddressOverride
    {
        internal const byte TypeId = 0x05;
        internal const byte Length = 12;

        ulong LocalApicAddress;

        internal LocalApicAddressOverride(IoMemory region, int offset)
        {
            Debug.Assert(region.Read8(offset + 0) == TypeId);
            Debug.Assert(region.Read8(offset + 1) == Length);

            // reserved = region.Read16(offset + 2);
            LocalApicAddress = region.Read64(offset + 4);

            // DebugStub.Print("{0:x04}:{1:x04} type {2:x01} LocalApicAddress {3:x016} (LocalApicAddressOverride)\n", __arglist(offset, offset + Length, TypeId, LocalApicAddress));
        }

        internal static object Create(IoMemory region, int offset)
        {
            return new LocalApicAddressOverride(region, offset);
        }
    }

    public class IoSApic
    {
        internal const byte TypeId = 0x6;
        internal const byte Length = 16;

        internal byte Id;
        internal uint InterruptBase;
        internal ulong Address;

        internal IoSApic(IoMemory region, int offset)
        {
            Debug.Assert(region.Read8(offset + 0) == TypeId);
            Debug.Assert(region.Read8(offset + 1) == Length);

            Id            = region.Read8(offset + 2);
            // reserved = region.Read8(offset + 3);
            InterruptBase = region.Read32(offset + 4);
            Address       = region.Read64(offset + 8);

            // DebugStub.Print("{0:x04}:{1:x04} type {2:x01} Id {3:x02} InterruptBase {4:x04} Address {5:x016} (IoSApic)\n", __arglist(offset, offset + Length, TypeId, Id, InterruptBase, Address));
        }

        internal static object Create(IoMemory region, int offset)
        {
            return new IoSApic(region, offset);
        }
    }

    public class LocalSApic
    {
        internal const byte TypeId = 0x07;
        internal const byte MinLength = 17;

        public byte   AcpiProcessorId;
        public byte   LocalSApicId;
        public byte   LocalSApicEid;
        public uint   Flags;              // Values per ApicFlags
        public uint   AcpiProcessorUidValue;
        public string AcpiProcessorUidString;

        internal LocalSApic(IoMemory region, int offset)
        {
            Debug.Assert(region.Read8(offset + 0) == TypeId);

            byte length = region.Read8(offset + 1);
            Debug.Assert(length >= MinLength);

            AcpiProcessorId        = region.Read8(offset + 2);
            LocalSApicId           = region.Read8(offset + 3);
            LocalSApicEid          = region.Read8(offset + 4);
            // reserved            = region.Read24(offset + 5);
            Flags                  = region.Read32(offset + 8);
            AcpiProcessorUidValue  = region.Read32(offset + 12) ;
            AcpiProcessorUidString = region.ReadString(offset + 16,
                                                       (int)length - 17);

            // DebugStub.Print("{0:x04}:{1:x04} type {2:x01} AcpiProcId {3:x02} LocalSApicId {4:x02} LocalSApicEid {5:x02} Flags {6:x08} AcpiProcUid {7:x04} AcpiProcUid \"{8}\" (LocalSApic)\n", __arglist(offset, offset + length, TypeId, AcpiProcessorId, LocalSApicId, LocalSApicEid, Flags, AcpiProcessorUidValue, AcpiProcessorUidString));
        }

        internal static object Create(IoMemory region, int offset)
        {
            return new LocalSApic(region, offset);
        }
    }

    public class PlatformInterruptSource
    {
        internal const byte TypeId = 0x8;
        internal const byte Length = 16;

        public ushort Flags;             // Values per MpsIntiFlags
        public byte   InterruptType;     // PlatformInterruptType
        public byte   ProcessorId;
        public byte   ProcessorEid;
        public byte   IoSApicVector;
        public uint   GlobalSystemInterrupt;
        public uint   SourceFlags;       // PlatformInterruptSourceFlags

        internal PlatformInterruptSource(IoMemory region, int offset)
        {
            Debug.Assert(region.Read8(offset + 0) == TypeId);
            Debug.Assert(region.Read8(offset + 1) == Length);

            Flags                 = region.Read16(offset + 2);
            InterruptType         = region.Read8(offset + 4);
            ProcessorId           = region.Read8(offset + 5);
            ProcessorEid          = region.Read8(offset + 6);
            IoSApicVector         = region.Read8(offset + 7);
            GlobalSystemInterrupt = region.Read32(offset + 8);
            SourceFlags           = region.Read32(offset + 12);

            // DebugStub.Print("{0:x04}:{1:x04} type {2:x01} Flags {3:x04} InterruptType {4:x02} ProcessorId {5:x02} ProcessorEid {6:x02} IoSApicVector {7:x02} GlobalSystemInterrupt {8:x04} SourceFlags {9:x04} (PlatformInterruptSource)\n", __arglist(offset, offset + Length, TypeId, Flags, InterruptType, ProcessorId, ProcessorEid, IoSApicVector, GlobalSystemInterrupt, SourceFlags));
        }

        internal static object Create(IoMemory region, int offset)
        {
            return new PlatformInterruptSource(region, offset);
        }
    }

}
