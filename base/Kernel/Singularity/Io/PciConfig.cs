///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PciConfig.cs
//
//  Note:
//

#define DEBUG_PCI

using System;
using StringBuilder = System.Text.StringBuilder;
using System.Collections;
using Microsoft.Singularity;

#if !SINGULARITY_PROCESS
using Microsoft.Singularity.Hal;
#endif

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public class PciConfig : IoConfig
    {
        //
        // Bit encodings for  PCI_COMMON_CONFIG.HeaderType
        //
        public const uint PCI_MULTIFUNCTION   = 0x800000; // full dword
        public const uint PCI_TYPE_MASK       = 0x7f0000; // full dword
        public const uint PCI_DEVICE_TYPE     = 0x000000; // full dword
        public const uint PCI_BRIDGE_TYPE     = 0x010000; // full dword
        public const uint PCI_CARDBUS_TYPE    = 0x020000; // full dword

        private const int PCI_CONTROL_OFFSET  = 0x0004;
        private const int PCI_STATUS_OFFSET   = 0x0006;

        //
        // Bit encodings for PCI_COMMON_CONFIG.Control
        //
        public const uint PCI_ENABLE_IO_SPACE               = 0x0001;
        public const uint PCI_ENABLE_MEMORY_SPACE           = 0x0002;
        public const uint PCI_ENABLE_BUS_MASTER             = 0x0004;
        public const uint PCI_ENABLE_SPECIAL_CYCLES         = 0x0008;
        public const uint PCI_ENABLE_WRITE_AND_INVALIDATE   = 0x0010;
        public const uint PCI_ENABLE_VGA_COMPATIBLE_PALETTE = 0x0020;
        public const uint PCI_ENABLE_PARITY                 = 0x0040; // (ro+)
        public const uint PCI_ENABLE_WAIT_CYCLE             = 0x0080; // (ro+)
        public const uint PCI_ENABLE_SERR                   = 0x0100; // (ro+)
        public const uint PCI_ENABLE_FAST_BACK_TO_BACK      = 0x0200; // (ro)
        public const uint PCI_DISABLE_INTERRUPTS            = 0x0400;

        //
        // Bit encodings for PCI_COMMON_CONFIG.Status
        //
        const uint PCI_STATUS_FAST_BACK_TO_BACK        = 0x0080;  // (ro)
        const uint PCI_STATUS_DATA_PARITY_DETECTED     = 0x0100;
        const uint PCI_STATUS_DEVSEL                   = 0x0600;  // 2 bits wide
        const uint PCI_STATUS_SIGNALED_TARGET_ABORT    = 0x0800;
        const uint PCI_STATUS_RECEIVED_TARGET_ABORT    = 0x1000;
        const uint PCI_STATUS_RECEIVED_MASTER_ABORT    = 0x2000;
        const uint PCI_STATUS_SIGNALED_SYSTEM_ERROR    = 0x4000;
        const uint PCI_STATUS_DETECTED_PARITY_ERROR    = 0x8000;

        // Bit encodes for PCI_COMMON_CONFIG.u.type0.BaseAddresses
        //
        const uint PCI_BAR_TYPE_MASK     = 0xf;
        const uint PCI_BAR_TYPE_IO       = 0x1;
        const uint PCI_BAR_TYPE_MEM20    = 0x2;
        const uint PCI_BAR_TYPE_MEM32    = 0x0;
        const uint PCI_BAR_TYPE_MEM64    = 0x4;
        const uint PCI_BAR_TYPE_MEMMASK  = 0x6;
        const uint PCI_BAR_TYPE_PREFETCH = 0x8;

        const uint PCI_ROMADDRESS_ENABLED              = 0x00000001;

        const uint PCI_ENABLE_BRIDGE_PARITY_ERROR        = 0x0001;
        const uint PCI_ENABLE_BRIDGE_SERR                = 0x0002;
        const uint PCI_ENABLE_BRIDGE_ISA                 = 0x0004;
        const uint PCI_ENABLE_BRIDGE_VGA                 = 0x0008;
        const uint PCI_ENABLE_BRIDGE_MASTER_ABORT_SERR   = 0x0020;
        const uint PCI_ASSERT_BRIDGE_RESET               = 0x0040;
        const uint PCI_ENABLE_BRIDGE_FAST_BACK_TO_BACK   = 0x0080;

        const byte PCI_CLASS_STORAGE            = 0x01;
        const byte PCI_CLASS_NETWORK            = 0x02;
        const byte PCI_CLASS_DISPLAY            = 0x03;
        const byte PCI_CLASS_MULTIMEDIA         = 0x04;
        const byte PCI_CLASS_MEMORY             = 0x05;
        const byte PCI_CLASS_BRIDGE             = 0x06;
        const byte PCI_CLASS_COMMUNICATION      = 0x07;
        const byte PCI_CLASS_SYSTEM             = 0x08;
        const byte PCI_CLASS_INPUT              = 0x09;
        const byte PCI_CLASS_DOCKING            = 0x0a;
        const byte PCI_CLASS_PROCESSOR          = 0x0b;
        const byte PCI_CLASS_SERIAL             = 0x0c;
        const byte PCI_CLASS_WIRELESS           = 0x0d;
        const byte PCI_CLASS_I2O                = 0x0e;
        const byte PCI_CLASS_SATELLITE          = 0x0f;
        const byte PCI_CLASS_ENCRYPTION         = 0x10;
        const byte PCI_CLASS_ACQUISITION        = 0x11;
        const byte PCI_CLASS_OTHERS             = 0xff;

        const byte PCI_CLASS_STORAGE_SCSI       = 0x00;
        const byte PCI_CLASS_STORAGE_IDE        = 0x01; // NB: Interface
        const byte PCI_CLASS_STORAGE_FLOPPY     = 0x02;
        const byte PCI_CLASS_STORAGE_IPI        = 0x03;
        const byte PCI_CLASS_STORAGE_RAID       = 0x04;
        const byte PCI_CLASS_STORAGE_ATA        = 0x05; // NB: Interface
        const byte PCI_CLASS_STORAGE_OTHER      = 0x80;

        const byte PCI_CLASS_NETWORK_ETHERNET   = 0x00;
        const byte PCI_CLASS_NETWORK_RING       = 0x01;
        const byte PCI_CLASS_NETWORK_FDDI       = 0x02;
        const byte PCI_CLASS_NETWORK_ATM        = 0x03;
        const byte PCI_CLASS_NETWORK_ISDN       = 0x04;
        const byte PCI_CLASS_NETWORK_FIP        = 0x05;
        const byte PCI_CLASS_NETWORK_PICMG      = 0x06; // NB: Interface
        const byte PCI_CLASS_NETWORK_OTHER      = 0x80;

        const byte PCI_CLASS_DISPLAY_VGA        = 0x00; // NB: Interface
        const byte PCI_CLASS_DISPLAY_XGA        = 0x01;
        const byte PCI_CLASS_DISPLAY_3D         = 0x02;
        const byte PCI_CLASS_DISPLAY_OTHER      = 0x80;

        const byte PCI_CLASS_MULTIMEDIA_VIDEO   = 0x00;
        const byte PCI_CLASS_MULTIMEDIA_AUDIO   = 0x01;
        const byte PCI_CLASS_MULTIMEDIA_TELEPHONY   = 0x02;
        const byte PCI_CLASS_MULTIMEDIA_OTHER   = 0x80;

        const byte PCI_CLASS_MEMORY_RAM         = 0x00;
        const byte PCI_CLASS_MEMORY_FLASH       = 0x01;
        const byte PCI_CLASS_MEMORY_OTHER       = 0x80;

        const byte PCI_CLASS_BRIDGE_HOST        = 0x00;
        const byte PCI_CLASS_BRIDGE_ISA         = 0x01;
        const byte PCI_CLASS_BRIDGE_EISA        = 0x02;
        const byte PCI_CLASS_BRIDGE_MC          = 0x03;
        const byte PCI_CLASS_BRIDGE_PCI         = 0x04; // NB: Interface
        const byte PCI_CLASS_BRIDGE_PCMCIA      = 0x05;
        const byte PCI_CLASS_BRIDGE_NUBUS       = 0x06;
        const byte PCI_CLASS_BRIDGE_CARDBUS     = 0x07;
        const byte PCI_CLASS_BRIDGE_RACEWAY     = 0x08; // NB: Interface
        const byte PCI_CLASS_BRIDGE_SEMIPCI     = 0x09; // NB: Interface
        const byte PCI_CLASS_BRIDGE_INFINIBAND  = 0x0a;
        const byte PCI_CLASS_BRIDGE_OTHER       = 0x80;

        const byte PCI_CLASS_COMMUNICATION_SERIAL       = 0x00; // NB: Interface
        const byte PCI_CLASS_COMMUNICATION_PARALLEL     = 0x01; // NB: Interface
        const byte PCI_CLASS_COMMUNICATION_MULTIPORT    = 0x02;
        const byte PCI_CLASS_COMMUNICATION_MODEM        = 0x03; // NB: Interface
        const byte PCI_CLASS_COMMUNICATION_GPIB         = 0x04;
        const byte PCI_CLASS_COMMUNICATION_SMARTCARD    = 0x05;
        const byte PCI_CLASS_COMMUNICATION_OTHER        = 0x80;

        const byte PCI_CLASS_SYSTEM_PIC         = 0x00; // NB: Interface
        const byte PCI_CLASS_SYSTEM_DMA         = 0x01; // NB: Interface
        const byte PCI_CLASS_SYSTEM_TIMER       = 0x02; // NB: Interface
        const byte PCI_CLASS_SYSTEM_RTC         = 0x03; // NB: Interface
        const byte PCI_CLASS_SYSTEM_PCIHP       = 0x04;
        const byte PCI_CLASS_SYSTEM_OTHER       = 0x80;

        const byte PCI_CLASS_INPUT_KEYBOARD     = 0x00;
        const byte PCI_CLASS_INPUT_PEN          = 0x01;
        const byte PCI_CLASS_INPUT_MOUSE        = 0x02;
        const byte PCI_CLASS_INPUT_SCANNER      = 0x03;
        const byte PCI_CLASS_INPUT_GAMEPORT     = 0x04; // NB: Interface
        const byte PCI_CLASS_INPUT_OTHER        = 0x80;

        const byte PCI_CLASS_SERIAL_FIREWIRE    = 0x00; // NB: Interface
        const byte PCI_CLASS_SERIAL_ACCESS      = 0x01;
        const byte PCI_CLASS_SERIAL_SSA         = 0x02;
        const byte PCI_CLASS_SERIAL_USB         = 0x03; // NB: Interface
        const byte PCI_CLASS_SERIAL_FIBRE       = 0x04;
        const byte PCI_CLASS_SERIAL_SMBUS       = 0x05;
        const byte PCI_CLASS_SERIAL_INFINIBAND  = 0x06;
        const byte PCI_CLASS_SERIAL_IPMI        = 0x07; // NB: Interface
        const byte PCI_CLASS_SERIAL_SERCOS      = 0x08;
        const byte PCI_CLASS_SERIAL_CANBUS      = 0x09;

        const byte PCI_CLASS_WIRELESS_IRDA      = 0x00;
        const byte PCI_CLASS_WIRELESS_IR        = 0x01;
        const byte PCI_CLASS_WIRELESS_RF        = 0x10;
        const byte PCI_CLASS_WIRELESS_BLUETOOTH = 0x11;
        const byte PCI_CLASS_WIRELESS_BROADBAND = 0x12;
        const byte PCI_CLASS_WIRELESS_OTHER     = 0x80;

        const byte PCI_CLASS_I2O_I2O            = 0x00; // NB: Interface

        const byte PCI_CLASS_SATELLITE_TV       = 0x01;
        const byte PCI_CLASS_SATELLITE_AUDIO    = 0x02;
        const byte PCI_CLASS_SATELLITE_VOICE    = 0x03;
        const byte PCI_CLASS_SATELLITE_DATA     = 0x04;

        const byte PCI_CLASS_ENCRYPTION_NETWORK = 0x00;
        const byte PCI_CLASS_ENCRYPTION_ENTERTAINMENT = 0x10;
        const byte PCI_CLASS_ENCRYPTION_OTHER   = 0x80;

        const byte PCI_CLASS_ACQUISITION_DPIO   = 0x00;
        const byte PCI_CLASS_ACQUISITION_PERF   = 0x01;
        const byte PCI_CLASS_ACQUISITION_COMM   = 0x10;
        const byte PCI_CLASS_ACQUISITION_MGMT   = 0x20;
        const byte PCI_CLASS_ACQUISITION_OTHER  = 0x80;

        const int PCI_INTERRUPT_LINE = 0x3c;

        const int PCI_INTERRUPT_PIN  = 0x3d;
        const byte PCI_INTERRUPT_PIN_A = 1;
        const byte PCI_INTERRUPT_PIN_B = 2;
        const byte PCI_INTERRUPT_PIN_C = 3;
        const byte PCI_INTERRUPT_PIN_D = 4;

        protected PciPort   port;

        public ushort       VendorId;               // 00..01 (ro)
        public ushort       DeviceId;               // 02..03 (ro)

        protected byte      RevisionId;             // 08..08 (ro)
        public byte         Interface;              // 09..09 (ro)
        protected byte      SubClassId;             // 0a..0a (ro)
        protected byte      ClassId;                // 0b..0b (ro)
        public byte         CacheLineSize;          // 0c..0c (ro+)
        protected byte      LatencyTimer;           // 0d..0d (ro+)
        protected byte      HeaderType;             // 0e..0e (ro)
        protected byte      BIST;                   // 0f..0f Built in self test

        protected ulong[]   BaseAddresses;          // 10..17 or ..27 [2 or 6]
        protected ulong[]   BaseAddrSizes;

        protected ushort    SubsystemVendorId;      // 2c..2d (devices only)
        protected ushort    SubsystemDeviceId;      // 2e..2f (devices only)

        protected uint      ROMBaseAddress;         // 38..3b or 30.33
        protected byte      InterruptPin;           // 3d..3d

        public static PciConfig Create(String[] ids, PciPort port,
                                       IoRange [] fixedRanges)
        {
            uint u = port.Read32(0);
            if (u == ~0u || u == 0) {
                return null;
            }

            PciConfig config = null;

            u = port.Read32(0x0c);
            switch (u & PciConfig.PCI_TYPE_MASK) {
                case PciConfig.PCI_DEVICE_TYPE:
                    config = new PciDeviceConfig(port);
                    break;
                case PciConfig.PCI_BRIDGE_TYPE:
                    config = new PciBridgeConfig(port);
                    break;
                case PciConfig.PCI_CARDBUS_TYPE:
                    config = new PciCardbusConfig(port);
                    break;
            }
            if (config != null) {
                config.FixedRanges = fixedRanges;
            }
            return config;
        }

        internal PciConfig(String[] ids, PciPort port)
        {
            this.port = port;
            this.Read();
            this.Ids = ids;
        }

        public PciConfig(PciPort port)
        {
            this.port = port;
        }

        public PciPort PciPort
        {
            get { return this.port; }
        }

        public IoIrqRange GetIrq()
        {
            return new IoIrqRange(InterruptLine, 1);
        }

        public void SetInterrupt(byte irq)
        {
            Write8(PCI_INTERRUPT_LINE, irq);
        }

        public byte InterruptLine
        {
            get { return Read8(PCI_INTERRUPT_LINE); }
        }

        public ushort Control
        {
            get { return Read16(PCI_CONTROL_OFFSET); }
            set { Write16(PCI_CONTROL_OFFSET, value); }
        }

        public ushort Status
        {
            get { return Read16(PCI_STATUS_OFFSET); }
            set { Write16(PCI_STATUS_OFFSET, value); }
        }

        public bool IoSpaceEnabled
        {
            get { return ((uint)Control & PCI_ENABLE_IO_SPACE) != 0; }
            set {
                uint tmp = (uint)Control & ~PCI_ENABLE_IO_SPACE;
                if (value) {
                    tmp |= PCI_ENABLE_IO_SPACE;
                }
                Control = (ushort)(tmp & 0xffff);
            }
        }

        public bool MemorySpaceEnabled
        {
            get { return ((uint)Control & PCI_ENABLE_MEMORY_SPACE) != 0; }
            set {
                uint tmp = (uint)Control & ~PCI_ENABLE_MEMORY_SPACE;
                if (value) {
                    tmp |= PCI_ENABLE_MEMORY_SPACE;
                }
                Control = (ushort)(tmp & 0xffff);
            }
        }

        public bool InterruptsEnabled
        {
            get { return ((uint)Control & PCI_DISABLE_INTERRUPTS) == 0; }
            set {
                uint tmp = (uint)Control & ~PCI_DISABLE_INTERRUPTS;
                if (!value) {
                    tmp |= PCI_ENABLE_MEMORY_SPACE;
                }
                Control = (ushort)(tmp & 0xffff);
            }
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Port operations
        //

        public ulong Read64(int offset)
        {
            ulong hi = Read32(offset + 4);
            return (hi << 32) | (ulong)Read32(offset);
        }

        public void Write64(int offset, ulong value)
        {
            Write32(offset + 4, (uint)(value >> 32));
            Write32(offset, (uint)(value & 0xffffffff));
        }

        public uint Read32(int offset) {
            return port.Read32(offset);
        }

        public void Write32(int offset, uint value) {
            port.Write32(offset, value);
        }

        public ushort Read16(int offset) {
            return port.Read16(offset);
        }

        public void Write16(int offset, ushort value) {
            port.Write16(offset, value);
        }

        public byte Read8(int offset) {
            return port.Read8(offset);
        }

        public void Write8(int offset, byte value) {
            port.Write8(offset, value);
        }

        ///////////////////////////////////////////////////////////////////////

        protected virtual void Read()
        {
            uint u;

            u = Read32(0x00);
            VendorId = (ushort)(u & 0xffff);
            DeviceId = (ushort)((u >> 16) & 0xffff);

            u = Read32(0x08);
            RevisionId = (byte)(u & 0xff);
            Interface = (byte)((u >> 8) & 0xff);
            SubClassId = (byte)((u >> 16) & 0xff);
            ClassId = (byte)((u >> 24) & 0xff);

            u = Read32(0x0c);
            CacheLineSize = (byte)(u & 0xff);
            LatencyTimer = (byte)((u >> 8) & 0xff);
            HeaderType = (byte)((u >> 16) & 0xff);
            BIST = (byte)((u >> 24) & 0xff);

            this.Ids = GetIds();
        }

        /// <summary>
        /// <para>
        /// Builds the list of device IDs for this PCI device.  We generate the same
        /// strings that Windows uses for its hardware IDs and compatible IDs.
        /// The order is significant; the PNP manager will search the device IDs,
        /// one by one, for a device driver that matches.  The list is ordered from
        /// most specific to least specific.
        /// </para>
        ///
        /// <para>
        /// WDM "hardware IDs":
        ///      PCI\VEN_xxxy&amp;DEV_yyyy&amp;SUBSYS_zzzzzzzz&amp;REV_rr
        ///      PCI\VEN_xxxy&amp;DEV_yyyy&amp;SUBSYS_zzzzzzzz
        ///      PCI\VEN_xxxy&amp;DEV_yyyy&amp;CC_ccssii
        ///      PCI\VEN_xxxy&amp;DEV_yyyy&amp;CC_ccss
        ///      PCI\VEN_xxxy
        /// </para>
        ///
        /// <para>
        /// WDM "compatible IDs":
        ///      PCI\VEN_xxxy&amp;DEV_yyyy&amp;REV_rr
        ///      PCI\VEN_xxxy&amp;DEV_yyyy
        ///      PCI\VEN_xxxx&amp;CC_ccssii
        ///      PCI\VEN_xxxx&amp;CC_ccss
        ///      PCI\CC_ccssii
        ///      PCI\CC_ccss
        /// </para>
        /// </summary>
        /// <returns>
        /// An array containing the device IDs.  The list is ordered from most specific
        /// to least specific.
        /// </returns>
        public string[] GetIds()
        {
            const string pci_prefix = @"PCI/";
            const string and = "&";

            string id_classcode = "CC_" + ByteToHex(this.ClassId) + ByteToHex(this.SubClassId);
            string id_classcode_interface = id_classcode + ByteToHex(this.Interface);
            string id_vendor = "VEN_" + UInt16ToHex(this.VendorId);
            string id_device = "DEV_" + UInt16ToHex(this.DeviceId);
            string id_vendor_device = id_vendor + and + id_device;
            string id_revision = "REV_" + ByteToHex(this.RevisionId);
            string id_subsys = "SUBSYS_" + UInt16ToHex(this.SubsystemVendorId) + UInt16ToHex(this.SubsystemDeviceId);

#if ENABLE_OLD_SIGNATURE
            string sing_id = String.Format("/pci/{0,2:x2}/{1,2:x2}/{2,4:x4}/{3,4:x4}/" +
                               "{4,2:x2}",
                               ClassId,
                               SubClassId,
                               VendorId,
                               DeviceId,
                               RevisionId);
#endif

            string[] ids = {
#if ENABLE_OLD_SIGNATURE
                sing_id,
#endif

                // Hardware IDs
                pci_prefix + id_vendor_device + and + id_classcode
                + and + id_subsys + and + id_revision,
                pci_prefix + id_vendor_device + and + id_subsys + and + id_revision,
                pci_prefix + id_vendor_device + and + id_subsys,
                pci_prefix + id_vendor_device + and + id_classcode_interface,
                pci_prefix + id_vendor_device + and + id_classcode,
                pci_prefix + id_vendor,

                // Compatible IDs
                pci_prefix + id_vendor_device + and + id_revision,
                pci_prefix + id_vendor_device,
                pci_prefix + id_vendor + and + id_classcode_interface,
                pci_prefix + id_vendor + and + id_classcode,
                pci_prefix + id_classcode_interface,
                pci_prefix + id_classcode,
            };

            for (int i = 0; i < ids.Length; i++) {
                string id = ids[i];
                id = id.Replace('\\', '/').ToLower();
                ids[i] = id;
            }

            return ids;
        }

        static string ByteToHex(byte value)
        {
            StringBuilder sb = new StringBuilder(2);
            sb.Append(HexDigits[value >> 4]);
            sb.Append(HexDigits[value & 0xf]);
            return sb.ToString();
        }

        static string UInt16ToHex(ushort value)
        {
            StringBuilder sb = new StringBuilder(4);
            sb.Append(HexDigits[(value >> 12) & 0xf]);
            sb.Append(HexDigits[(value >> 8) & 0xf]);
            sb.Append(HexDigits[(value >> 4) & 0xf]);
            sb.Append(HexDigits[value & 0xf]);
            return sb.ToString();

        }

        const string HexDigits = "0123456789ABCDEF";

        private void ProbeIoRange(int offset,
                                  out ushort start,
                                  out ushort length)
        {
            uint start32 = port.Read32(offset);

            DebugStub.Assert((start32 & PCI_BAR_TYPE_IO) == PCI_BAR_TYPE_IO);

            Write32(offset, ~0u);
            uint length32 = Read32(offset);
            length32 &= ~PCI_BAR_TYPE_IO;
            length32 |= 0xffff0000;
            length32 = ~length32 + 1;

            Write32(offset, start32);

            if (start32 <= 0xffff && length32 <= 0xffff) {
                start  = (ushort)start32;
                length = (ushort)length32;
            }
            else {
                start  = 0;
                length = 0;
#if DEBUG_PCI
                DebugStub.Break();
#endif // DEBUG_PCI
            }
        }

        private void ProbeMemoryRange64(int offset,
                                        out ulong start,
                                        out ulong length)
        {
            start = Read64(offset);

            DebugStub.Assert((start & PCI_BAR_TYPE_MEMMASK) ==
                             PCI_BAR_TYPE_MEM64);

            Write64(offset, UInt64.MaxValue);
            length = Read64(offset);

            length &= ~((ulong)PCI_BAR_TYPE_MASK);
            length = ~length + 1;

            Write64(offset, start);

            if (UIntPtr.Size == 4 &&
                (start > (ulong)UInt32.MaxValue ||
                 (start + length) > (ulong)UInt32.MaxValue)) {
                start  = 0;
                length = 0;
#if DEBUG_PCI
                DebugStub.Break();
#endif // DEBUG_PCI
            }
        }

        private void ProbeMemoryRange32(int offset,
                                        out uint start,
                                        out uint length)
        {
            start = Read32(offset);

            DebugStub.Assert(
                (start & PCI_BAR_TYPE_MEMMASK) == PCI_BAR_TYPE_MEM32 ||
                (start & PCI_BAR_TYPE_MEMMASK) == PCI_BAR_TYPE_MEM20
                );

            Write32(offset, UInt32.MaxValue);
            length = port.Read32(offset) & ~PCI_BAR_TYPE_MASK;
            if ((start & PCI_BAR_TYPE_MASK) == PCI_BAR_TYPE_MEM20) {
                length |= 0xfff00000;
            }
            length = ~length + 1;

            Write32(offset, start);
        }

        protected void ReadBaseAddresses(int n)
        {
            InterruptPin = Read8(PCI_INTERRUPT_PIN);

            if (InterruptPin != 0) {

                // Add interrupt resource to list of ranges if present
                DynamicRanges = new IoRange [n + 1];

                DynamicRanges[n] = new IoIrqRange(Read8(PCI_INTERRUPT_LINE), 1);
                byte currentInterruptLine = InterruptLine;

#if !SINGULARITY_PROCESS
                byte newInterruptLine = Platform.TranslatePciInterrupt(currentInterruptLine,
                                                                       InterruptPin,
                                                                       port);
                if (newInterruptLine != currentInterruptLine)
                {
                    SetInterrupt(newInterruptLine);
                    currentInterruptLine = newInterruptLine;
                }
#endif

                IoIrqRange range = new IoIrqRange(currentInterruptLine, 1);

                DynamicRanges[n] = range;
            }
            else {
                DynamicRanges = new IoRange [n];
            }

            BaseAddresses = new ulong [n];
            BaseAddrSizes = new ulong [n];

            uint control = Read32(0x04);
            uint send = (control & (~(PCI_ENABLE_IO_SPACE|PCI_ENABLE_MEMORY_SPACE)))
                & 0xffff;
            if (control == 0x02b00003) {
                send = (control & (~(PCI_ENABLE_IO_SPACE))) & 0xffff;
            }

#if DONT_SKIP_NVIDIA
            if (control == 0x02b00003) {
                send = control & 0xffff;

                send &= ~PCI_ENABLE_IO_SPACE;
                port.Write32(0x04, send);
                Tracing.Log(Tracing.Debug, "NVIDIA Read[{0}]: ctrl={1:x8} send={2:x8}", n, control, send);
                uint x = Read32(0x04);
                Tracing.Log(Tracing.Debug, "NVIDIA Read[{0}]: finl={1:x8}", n, x);

                port.Write32(0x04, control & 0xffff);
                x = Read32(0x04);
                Tracing.Log(Tracing.Debug, "NVIDIA Read[{0}]: last={1:x8}", n, x);
                return;
            }
#endif

            port.Write32(0x04, send);

            for (int i = 0, bar = 0; i < n; i++, bar++) {
                int offset = 0x10 + i * 4;
                uint type = Read32(offset) & PCI_BAR_TYPE_MASK;

                if ((type & PCI_BAR_TYPE_IO) == PCI_BAR_TYPE_IO) {
                    ushort addr16, size16;
                    ProbeIoRange(offset, out addr16, out size16);
                    if (size16 != 0) {
                        DynamicRanges[bar] =
                            new IoPortRange(
                                (ushort)((uint)addr16 & ~PCI_BAR_TYPE_IO),
                                size16,
                                Access.ReadWrite
                                );
                        BaseAddresses[bar] = addr16;
                        BaseAddrSizes[bar] = size16;
                    }
                }
                else if ((type & PCI_BAR_TYPE_MEMMASK) == PCI_BAR_TYPE_MEM64) {
                    ulong addr64, size64;
                    ProbeMemoryRange64(offset, out addr64, out size64);
                    if (size64 != 0) {
                        DynamicRanges[bar] =
                            new IoMemoryRange(
                                addr64 & ~PCI_BAR_TYPE_MASK,
                                size64,
                                Access.ReadWrite
                                );
                        BaseAddresses[bar] = addr64;
                        BaseAddrSizes[bar] = size64;
                        i += 1;
                    }
                }
                else if ((type & PCI_BAR_TYPE_MEMMASK) == PCI_BAR_TYPE_MEM32 ||
                         (type & PCI_BAR_TYPE_MEMMASK) == PCI_BAR_TYPE_MEM20) {
                    uint addr32, size32;
                    ProbeMemoryRange32(offset, out addr32, out size32);
                    if (size32 != 0) {
                        DynamicRanges[bar] =
                            new IoMemoryRange(
                                addr32 & ~PCI_BAR_TYPE_MASK,
                                size32,
                                Access.ReadWrite
                                );
                        BaseAddresses[bar] = addr32;
                        BaseAddrSizes[bar] = size32;
                    }
                }
            }

            port.Write32(0x04, control & 0xffff);
        }

        public override string ToString()
        {
            return String.Format("[PCI: VEN_{0:x4} DEV_{1:x4} CLASS {2:x2}.{3:x2}.{4:x2} BASE {5:x8}]",
                this.VendorId,
                this.DeviceId,
                this.ClassId,
                this.SubClassId,
                this.Interface,
                this.Base);
        }

        public override string ToPrint()
        {
            StringBuilder text = new StringBuilder();
            base.DumpRanges(text);
            text.AppendFormat("    PCI Vendor/Device:  {0:x4}.{1:x4} rev {2:x2}  {3} {4}\n",
                this.VendorId,
                this.DeviceId,
                this.RevisionId,
                this.Vendor,
                this.Device);
            text.AppendFormat("    PCI Class/Subclass: {0:x2}.{1:x2}.{2:x2}\n",
                this.ClassId,
                this.SubClassId,
                this.Interface,
                this.Class);
            return text.ToString();
        }

        protected string PrintAddresses()
        {
            String s;

            bool print = false;
            for (int i = 0; i < BaseAddresses.Length; i++) {
                if (BaseAddresses[i] != 0 || BaseAddrSizes[i] != 0) {
                    print = true;
                    break;
                }
            }
            if (!print &&
                ROMBaseAddress == 0 && InterruptLine == 0 && InterruptPin == 0) {

                return "";
            }

            s = String.Format("      RM={0:x8} IL={1,2:x2} IP={2,2:x2} ",
                              ROMBaseAddress,
                              InterruptLine,
                              InterruptPin);

            int printed = 0;
            for (int i = 0; i < BaseAddresses.Length; i++) {
                if (DynamicRanges[i] != null) {
                    s += String.Format("A{0}={1} ", i, DynamicRanges[i]);
                }

#if DONT_PRINT_RAW_ADDRESSS_BUT_ONLY_RANGES
                if (BaseAddresses[i] == 0 && BaseAddrSizes[i] == 0) {
                    continue;
                }

                if ((BaseAddresses[i] & PCI_BAR_TYPE_IO) != 0) {
                    s += String.Format("A{0}=IO:{1:x8}[{2:x}]  ",
                                       i, BaseAddresses[i], BaseAddrSizes[i]);
                }
                else if ((BaseAddresses[i] & PCI_BAR_TYPE_MEM64) != 0) {
                    s += String.Format("A{0}=64:{1:x8}[{2:x}] ",
                                       i, BaseAddresses[i], BaseAddrSizes[i]);
                }
                else if ((BaseAddresses[i] & PCI_BAR_TYPE_MEM20) != 0) {
                    s += String.Format("A{0}=20:{1:x8}[{2:x}] ",
                                       i, BaseAddresses[i], BaseAddrSizes[i]);
                }
                else {
                    s += String.Format("A{0}=32:{1:x8}[{2:x}] ",
                                       i, BaseAddresses[i], BaseAddrSizes[i]);
                }
#endif
                printed++;
            }
            return s;
        }

        protected string Vendor {
            get {
                switch (VendorId) {
                    case 0x1011:
                        return "DEC";
                    case 0x104c:
                        return "TI";
                    case 0x5333:
                        return "S3";
                    case 0x8086:
                        return "Intel";
                    case 0x10de:
                        return "nVidia";
                    case 0x1106:
                        return "VIA Technologies";
                    default:
                        return String.Format("{0,4:x4}", VendorId);
                }
            }
        }

        protected string Device {
            get {
                switch (VendorId) {
                    case 0x8086:
                        switch (DeviceId) {
                            case 0x0484: return "82379AB";
                            case 0x1229: return "82559nic";
                            case 0x122E: return "82371FB";
                            case 0x1234: return "82371MX";
                            case 0x2410: return "82801AA";
                            case 0x7000: return "82371SB";
                            case 0x7110: return "82371AB";
                            default:
                                break;
                        }
                        break;

                    case 0x10de:
                        // NVIDIA
                        switch (DeviceId) {
                            case 0x0050: return "PCI-to-ISA bridge";
                            case 0x0052: return "nForce PCI System Management Module";
                            case 0x0057: return "nForce Network Interface";
                            case 0x0059: return "Realtek AC'97 Audio";
                            case 0x005a: return "USB OHCI";
                            case 0x005d: return "PCI-to-PCI bridge";
                            case 0x005e: return "nForce4 HyperTransport Bridge";
                            default:
                                break;
                        }
                        break;

                    case 0x1106:
                        // VIA
                        switch (DeviceId) {
                            case 0x3044: return "OHCI Compliant IEEE 1394 Host Controller";
                            default:
                                break;
                        }
                        break;


                    default:
                        break;
                }

                return String.Format("{0,4:x4}", DeviceId);

            }
        }

        protected string Class {
            get {
                switch (ClassId) {
                    case PCI_CLASS_STORAGE:
                        switch (SubClassId) {
                            case PCI_CLASS_STORAGE_SCSI:      return "Scsi";
                            case PCI_CLASS_STORAGE_IDE:       return "Ide";
                            case PCI_CLASS_STORAGE_FLOPPY:    return "Floppy";
                            case PCI_CLASS_STORAGE_IPI:       return "Ipi";
                            case PCI_CLASS_STORAGE_RAID:      return "Raid";
                            case PCI_CLASS_STORAGE_OTHER:     return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_NETWORK:
                        switch (SubClassId) {
                            case PCI_CLASS_NETWORK_ETHERNET:  return "Ethernet";
                            case PCI_CLASS_NETWORK_RING:      return "Ring";
                            case PCI_CLASS_NETWORK_FDDI:      return "Fddi";
                            case PCI_CLASS_NETWORK_ATM:       return "Atm";
                            case PCI_CLASS_NETWORK_OTHER:     return "Other";
                            case PCI_CLASS_NETWORK_FIP:       return "FIP";
                            case PCI_CLASS_NETWORK_PICMG:     return "PICMG";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_DISPLAY:
                        switch (SubClassId) {
                            case PCI_CLASS_DISPLAY_VGA:       return "Vga";
                            case PCI_CLASS_DISPLAY_XGA:       return "Xga";
                            case PCI_CLASS_DISPLAY_3D:        return "3D";
                            case PCI_CLASS_DISPLAY_OTHER:     return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_MULTIMEDIA:
                        switch (SubClassId) {
                            case PCI_CLASS_MULTIMEDIA_VIDEO:  return "Video";
                            case PCI_CLASS_MULTIMEDIA_AUDIO:  return "Audio";
                            case PCI_CLASS_MULTIMEDIA_TELEPHONY:  return "Telephony";
                            case PCI_CLASS_MULTIMEDIA_OTHER:  return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_MEMORY:
                        switch (SubClassId) {
                            case PCI_CLASS_MEMORY_RAM:        return "Ram";
                            case PCI_CLASS_MEMORY_FLASH:      return "Flash";
                            case PCI_CLASS_MEMORY_OTHER:      return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_BRIDGE:
                        switch (SubClassId) {
                            case PCI_CLASS_BRIDGE_HOST:       return "Host";
                            case PCI_CLASS_BRIDGE_ISA:        return "Isa";
                            case PCI_CLASS_BRIDGE_EISA:       return "Eisa";
                            case PCI_CLASS_BRIDGE_MC:         return "Mc";
                            case PCI_CLASS_BRIDGE_PCI:        return "Pci";
                            case PCI_CLASS_BRIDGE_PCMCIA:     return "Pcmcia";
                            case PCI_CLASS_BRIDGE_NUBUS:      return "Nubus";
                            case PCI_CLASS_BRIDGE_CARDBUS:    return "Cardbus";
                            case PCI_CLASS_BRIDGE_RACEWAY:    return "Raceway";
                            case PCI_CLASS_BRIDGE_SEMIPCI:    return "Semipci";
                            case PCI_CLASS_BRIDGE_INFINIBAND: return "Infiniband";
                            case PCI_CLASS_BRIDGE_OTHER:      return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_COMMUNICATION:
                        switch (SubClassId) {
                            case PCI_CLASS_COMMUNICATION_SERIAL:      return "Serial";
                            case PCI_CLASS_COMMUNICATION_PARALLEL:    return "Parallel";
                            case PCI_CLASS_COMMUNICATION_MULTIPORT:   return "Multiport";
                            case PCI_CLASS_COMMUNICATION_MODEM:       return "Modem";
                            case PCI_CLASS_COMMUNICATION_GPIB:        return "Gpib";
                            case PCI_CLASS_COMMUNICATION_SMARTCARD:   return "Smartcard";
                            case PCI_CLASS_COMMUNICATION_OTHER:       return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_SYSTEM:
                        switch (SubClassId) {
                            case PCI_CLASS_SYSTEM_PIC:        return "Pic";
                            case PCI_CLASS_SYSTEM_DMA:        return "Dma";
                            case PCI_CLASS_SYSTEM_TIMER:      return "Timer";
                            case PCI_CLASS_SYSTEM_RTC:        return "Rtc";
                            case PCI_CLASS_SYSTEM_PCIHP:      return "Pcihp";
                            case PCI_CLASS_SYSTEM_OTHER:      return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_INPUT:
                        switch (SubClassId) {
                            case PCI_CLASS_INPUT_KEYBOARD:    return "Keyboard";
                            case PCI_CLASS_INPUT_PEN:         return "Pen";
                            case PCI_CLASS_INPUT_MOUSE:       return "Mouse";
                            case PCI_CLASS_INPUT_SCANNER:     return "Scanner";
                            case PCI_CLASS_INPUT_GAMEPORT:    return "Gameport";
                            case PCI_CLASS_INPUT_OTHER:       return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_SERIAL:
                        switch (SubClassId) {
                            case PCI_CLASS_SERIAL_FIREWIRE:   return "Firewire";
                            case PCI_CLASS_SERIAL_ACCESS:     return "Access";
                            case PCI_CLASS_SERIAL_SSA:        return "Ssa";
                            case PCI_CLASS_SERIAL_USB:
                                switch (this.Interface) {
                                    case 0x00: return "USB1.1 UHCI";
                                    case 0x10: return "USB1.1 OHCI";
                                    case 0x20: return "USB2.0 EHCI";
                                    default:
                                        return "Usb";
                                }
                            case PCI_CLASS_SERIAL_FIBRE:      return "Fibre";
                            case PCI_CLASS_SERIAL_SMBUS:      return "Smbus";
                            case PCI_CLASS_SERIAL_INFINIBAND: return "Infiniband";
                            case PCI_CLASS_SERIAL_IPMI:       return "Ipmi";
                            case PCI_CLASS_SERIAL_SERCOS:     return "Sercos";
                            case PCI_CLASS_SERIAL_CANBUS:     return "Canbus";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }
                    case PCI_CLASS_WIRELESS:
                        switch (SubClassId) {
                            case PCI_CLASS_WIRELESS_IRDA:     return "Irda";
                            case PCI_CLASS_WIRELESS_IR:       return "Ir";
                            case PCI_CLASS_WIRELESS_RF:       return "Rf";
                            case PCI_CLASS_WIRELESS_BLUETOOTH: return "Bluetooth";
                            case PCI_CLASS_WIRELESS_BROADBAND: return "Broadband";
                            case PCI_CLASS_WIRELESS_OTHER:    return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_I2O:
                        switch (SubClassId) {
                            case PCI_CLASS_I2O_I2O:           return "I2O";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_SATELLITE:
                        switch (SubClassId) {
                            case PCI_CLASS_SATELLITE_TV:      return "Tv";
                            case PCI_CLASS_SATELLITE_AUDIO:   return "Audio";
                            case PCI_CLASS_SATELLITE_VOICE:   return "Voice";
                            case PCI_CLASS_SATELLITE_DATA:    return "Data";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_ENCRYPTION:
                        switch (SubClassId) {
                            case PCI_CLASS_ENCRYPTION_NETWORK:      return "Network";
                            case PCI_CLASS_ENCRYPTION_ENTERTAINMENT:return "Entertainment";
                            case PCI_CLASS_ENCRYPTION_OTHER:        return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }

                    case PCI_CLASS_ACQUISITION:
                        switch (SubClassId) {
                            case PCI_CLASS_ACQUISITION_DPIO:  return "Dpio";
                            case PCI_CLASS_ACQUISITION_PERF:  return "Perf";
                            case PCI_CLASS_ACQUISITION_COMM:  return "Comm";
                            case PCI_CLASS_ACQUISITION_MGMT:  return "Mgmt";
                            case PCI_CLASS_ACQUISITION_OTHER: return "Other";
                            default: return String.Format("{0,2:x2}", SubClassId);
                        }
                    default: return String.Format("{0,2:x2}", SubClassId);
                }
            }
        }

        protected string Base {
            get {
                switch (ClassId) {
                    case PCI_CLASS_STORAGE:       return "Storage";
                    case PCI_CLASS_NETWORK:       return "Network";
                    case PCI_CLASS_DISPLAY:       return "Display";
                    case PCI_CLASS_MULTIMEDIA:    return "Multimedia";
                    case PCI_CLASS_MEMORY:        return "Memory";
                    case PCI_CLASS_BRIDGE:        return "Bridge";
                    case PCI_CLASS_COMMUNICATION: return "Communication";
                    case PCI_CLASS_SYSTEM:        return "System";
                    case PCI_CLASS_INPUT:         return "Input";
                    case PCI_CLASS_DOCKING:       return "Docking";
                    case PCI_CLASS_PROCESSOR:     return "Processor";
                    case PCI_CLASS_SERIAL:        return "Serial";
                    case PCI_CLASS_OTHERS:        return "Others";
                    case PCI_CLASS_WIRELESS:      return "Wireless";
                    case PCI_CLASS_I2O:           return "I2O";
                    case PCI_CLASS_SATELLITE:     return "Satellite";
                    case PCI_CLASS_ENCRYPTION:    return "Encryption";
                    case PCI_CLASS_ACQUISITION:   return "Acquisition";
                    default: return String.Format("{0,2:x2}", ClassId);
                }
            }
        }
    }

    [CLSCompliant(false)]
    public class PciBridgeConfig : PciConfig
    {
        // Bridges: (HeaderType & ~PCI_MULTIFUNCTION) == PCI_BRIDGE_TYPE
        // public uint  BaseAddresses[2];           // 10..17
        protected byte     PrimaryBus;                 // 18..18
        protected byte     SecondaryBus;               // 19..19
        protected byte     SubordinateBus;             // 1a..1a
        protected byte     SecondaryLatency;           // 1b..1b
        protected byte     IOBase;                     // 1c..1c
        protected byte     IOLimit;                    // 1d..1d
        protected ushort   SecondaryStatus;            // 1e..1f
        protected ushort   MemoryBase;                 // 20..21
        protected ushort   MemoryLimit;                // 22..23
        protected ushort   PrefetchBase;               // 24..25
        protected ushort   PrefetchLimit;              // 26..27
        protected uint     PrefetchBaseUpper32;        // 28..2b
        protected uint     PrefetchLimitUpper32;       // 2c..2f
        protected ushort   IOBaseUpper16;              // 30..31
        protected ushort   IOLimitUpper16;             // 32..33
        // protected uint  Reserved;                   // 34..37
        // protected uint  ROMBaseAddress;             // 38..3b
#if DISABLED
        // protected byte  InterruptLine;              // 3c..3c
#endif
        // protected byte  InterruptPin;               // 3d..3d
        protected ushort   BridgeControl;              // 3e..3f

        public PciBridgeConfig(PciPort port)
            : base(port)
        {
            Read();
        }

        protected override void Read()
        {
            base.Read();
            base.ReadBaseAddresses(2);

            uint u;

            u = port.Read32(0x18);
            PrimaryBus = (byte)(u & 0xff);
            SecondaryBus = (byte)((u >> 8) & 0xff);
            SubordinateBus = (byte)((u >> 16) & 0xff);
            SecondaryLatency = (byte)((u >> 24) & 0xff);

            u = port.Read32(0x1c);
            IOBase = (byte)(u & 0xff);
            IOLimit = (byte)((u >> 8) & 0xff);
            SecondaryStatus = (ushort)((u >> 16) & 0xffff);

            u = port.Read32(0x20);
            MemoryBase = (ushort)(u & 0xffff);
            MemoryLimit = (ushort)((u >> 16) & 0xffff);

            u = port.Read32(0x24);
            PrefetchBase = (ushort)(u & 0xffff);
            PrefetchLimit = (ushort)((u >> 16) & 0xffff);

            u = port.Read32(0x28);
            PrefetchBaseUpper32 = u;

            u = port.Read32(0x2c);
            PrefetchLimitUpper32 = u;

            u = port.Read32(0x30);
            IOBaseUpper16 = (ushort)(u & 0xffff);
            IOLimitUpper16 = (ushort)((u >> 16) & 0xffff);

            u = port.Read32(0x38);
            ROMBaseAddress = u;

            u = port.Read32(0x3c);
#if DISABLED
            InterruptLine = (byte)(u & 0xff);
#endif
            InterruptPin = (byte)((u >> 8) & 0xff);
            BridgeControl = (ushort)((u >> 16) & 0xffff);
        }

        public override string ToPrint()
        {
            return base.ToPrint() +
                String.Format("BUS={0,2:x2}.{1,2:x2}.{2,2:x2} IO={3,4:x4}..{4,4:x4}",
                              PrimaryBus, SecondaryBus, SubordinateBus,
                              IOBase, IOLimit) +
                "" +
                base.PrintAddresses() + "";
        }
    }

    [CLSCompliant(false)]
    public class PciDeviceConfig : PciConfig
    {
        // Devices: (HeaderType & ~PCI_MULTIFUNCTION) == PCI_DEVICE_TYPE
        // public uint  BaseAddresses[6];           // 10..27
        protected uint     CardbusCisPtr;              // 28..2b
        // protected ushort SubsystemVendorId;         // 2c..2d
        // protected ushort SubsystemDeviceId;         // 2e..2f
        // protected uint  ROMBaseAddress;             // 30..33
        protected byte     capabilities;               // 34..34
        // protected byte  Reserved[7];                // 35..38
#if DISABLED
        // protected byte  InterruptLine;              // 3c..3c
#endif
        // protected byte  InterruptPin;               // 3d..3d (ro)
        protected byte     MinimumGrant;               // 3e..3e (ro)
        protected byte     MaximumLatency;             // 3f..3f (ro)

        public PciDeviceConfig(PciPort port)
            : base(port)
        {
            Read();
        }

        public byte Capabilities
        {
            get { return this.capabilities; }
        }

        protected override void Read()
        {
            base.Read();
            base.ReadBaseAddresses(6);

            uint u;

            u = port.Read32(0x28);
            CardbusCisPtr = u;

            u = port.Read32(0x2c);
            SubsystemVendorId = (ushort)(u & 0xffff);
            SubsystemDeviceId = (ushort)((u >> 16) & 0xffff);

            u = port.Read32(0x30);
            ROMBaseAddress = u;

            u = port.Read32(0x34);
            this.capabilities = (byte)(u & 0xff);

            u = port.Read32(0x3c);
            if ((u & 0xff) == 0) {
                port.Write32(0x3c, u | 0x7);
                u = port.Read32(0x3c);
            }

#if DISABLED
            InterruptLine = (byte)(u & 0xff);
#endif
            InterruptPin = (byte)((u >> 8) & 0xff);
            MinimumGrant = (byte)((u >> 16) & 0xff);
            MaximumLatency = (byte)((u >> 24) & 0xff);

            Ids = GetIds();
        }

        public override string ToPrint()
        {
            String s = base.ToPrint() + "\n    " + base.PrintAddresses();

            if (CardbusCisPtr != 0 ||
                Capabilities != 0 ||
                MinimumGrant != 0 ||
                MaximumLatency != 0) {

                s += String.Format("      cis={0:x8} cap={1,2:x2} mg={2,2:x2} ml={3,2:x2}",
                                   CardbusCisPtr,
                                   Capabilities,
                                   MinimumGrant,
                                   MaximumLatency);
            }
            return s;
        }
    }

    [CLSCompliant(false)]
    public class PciCardbusConfig : PciConfig
    {
        public PciCardbusConfig(PciPort port)
            : base(port)
        {
            BaseAddresses = new ulong [0];
            Read();
        }

        protected override void Read()
        {
            base.Read();
        }

        public override string ToPrint()
        {
            return base.ToPrint();
        }
    }
} // end namespace Microsoft.Singularity.Io
