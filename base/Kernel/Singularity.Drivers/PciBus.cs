////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PciBus.cs
//
//  Note:
//

#define VERBOSE
//#define DEBUG_PCI_BUS
//#define DONT_USE_PNP_FOR_PCI

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;

using System;
using System.Collections;
using System.Text;
using System.Configuration.Assemblies;
using System.Runtime.Remoting;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Drivers
{
    // create the resource object for CTR to fill in
    [DriverCategory]
    [Signature("/pnp/PNP0A03")]
    [Signature("/pnp/PNP0A08")]
    [EnumeratesDevice("pci/...")]
    internal class PciBusResources : DriverCategoryDeclaration
    {
        [IoFixedPortRange(Base = 0x0cf8, Length = 0x08, Shared = true)]
        IoPortRange configPort;

        // Provide to unify creation.
        public static IDevice! DeviceCreate(IoConfig! config, String! instanceName)
        {
            Tracing.Log(Tracing.Debug, "Creating PCI Bus");
            PciBus pciBus = new PciBus(PciEnumerator.GetEnumerator(config));
#if VERBOSE
            DebugStub.WriteLine("Displaying PCI Enumeration:");
            pciBus.Display();
            DebugStub.WriteLine("PCI Enumeration End.");
#endif
            return pciBus;
        }
    }

    [CLSCompliant(false)]
    public class PciBus : IBusDevice
    {
        private PciEnumerator! enumerator;

        static ushort IdentifierFromUnits(uint nBus, uint nDevice, uint nFunction)
        {
            return (ushort)(nFunction | (nDevice << 3) | (nBus << 8));
        }

        public PciBus(PciEnumerator! enumerator)
        {
            this.enumerator = enumerator;
        }

        public void Initialize()
        {
            Tracing.Log(Tracing.Debug, "Initializing PciBus.");
        }

        public void Finalize()
        {
        }

        public SortedList Enumerate()
        {
            return enumerator.Enumerate();
        }

        public void Display()
        {
            SortedList sl = enumerator.Enumerate();
            for ( int i = 0; i < sl.Count; i++ )  {
                object o = sl.GetByIndex(i);
                PciConfig config = o as PciConfig;
                if (config == null) {
                    DebugStub.Break();
                }
                else {
                    string str = sl.GetKey(i) as string;
                    DebugStub.Write("{0}: ",__arglist(str));
                    config.Print();
                }
            }
        }
    }

    [CLSCompliant(false)]
    public class PciEnumerator
    {
        public const uint MAX_BUSES         = 256;
        public const uint MAX_DEVICES       = 32;
        public const uint MAX_FUNCTIONS     = 8;
        public const uint MAX_IDENTIFIER    = (MAX_BUSES * MAX_DEVICES * MAX_FUNCTIONS) - 1;

        private const ushort PCI_ADDRESS_PORT    = 0xcf8;
        private const ushort PCI_DATA_PORT       = 0xcfc;

        private IoPort! addressPort;
        private IoPort! dataPort;

        static ushort IdentifierFromUnits(uint nBus, uint nDevice, uint nFunction)
        {
            return (ushort)(nFunction | (nDevice << 3) | (nBus << 8));
        }

        public static PciEnumerator GetEnumerator(IoConfig config)
        {
#if DONT_USE_PNP_FOR_PCI
            if (config != null && config.FixedRanges != null &&
                config.FixedRanges.Length >= 1 && config.FixedRanges[0] != null &&
                config.FixedRanges[0] is IoPortRange) {
                IoPortRange ports = (IoPortRange)config.FixedRanges[0];
                if(ports != null) {
                    IoPort addrPort = ports.PortAtOffset(0, 4, Access.Write);
                    IoPort dataPort = ports.PortAtOffset(4, 4, Access.ReadWrite);
                    return new PciEnumerator(addrPort, dataPort);
                }
                else {
                    DebugStub.WriteLine("PciBus: config != null but ports == null\n");
                    DebugStub.Break();
                }
            }
            else {
#endif
                IoPortRange dev = new IoPortRange(PCI_ADDRESS_PORT, 8, Access.ReadWrite);

                return new PciEnumerator(dev.PortAtOffset(0, 4, Access.Write),
                                         dev.PortAtOffset(4, 4, Access.ReadWrite));
#if DONT_USE_PNP_FOR_PCI
            }
#endif

        }

        private PciEnumerator(IoPort! addressPort, IoPort! dataPort)
        {
            this.addressPort = addressPort;
            this.dataPort = dataPort;
        }

        private uint Read32(uint identifier, uint offset)
        {
            if (identifier < 0 || identifier > MAX_IDENTIFIER) {
                throw new OverflowException("BAD_IDENTIFIER");
            }
            if ((offset & 0x3) != 0) {
                throw new Exception("BAD_OFFSET");
            }

            uint config = (((uint)offset & 0xfc) |
                           ((uint)identifier << 8) |
                           ((uint)1 << 31));

            addressPort.Write32(config);
            return dataPort.Read32();
        }

        private void Write32(uint identifier, uint offset, uint value)
        {
            if (identifier < 0 || identifier > MAX_IDENTIFIER) {
                throw new OverflowException("BAD_IDENTIFIER");
            }
            if ((offset & 0x3) != 0) {
                throw new Exception("BAD_OFFSET");
            }

            uint config = (((uint)offset & 0xfc) |
                           ((uint)identifier << 8) |
                           ((uint)1 << 31));

            addressPort.Write32(config);
            dataPort.Write32(value);
        }

        private PciPort PortForIdentifier(uint identifier)
        {
            if (identifier < 0 || identifier > MAX_IDENTIFIER) {
                throw new OverflowException("BAD_IDENTIFIER");
            }
            return new PciPort(addressPort, dataPort, (ushort)identifier);
        }

        public SortedList! Enumerate()
        {
            Tracing.Log(Tracing.Debug, "PCI Bus Enumerate");

            SortedList found = new SortedList();
            for (uint bus = 0; bus < MAX_BUSES; bus++) {
                bool hadDevices = false;

                for (uint device = 0; device < MAX_DEVICES; device++) {
                    PciConfig config;
                    uint identifier = IdentifierFromUnits(bus, device, 0);
                    uint u = Read32(identifier, 0);

                    if (u == ~0u || u == 0) {
                        continue;
                    }

                    u = Read32(identifier, 0x0c);

                    uint max_functions = (u & PciConfig.PCI_MULTIFUNCTION) == 0
                        ? (uint)1 : MAX_FUNCTIONS;
#if DEBUG_PCI_BUS
                    Tracing.Log(Tracing.Debug, "    {0}.{1}:C => max={2} [{3:x8}]",
                                bus, device, max_functions, u);
#endif

                    for (uint function = 0; function < max_functions; function++) {
                        identifier = IdentifierFromUnits(bus, device, function);
                        u = Read32(identifier, 0);
#if DEBUG_PCI_BUS
                        Tracing.Log(Tracing.Debug, "    {0}.{1}.{2}:0 => {3:x8}",
                                    bus, device, function, u);
#endif

                        if (u == ~0u || u == 0) {
                            continue;
                        }

                        u = Read32(identifier, 0x0c);
#if DEBUG_PCI_BUS
                        Tracing.Log(Tracing.Debug, "    {0}.{1}.{2}:C => {3:x8}",
                                    bus, device, function, u);
#endif

                        switch (u & PciConfig.PCI_TYPE_MASK) {
                            case PciConfig.PCI_DEVICE_TYPE:
                                config = new PciDeviceConfig(PortForIdentifier(identifier));
                                break;
                            case PciConfig.PCI_BRIDGE_TYPE:
                                config = new PciBridgeConfig(PortForIdentifier(identifier));
                                break;
                            case PciConfig.PCI_CARDBUS_TYPE:
                                config = new PciCardbusConfig(PortForIdentifier(identifier));
                                break;
                            default:
                                config = null;
                                break;
                        }

                        if (config != null) {

                            if (((config.VendorId == 0x8086) && (config.DeviceId == 0x269E)) ||
                                ((config.VendorId == 0x8086) && (config.DeviceId == 0x2681))) {
                                //
                                // TEMP: Do not enumerate Intel SATA controllers on the Dell Precision 490.
                                // This needs to be removed when we have real drivers for them.
                                //
                            }
                            else if ((config.VendorId == 0x8086) &&
                                     (config.DeviceId >= 0x27C0) &&
                                     (config.DeviceId <= 0x27C6)) {
                                //
                                // TEMP: Do not enumerate Intel SATA controllers on the Dell Precision 380.
                                // This needs to be removed when we have real drivers for them.
                                //
                            }
                            else {
                                found.Add(String.Format("/bus{0,4:x4}/dev{1,4:x4}/func{2,4:x4}",
                                                        bus, device, function),
                                          config);
                                hadDevices = true;
                            }
                        }
                    }
                }
                if (!hadDevices) {
                    break;
                }
            }
            return found;
        }
    }
}
