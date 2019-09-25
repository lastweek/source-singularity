///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IdeBus.cs
//
//  Creates IDE Bus device
//      Creates IDE controller devices as sub devices and registers with with the system
//      Creates two instances of the controller

#define SUPPORT_MINIMAL_MATCH
#define DONT_DISABLE_LEGACY_NFORCE_TO_HIDE_DVD

using System;
using System.Collections;
using System.Threading;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Drivers.IDE;

namespace Microsoft.Singularity.Drivers.IDE
{
    // create the resource objects for CTR to fill in
    // CTR will have to figure out which class to use...
    [DriverCategory]
    [Signature("pci/cc_0101")]

#if DONT_DISABLE_LEGACY_NFORCE_TO_HIDE_DVD
    [Signature("pci/ven_10de&dev_0053&cc_0101")] // nForce4
    [Signature("pci/ven_10de&dev_0035&cc_0101")] // nForce4 Intel Edition
#endif
    [EnumeratesDevice("/ata/controller")]
    internal class LegacyIdeBus : DriverCategoryDeclaration
    {
        [IoPortRange(4, Default = 0xffa0, Length = 0x10, Shared = true)]
        IoPortRange port1;

        [IoFixedIrqRange(Base = 14, Shared = true)]
        IoIrqRange primaryIrq;

        [IoFixedIrqRange(Base = 15, Shared = true)]
        IoIrqRange secondaryIrq;

        // Provide to unify creation.
        public static IDevice! DeviceCreate(IoConfig! config, String! instanceName)
        {
            return new IdeBus((PciDeviceConfig)config);
        }
    }

    [DriverCategory]
    [Signature("pci/ven_10de&dev_0054&cc_0101")] // nForce4
    [Signature("pci/ven_10de&dev_0055&cc_0101")] // nForce4
    [Signature("pci/ven_10de&dev_0036&cc_0101")] // nForce4 Intel Edition
    [Signature("pci/ven_10d3&dev_003e&cc_0101")] // nForce4 Intel Edition
#if DELL490_IS_FIXED
    // TODO: fixme
    [Signature("pci/ven_8086&dev_2680&cc_0101")] // Intel 3100 SATA in ATA mode
    [Signature("pci/ven_8086&dev_269e&cc_0101")] // Intel 3100 Legacy (DELL 490)
#endif
    [EnumeratesDevice("/ata/controller")]
    internal class NvIdeBus : DriverCategoryDeclaration
    {
        // TODO: Should all of these be shared?
        [IoPortRange(0, Default = 0x09f0, Length = 0x08, Shared = true)]
        IoPortRange port1;

        [IoPortRange(1, Default = 0x0bf0, Length = 0x04, Shared = true)]
        IoPortRange port2;

        [IoPortRange(2, Default = 0x0970, Length = 0x08, Shared = true)]
        IoPortRange port3;

        [IoPortRange(3, Default = 0x0b70, Length = 0x04, Shared = true)]
        IoPortRange port4;

        [IoPortRange(4, Default = 0xf600, Length = 0x10, Shared = true)]
        IoPortRange port5;

        [IoIrqRange(6, Default = 0x0b, Shared = true)]
        IoIrqRange irq1;

        // Provide to unify creation.
        public static IDevice! DeviceCreate(IoConfig! config, String! name)
        {
            return new IdeBus((PciDeviceConfig)config);
        }
    }

    [DriverCategory]
    [Signature("pci/ven_10de&dev_037f&cc_0101")] // new motherboardx
    [EnumeratesDevice("/ata/controller")]
    internal class TyanIdeBus : DriverCategoryDeclaration
    {
        [IoPortRange(0, Default = 0x24d0, Length = 0x08, Shared = true)]
        IoPortRange port1;

        [IoPortRange(1, Default = 0x24c4, Length = 0x04, Shared = true)]
        IoPortRange port2;

        [IoPortRange(2, Default = 0x24c8, Length = 0x08, Shared = true)]
        IoPortRange port3;

        [IoPortRange(3, Default = 0x24c0, Length = 0x04, Shared = true)]
        IoPortRange port4;

        [IoPortRange(4, Default = 0x2490, Length = 0x10, Shared = true)]
        IoPortRange port5;

        [IoIrqRange(6, Default = 0x07, Shared = true)]
        IoIrqRange irq1;

        // Provide to unify creation.
        public static IDevice! DeviceCreate(IoConfig! config, String! name)
        {
            return new IdeBus((PciDeviceConfig)config);
        }
    }

    [CLSCompliant(false)]
    public class IdeBus : IBusDevice
    {
        private PciDeviceConfig! config;
        private PnpConfig        primaryConfig;
        private PnpConfig        secondaryConfig;
        const uint PCI_CONFIG_Command_IOE           = 0x1;
        const uint PCI_CONFIG_PI_PrimaryMode        = 0x1; // NATIVE, ~compatible
        const uint PCI_CONFIG_PI_PrimaryFixed       = 0x2; // DYNAMIC, ~fixed
        const uint PCI_CONFIG_PI_SecondaryMode      = 0x4; // NATIVE, ~compatible
        const uint PCI_CONFIG_PI_SecondaryFixed     = 0x8; // DYNAMIC, ~fixed

        public IdeBus(PciDeviceConfig! config)
        {
            //DebugStub.Print("IdeBus: Device instantiated.\n");
            this.config = config;
        }

        public void Initialize()
        {
            // 0: irq, 1: command, 2: control, 3: dma
            IoRange[] primary = new IoRange[4];
            IoRange[] secondary = new IoRange[4];

            DebugStub.Print("IdeBus: Initializing device {0:x8}, vendor {1:x8}, config: {2}\n",
                            __arglist(
                                (ulong)config.DeviceId,
                                (ulong)config.VendorId,
                                config.ToString()));

            // First, Check to see if the IDE controller is active by checking the
            // IO enable bit in the PCI configspace Command Register.
            // For the moment we are assuming that Read32() is handling endian issues
            // for us.
            config.IoSpaceEnabled = true;

            // Read the Programming Interface (PI) Register from the PCI configuration space
            byte programmingInterfaceValue = config.Read8(0x9);

            // The high bit in the PI indicates the presence of bus-master DMA.
            assert config.DynamicRanges != null;

            if ((programmingInterfaceValue & 0x80) > 0 &&
                config.DynamicRanges[4] as IoPortRange != null) {

                IoPortRange! range = (IoPortRange!)(config.DynamicRanges[4]);

                primary[3] = range.RangeAtOffset(0, 8, true, true);
                secondary[3] = range.RangeAtOffset(8, 8, true, true);

                DebugStub.Print("IdeBus: Interface supports BusMaster DMA, at {0}\n",
                                __arglist(range.ToString()));
            }

            // Next we decode the Native/Compat bits from the PI register
            if ((programmingInterfaceValue & PCI_CONFIG_PI_PrimaryMode) > 0) {
                //DebugStub.Print("Using Native mode PI={0:x2}\n",__arglist(programmingInterfaceValue));
                primary[0] = config.GetIrq();
                secondary[0] = config.GetIrq();

                primary[1] = config.DynamicRanges[0];
                primary[2] = config.DynamicRanges[1];

                secondary[1] = config.DynamicRanges[2];
                secondary[2] = config.DynamicRanges[3];

                uint ideChannelConfig = config.Read32(0x50);
                Tracing.Log(Tracing.Debug,"Channel Config= {0:x8}\n",
                            (UIntPtr)ideChannelConfig);
            }
            else {
                //compat mode
                primary[0] = new IoIrqRange(14, 1);
                secondary[0] = new IoIrqRange(15, 1);

                primary[1] = new IoPortRange(0x1F0, 8, Access.ReadWrite);
                primary[2] = new IoPortRange(0x3F4, 4, Access.ReadWrite);

                secondary[1] = new IoPortRange(0x170, 8, Access.ReadWrite);
                secondary[2] = new IoPortRange(0x374, 4, Access.ReadWrite);
            }

            primaryConfig = new PnpConfig(new string[] { "/ata/controller" }, primary);
            secondaryConfig = new PnpConfig(new string[] { "/ata/controller" }, secondary);
        }

        public void Finalize()
        {
            DebugStub.Print("IdeBus: Finalized.\n");
        }

        public SortedList Enumerate()
        {
            SortedList found = new SortedList();
            found.Add("/controller0", primaryConfig);
            found.Add("/controller1", secondaryConfig);
            //FIXFIX:  need to figure out why shared interrupt is not working. Post SOSP
            //found.Add("/secondary",secondaryConfig);
            return found;
        }
    }
}

