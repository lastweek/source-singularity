////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Register.cs
//
//  Note:   PnP Device Type Registration and Base Initialization.
//

#define ACPI_ENABLED
#define VESA_ENABLED

using Microsoft.Singularity.Drivers.IDE;
using Microsoft.Singularity.Drivers.Pci;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Hal.Acpi;
using Microsoft.Singularity.Io;

#if VESA_ENABLED
using System;
using System.Collections;
#endif


namespace Microsoft.Singularity.Drivers
{
    public sealed class Devices
    {
        public static void RegisterPnpResources()
        {
            // Register our pseudo bus driver
            PseudoBus pseudo = new PseudoBus();
            IoSystem.AddRootDevice("/pseudobus0", pseudo, pseudo.ReportConfig());

            // : /pnp/PNP0700 : Floppy Controller   : PC Standard
            // : /pnp/PNP0C01 : RAM                 : System Board
            // : /pnp/PNP0A03 : PCI                 : PCI Bus
            // : /pnp/PNP0501 : Generic Serial      : 16550A COM Port
            // : /pnp/PNP0501 : Generic Serial      : 16550A COM Port
            // : /pnp/PNP0400 : AT Parallel         : LPT Port
            // : /pnp/PNP0000 : ISA 8259 PIC        : AT Interrupt Controller
            // : /pnp/PNP0200 : ISA 8237 DMA        : AT DMA Controller
            // : /pnp/PNP0100 : ISA 8254 Timer      : AT Timer
            // : /pnp/PNP0B00 : ISA RTC Controller  : AT RTC
            // : /pnp/PNP0800 : Other               : ???
            // : /pnp/PNP0C02 : Other               : PnP Event Notification
            // : /pnp/PNP0C02 : Other               : PnP Event Notification
            // : /pnp/PNP0C04 : Other               : Math Coprocessor
            // : /pnp/PNP0303 : Keyboard controller : 101/102 Keyboard
            // : /pnp/PNP0F13 : Mouse Controller    : Logitech PS/2 Mouse
            AcpiDevice[] deviceInfo = null;
            AcpiTables.Parse();
#if ACPI_ENABLED
            deviceInfo = AcpiTables.LoadDevices();
#endif // ACPI_ENABLED


            if (deviceInfo != null && deviceInfo.Length > 0) {
                AcpiBus! acpi = new AcpiBus(deviceInfo);
                IoSystem.AddRootDevice("/acpi0", acpi, acpi.ReportConfig());
            }
            else {
                PnpBios bios = new PnpBios(Resources.GetPnpBiosInfo());

                // in order for IoSystem accounting to work, we need to explicitly
                // tell it what the IoConfig of the root device is:
                IoSystem.AddRootDevice("/pnp0", bios, bios.ReportConfig());
            }

#if VESA_ENABLED
            // Add VESA Device if it exists.
            if (((!)Platform.ThePlatform).VesaBuffer != 0) {
                SortedList custom = new SortedList();

                custom.Add("000",
                           new PnpConfig(
                               new String[] { "/pnp/vesa" },
                               new IoRange[] {
                                   new IoMemoryRange(
                                       Platform.ThePlatform.VesaBuffer,
                                       0x300000, Access.ReadWrite) }));
                IoSystem.AddDevicesToTree(custom, "/vesa0/", false);
            }
#endif // VESA_ENABLED

        }
        // Now that we use metadata, this only registers drivers that do not run
        // in separate processes.  All external processes are registered through
        // the IoSystem.Initialize() code.
        public static void RegisterInternalDrivers()
        {
            // PCI Bus
            IoSystem.RegisterKernelDriver(
                typeof(PciBusResources),
                new IoDeviceCreate(PciBusResources.DeviceCreate));

            // nForce4 LPC Bridge
            IoSystem.RegisterKernelDriver(
                typeof(NvPciLpcResources),
                new IoDeviceCreate(NvPciLpcResources.DeviceCreate));

            // Legacy PC IDE bus
            IoSystem.RegisterKernelDriver(
                typeof(LegacyIdeBus),
                new IoDeviceCreate(LegacyIdeBus.DeviceCreate));

            // nForce4 IDE bus
            IoSystem.RegisterKernelDriver(
                typeof(NvIdeBus),
                new IoDeviceCreate(NvIdeBus.DeviceCreate));

            // Tyan motherboard IDE bus
            IoSystem.RegisterKernelDriver(
                typeof(TyanIdeBus),
                new IoDeviceCreate(TyanIdeBus.DeviceCreate));
        }
    }
}
