///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   NvPciLpcBridge.cs
//
//  Notes:
//
//  Driver for Low-Pin Count devices.  These are a mix of control
//  registers for legacy and current devices.  We currently use it to
//  reroute integrated peripheral interrupts.

using System;
using System.Collections;
using System.Diagnostics;

using Microsoft.Singularity.Drivers.Pci;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;

namespace Microsoft.Singularity.Drivers
{
    // create the resource object for CTR to fill in
    [DriverCategory]
    [Signature("pci/ven_10de&dev_0050&cc_0601")] // nForce4
    [Signature("pci/ven_10de&dev_0030&cc_0601")] // nForce4 Intel Edition
    [EnumeratesDevice("/pnp/PNP0103")]
    internal class NvPciLpcResources : DriverCategoryDeclaration
    {
        // Provide to unify creation.
        public static IDevice! DeviceCreate(IoConfig! config, string! name)
        {
            return new NvPciLpcBridge((PciDeviceConfig) config);
        }
    }

    public sealed class NvPciLpcBridge : IBusDevice
    {
        private const ushort PCI_VENDOR_NVIDIA             = 0x10de;

        private const ushort PCI_DEVICE_NVIDIA_AMD_SATA0   = 0x0054;
        private const ushort PCI_DEVICE_NVIDIA_AMD_SATA1   = 0x0055;
        private const ushort PCI_DEVICE_NVIDIA_AMD_MCP04   = 0x0056;

        private const ushort PCI_DEVICE_NVIDIA_INTEL_SATA0 = 0x0036;
        private const ushort PCI_DEVICE_NVIDIA_INTEL_SATA1 = 0x003e;
        private const ushort PCI_DEVICE_NVIDIA_INTEL_MCP04 = 0x0030;

        private const int PCI_HPET_POINTER = 0x44;

        // Generic PCI interrupt remapping
        private const int PCI_INTERRUPT_MAPPING = 0x7c;
        private const int SATA0_DEVICE_7_ROLL = 24; // Secondary SATA0 IRQ
        private const int SATA1_DEVICE_8_ROLL = 20; // Secondary SATA1 IRQ
        private const int PCI_INTR_Z_ROLL     = 12;
        private const int PCI_INTR_Y_ROLL     = 8;
        private const int PCI_INTR_X_ROLL     = 4;
        private const int PCI_INTR_W_ROLL     = 0;

        private const uint PINT_SEL_DISABLE_IRQ = 0x0;
        private const uint PINT_SEL_APIC_IRQ17 = 0x1;
        private const uint PINT_SEL_APIC_IRQ18 = 0x2;
        private const uint PINT_SEL_IRQ3       = 0x3;
        private const uint PINT_SEL_IRQ4       = 0x4;
        private const uint PINT_SEL_IRQ5       = 0x5;
        private const uint PINT_SEL_IRQ6       = 0x6;
        private const uint PINT_SEL_IRQ7       = 0x7;
        private const uint PINT_SEL_APIC_IRQ16 = 0x8;
        private const uint PINT_SEL_IRQ9       = 0x9;
        private const uint PINT_SEL_IRQ10      = 0xa;
        private const uint PINT_SEL_IRQ11      = 0xb;
        private const uint PINT_SEL_IRQ12      = 0xc;
        private const uint PINT_SEL_APIC_IRQ19 = 0xd;
        private const uint PINT_SEL_IRQ14      = 0xe;
        private const uint PINT_SEL_IRQ15      = 0xf;

        // Integrate peripheral mapping
        private const int INTERNAL_IRQ0 = 0x80;
        private const int INTERNAL_IRQ0_SATA0_ROLL = 28;  // Primary SATA
        private const int INTERNAL_IRQ0_SATA1_ROLL = 24;
        private const int INTERNAL_IRQ0_P2P_ROLL   = 16;
        private const int INTERNAL_IRQ0_USB2_ROLL  = 12;
        private const int INTERNAL_IRQ0_SMBUS_ROLL = 8;
        private const int INTERNAL_IRQ0_TCO_ROLL   = 4;
        private const int INTERNAL_IRQ0_SCI_ROLL   = 0;

        private const int INTERNAL_IRQ1 = 0x84;
        private const int INTERNAL_IRQ1_IDE1_ROLL = 28;
        private const int INTERNAL_IRQ1_IDE0_ROLL = 24;
        private const int INTERNAL_IRQ1_MCI_ROLL  = 20;
        private const int INTERNAL_IRQ1_ACI_ROLL  = 16;
        private const int INTERNAL_IRQ1_MAC_ROLL  = 8;
        private const int INTERNAL_IRQ1_USB0_ROLL = 0;

        private const uint INTERNAL_SEL_DISABLE_IRQ = 0x0;
        private const uint INTERNAL_SEL_APIC_IRQ23  = 0x1;
        private const uint INTERNAL_SEL_APIC_IRQ22  = 0x2;
        private const uint INTERNAL_SEL_IRQ3        = 0x3;
        private const uint INTERNAL_SEL_IRQ4        = 0x4;
        private const uint INTERNAL_SEL_IRQ5        = 0x5;
        private const uint INTERNAL_SEL_IRQ6        = 0x6;
        private const uint INTERNAL_SEL_IRQ7        = 0x7;
        private const uint INTERNAL_SEL_APIC_IRQ20  = 0x8;
        private const uint INTERNAL_SEL_IRQ9        = 0x9;
        private const uint INTERNAL_SEL_IRQ10       = 0xa;
        private const uint INTERNAL_SEL_IRQ11       = 0xb;
        private const uint INTERNAL_SEL_IRQ12       = 0xc;
        private const uint INTERNAL_SEL_APIC_IRQ21  = 0xd;
        private const uint INTERNAL_SEL_IRQ14       = 0xe;
        private const uint INTERNAL_SEL_IRQ15       = 0xf;

        ///////////////////////////////////////////////////////////////////////

        PciDeviceConfig! config;

        internal NvPciLpcBridge(PciDeviceConfig! pciDeviceConfig)
        {
            config = pciDeviceConfig;
        }

        void IDevice.Initialize()
        {
            DebugStub.Print("NvPciLpc.Initialize (maxirq={0})\n",
                            __arglist(IoSystem.GetMaximumIrq()));
            // Reroute NVidia fixed device resources on APIC system
            if (IoSystem.GetMaximumIrq() > 15) {
                ReroutePciInterrupts();
            }
        }

        void IDevice.Finalize()
        {
        }

        private void SetRouteEntry(int register, int roll, uint value)
        {
            DebugStub.Print("NvPciLpc.SetRouteEntry(reg={0},rol={1},val={2})\n",
                            __arglist(register, roll, value));
            uint r = config.Read32(register) & ~(0x0fu << roll);
            r |= value << roll;
            config.Write32(register, r);
        }

        private void ReroutePciInterrupts()
        {
            PciEnumerator enumerator = PciEnumerator.GetEnumerator(null);
            ICollection! pciConfigs = enumerator.Enumerate().Values;

            foreach (PciConfig! pc in pciConfigs) {
                if (pc.VendorId == PCI_VENDOR_NVIDIA) {
                    // NB - if there are multiple devices on the bus with the
                    // same ID, we still break.  Also note that the parameter
                    // "1" indicates that this method wants to renumber the 1st
                    // Irq in the IoConfig.DynamicRanges list, not the 1st
                    // object.
                    if ((pc.DeviceId == PCI_DEVICE_NVIDIA_AMD_MCP04 ||
                         pc.DeviceId == PCI_DEVICE_NVIDIA_INTEL_MCP04) &&
                        IoSystem.RequestRerouteIrq((!)pc.Id, 1, 23))
                    {
                        SetRouteEntry(INTERNAL_IRQ1, INTERNAL_IRQ1_MAC_ROLL,
                                      INTERNAL_SEL_APIC_IRQ23);
                        pc.SetInterrupt(23);
                    }
                    else if ((pc.DeviceId == PCI_DEVICE_NVIDIA_AMD_SATA0 ||
                              pc.DeviceId == PCI_DEVICE_NVIDIA_INTEL_SATA0) &&
                             IoSystem.RequestRerouteIrq((!)pc.Id, 1, 14))
                    {
                        SetRouteEntry(INTERNAL_IRQ0,
                                      INTERNAL_IRQ0_SATA0_ROLL,
                                      INTERNAL_SEL_IRQ14);
                        pc.SetInterrupt(14);

                        // Map secondary same as primary
                        SetRouteEntry(PCI_INTERRUPT_MAPPING,
                                      SATA0_DEVICE_7_ROLL,
                                      PINT_SEL_IRQ14);
                    }
                    else if ((pc.DeviceId == PCI_DEVICE_NVIDIA_AMD_SATA1 ||
                              pc.DeviceId == PCI_DEVICE_NVIDIA_INTEL_SATA1) &&
                             IoSystem.RequestRerouteIrq((!)pc.Id, 1, 15))
                    {
                        SetRouteEntry(INTERNAL_IRQ0,
                                      INTERNAL_IRQ0_SATA1_ROLL,
                                      INTERNAL_SEL_IRQ15);
                        pc.SetInterrupt(15);

                        // Map secondary same as primary
                        SetRouteEntry(PCI_INTERRUPT_MAPPING,
                                      SATA1_DEVICE_8_ROLL,
                                      PINT_SEL_IRQ15);
                    }
                }
            }
        }

        public SortedList Enumerate()
        {
            SortedList devs = new SortedList();

            uint hpetPointer = config.Read32(PCI_HPET_POINTER);

            if (hpetPointer != 0) {
                IoMemoryRange hpetMemory =
                    new IoMemoryRange(hpetPointer, 0x1000,
                                      Access.ReadWrite);

                devs.Add("/hpet",
                         new PnpConfig(new string[] { "/pnp/PNP0103" },
                                       new IoRange [1] { hpetMemory }
                                       )
                         );
            }

#if NO
            //
            // XXX sgc compiler does not accept the following preferred
            // means of instantiating a PnpConfig object.  It complains:
            //
            // NvPciLpc.cs(189,31): error CS1501:
            // No overload for method 'PnpConfig' takes '2' arguments
            //
            // which is bogus - there are two constructors that take two
            // arguments.  They are both public and differ only in their
            // second argument.  This is visible in PnpConfig.cs and in
            // the kernel ilasm.
            //
            ArrayList hpetResources = new ArrayList();
            hpetResources.Add(hpetMemory);
            devs.Add("/hpet", new PnpConfig("/PNP0103", hpResources));
#endif
            return devs;
        }
    }
}
