//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System.Runtime.CompilerServices;
using kernel;

namespace kernel
{

internal class IoThread: ThreadStart
{
    public override void Run()
    {
        System.DebugStub.Print("IoThread@" + Kernel.CurrentThread + ". ");
        byte[] pciDmaBuffer;
        try {
            CompilerIntrinsics.Cli();
            pciDmaBuffer = NucleusCalls.PciDmaBuffer();
        } finally {
            CompilerIntrinsics.Sti();
        }

        if (pciDmaBuffer == null)
        {
            System.DebugStub.Print("No IO-MMU. ");
            Kernel.kernel.NewSemaphore(0).Wait();
            return;
        }
        // Set up networking
        Microsoft.Singularity.NetStack2.ARP arp =
            new Microsoft.Singularity.NetStack2.ARP();
        Microsoft.Singularity.NetStack2.IP.Initialize(arp);
        Microsoft.Singularity.NetStack2.Ethernet.Initialize(arp);

        //Microsoft.Singularity.NetStack2.Channels.Private.RoutingExpManager routingManager =
        //    new Microsoft.Singularity.NetStack2.Channels.Private.RoutingExpManager();
        Microsoft.Singularity.NetStack2.Channels.Private.IPContract ipManager =
            new Microsoft.Singularity.NetStack2.Channels.Private.IPContract();

        // Establish DMA buffer area
        Microsoft.Singularity.Io.DmaMemory.Setup();

        // Enumerate and initialize PCI devices
        for (uint id = 0; id < 65536; id += 8) {
            uint v;
            try {
                CompilerIntrinsics.Cli();
                v = NucleusCalls.PciConfigRead32(id, 0);
            } finally {
                CompilerIntrinsics.Sti();
            }
            if (v == 0x107c8086) {
                // Intel NIC
                System.DebugStub.Print("Found Intel NIC. ");
                Microsoft.Singularity.Drivers.Network.Intel.Intel intel =
                    new Microsoft.Singularity.Drivers.Network.Intel.Intel(
                        new Microsoft.Singularity.Io.PciDeviceConfig((ushort)id),
                        new Microsoft.Singularity.Io.PciMemory(id),
                        "82541 PI",
                        Microsoft.Singularity.Drivers.Network.Intel.CardType.I82541PI);
                intel.Initialize();
                Microsoft.Singularity.Io.Net.NicDeviceContract nicDev =
                    new Microsoft.Singularity.Drivers.Network.Intel.IntelDeviceChannel(intel);
                bool ok = Microsoft.Singularity.NetStack2.Channels.Nic.Nic.CreateAndRegister(
                    nicDev, "/nic0");
                System.VTable.Assert(ok);
                ipManager.StartDhcp("/nic0");
            }
        }
        System.DebugStub.Print("IoThread done. ");
        Kernel.kernel.NewSemaphore(0).Wait();
    }
}

} // kernel
