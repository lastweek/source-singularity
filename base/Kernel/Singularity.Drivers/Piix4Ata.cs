////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Piix4Ata.cs
//
//  Device driver for accessing the IDE/ATA functionality of the Intel PIIX4
//  and compatible devices.
//

using Microsoft.Singularity;

using System;
using System;
using System.Text;
using System.Configuration.Assemblies;
using System.Runtime.Remoting;
using System.Runtime.InteropServices;

namespace Microsoft.Singularity.Drivers
{
    public class Piix4Ata : IDiskDevice
    {
        public static IDevice! DeviceCreate(IoConfig! config)
        {
            DebugStub.Print("Creating Piix4Ata Driver\n");
            return new Piix4Ata((PciDeviceConfig)config);
        }

        private Piix4Ata(PciDeviceConfig config)
        {
            DebugStub.Print("Piix4Ata Constructor\n");
        }

        public void Initialize()
        {
            DebugStub.Print("Initializing Piix4Ata Driver\n");
        }

        public void Finalize()
        {
        }

        public void Read(ulong diskByteOffset, [Out] IoMemory memory, int offset, int bytes)
        {
        }

        public void Write(ulong diskByteOffset, [In] IoMemory memory, int offset, int bytes)
        {
        }

        public void GetInfo(out DISK_INFO info)
        {
            info = new DISK_INFO();
        }
    }
}

