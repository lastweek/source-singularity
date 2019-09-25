///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   AcpiTables.cs
//
//  Note:
//    Page 89 of ACPI 3.0 Spec.

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using Microsoft.Singularity.Io;

    internal class Rsdp
    {
        public const string Id = "RSD PTR ";

        private IoMemory region;

        public Rsdp(IoMemory region)
        {
            this.region = region;
        }

        public string Signature
        {
            get { return Id; }
        }

        public string OemId
        {
            get { return region.ReadAsciiZeroString(9, 6); }
        }

        public byte Revision
        {
            get { return region.Read8(15); }
        }

        public uint RsdtAddress
        {
            get { return region.Read32(16); }
        }

        public ulong XsdtAddress
        {
            get { return region.Read64(24); }
        }

        public uint Length
        {
            get { return region.Read32(20); }
        }

        public static Rsdp Parse(UIntPtr regionAddress,
                                          uint    regionBytes)
        {
            if (regionBytes >= 20) {
                IoMemory region = IoMemory.MapPhysicalMemory(regionAddress,
                                                             regionBytes,
                                                             true, false);

                if (AcpiChecksum.Compute(region, 0, 20) == 0 &&
                    region.ReadAsciiZeroString(0, 8) == Rsdp.Id)
                {
                    return new Rsdp(region);
                }
            }
            return null;
        }
    }
}
