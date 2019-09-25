///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Dsdt.cs
//

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using Microsoft.Singularity.Io;

    public class Dsdt
    {
        public const string Signature = "DSDT";

        private IoMemory          region;
        private SystemTableHeader header;

        public Dsdt(IoMemory region, SystemTableHeader header)
        {
            this.region = region;
            this.header = header;
        }

        public IoMemory Region
        {
            get { return region; }
        }

        public static Dsdt Create(SystemTableHeader header)
        {
            IoMemory region = IoMemory.MapPhysicalMemory(header.PostHeaderAddress,
                                                         header.PostHeaderLength,
                                                         true, false);
            int sum = (header.Checksum + AcpiChecksum.Compute(region)) & 0xff;
            if (sum != 0) {
                return null;
            }
            return new Dsdt(region, header);
        }
    }

}
