///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Rsdt.cs
//
//  Note:
//    Page 93 of ACPI 3.0 Spec.

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using Microsoft.Singularity.Io;
    public class Rsdt
    {
        protected IoMemory          region;
        private SystemTableHeader header;

        protected Rsdt(IoMemory region, SystemTableHeader header)
        {
            this.region = region;
            this.header = header;
        }

        public virtual int EntryCount { get { return region.Length / 4; } }

        public virtual ulong GetEntry(int index)
        {
            index *= 4;
            if (index > region.Length)
                return 0;
            return region.Read32(index);
        }

        public SystemTableHeader GetTableHeader(int index)
        {
            ulong address = GetEntry(index);
            if (address == 0)
                return null;
            return SystemTableHeader.Create(address);
        }

        public static Rsdt Create(SystemTableHeader header)
        {
            DebugStub.Assert(header.Signature == "RSDT");
            return new Rsdt(
                IoMemory.MapPhysicalMemory(
                    header.PostHeaderAddress, header.PostHeaderLength,
                    true, false
                    ),
                header
                );
        }
    }

    public class Xsdt : Rsdt
    {
        private Xsdt(IoMemory region, SystemTableHeader header)
            : base(region, header)
        {
            // Nothing to do
        }

        public override int EntryCount { get { return region.Length / 8; } }

        public override ulong GetEntry(int index)
        {
            index *= 8;
            if (index > region.Length)
                return 0;
            return region.Read64(index);
        }

        public new static Xsdt Create(SystemTableHeader header)
        {
            DebugStub.Assert(header.Signature == "XSDT");
            return new Xsdt(
                IoMemory.MapPhysicalMemory(
                    header.PostHeaderAddress, header.PostHeaderLength,
                    true, false
                    ),
                header
                );
        }
    }
}
