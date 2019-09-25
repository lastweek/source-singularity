///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   SystemTableHeader.cs
//
//  Note:
//    Page 90 of ACPI 3.0 Spec.

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using Microsoft.Singularity.Io;

    public class SystemTableHeader
    {
        public const uint Length = 36;

        private IoMemory region;

        public SystemTableHeader(IoMemory region)
        {
            this.region = region;
        }

        // Returns a PHYSICAL address
        public UIntPtr Address
        {
            get { return region.PhysicalAddress.Value; }
        }

        public string Signature
        {
            get { return region.ReadAsciiZeroString(0, 4); }
        }

        public uint FullTableLength
        {
            get { return region.Read32(4); }
        }

        public uint PostHeaderLength
        {
            get { return FullTableLength - Length; }
        }

        // Returns a PHYSICAL address
        public UIntPtr PostHeaderAddress
        {
            get { return new UIntPtr ((uint)region.PhysicalAddress.Value + Length); }
        }

        public byte Checksum
        {
            get { return AcpiChecksum.Compute(region); }
        }

        public byte Revision
        {
            get { return region.Read8(8); }
        }

        public string OemId
        {
            get { return region.ReadAsciiZeroString(10, 6/*max length*/); }
        }

        public string OemTableId
        {
            get { return region.ReadAsciiZeroString(16, 8/*max length*/); }
        }

        public uint OemRevision
        {
            get { return region.Read32(24); }
        }

        public uint CreatorId
        {
            get { return region.Read32(28); }
        }

        public uint CreatorRevision
        {
            get { return region.Read32(32); }
        }

        public static SystemTableHeader Create(ulong address)
        {
            return new SystemTableHeader(
                IoMemory.MapPhysicalMemory(new UIntPtr(address), Length, true, false)
                );
        }
    }
}
