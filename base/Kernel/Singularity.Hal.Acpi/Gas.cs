///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Gas.cs
//
//  Note:
//    Page 87 of ACPI 3.0 Spec.

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using Microsoft.Singularity.Io;

    public class Gas  // Generic Address Structure
    {
        // Address space id values
        public const byte SystemMemory            = 0;
        public const byte SystemIo                = 1;
        public const byte PciConfigSpace          = 2;
        public const byte EmbeddedController      = 3;
        public const byte SMBus                   = 4;
        public const byte FunctionalFixedHardware = 0x7f;

        private uint  properties;
        private ulong address;

        public Gas(uint properties, ulong address)
        {
            this.properties = properties;
            this.address = address;
        }

        public byte AddressSpaceId
        {
            get { return (byte) properties; }
        }

        public byte RegisterBitWidth
        {
            get { return (byte) (properties >> 8); }
        }

        public byte RegisterBitOffset
        {
            get { return (byte) (properties >> 16); }
        }

        public byte AccessSize
        {
            get { return (byte) (properties >> 24); }
        }

        public int AccessSizeBytes
        {
            get { return ((1 << AccessSize) >> 1); }
        }

        public ulong Address
        {
            get { return address; }
        }
    }
}
