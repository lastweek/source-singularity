///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PciConfig.cs
//
//  Note:
//

#define DEBUG_PCI

using System;
using StringBuilder = System.Text.StringBuilder;
using System.Collections;
using Microsoft.Singularity;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public class PciPort
    {
        private readonly IoPort addressPort;
        private readonly IoPort dataPort;
        private readonly ushort identifier;

        public PciPort(IoPort addressPort, IoPort dataPort, ushort identifier)
        {
            this.addressPort = addressPort;
            this.dataPort = dataPort;
            this.identifier = identifier;
        }

        public ushort Identifier { get { return this.identifier; } }

        public ushort Function
        {
            get { return (ushort)(Identifier & ((1 << 3) - 1)); }
        }

        public ushort Device
        {
            get { return (ushort)((Identifier >> 3) & ((1 << 5) - 1)); }
        }

        public ushort Bus
        {
            get { return (ushort)(Identifier >> 8); }
        }

        public virtual uint Read32(int offset)
        {
            if ((offset & 0x3) != 0) {
                throw new Exception("BAD_OFFSET");
            }

            uint config = (((uint)offset & 0xfc) |
                           ((uint)identifier << 8) |
                           ((uint)1 << 31));

            addressPort.Write32(config);
            return dataPort.Read32();
        }

        public virtual ushort Read16(int offset)
        {
            if ((offset & 0x1) != 0) {
                throw new Exception("BAD_OFFSET");
            }

            uint config = (((uint)offset & 0xfc) |
                           ((uint)identifier << 8) |
                           ((uint)1 << 31));

            addressPort.Write32(config);
            return dataPort.Read16((uint)(offset & 0x2));
        }

        public virtual byte Read8(int offset)
        {
            uint config = (((uint)offset & 0xfc) |
                           ((uint)identifier << 8) |
                           ((uint)1 << 31));

            addressPort.Write32(config);
            return dataPort.Read8((uint)(offset & 0x3));
        }

        public virtual void Write32(int offset, uint value)
        {
            if ((offset & 0x3) != 0) {
                throw new Exception("BAD_OFFSET");
            }

            uint config = (((uint)offset & 0xfc) |
                           ((uint)identifier << 8) |
                           ((uint)1 << 31));

            addressPort.Write32(config);
            dataPort.Write32(value);
        }

        public virtual void Write16(int offset, ushort value)
        {
            if ((offset & 0x1) != 0) {
                throw new Exception("BAD_OFFSET");
            }

            uint config = (((uint)offset & 0xfc) |
                           ((uint)identifier << 8) |
                           ((uint)1 << 31));

            addressPort.Write32(config);
            dataPort.Write16((uint)(offset & 0x2), value);
        }

        public virtual void Write8(int offset, byte value)
        {
            uint config = (((uint)offset & 0xff) |
                           ((uint)identifier << 8) |
                           ((uint)1 << 31));

            addressPort.Write32(config);
            dataPort.Write8((uint)(offset & 0x3), value);
        }
    }
} // end namespace Microsoft.Singularity.Io
