// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
// Microsoft Research, Cambridge
//

using Microsoft.Singularity;
using NetStack.Common;
using System;
using System.Diagnostics;

#if !SINGULARITY
using System.Net;
// using System.Net.Sockets;   // for AddressFamily
#endif

using System.Net.IP;
using Drivers.Net;

namespace NetStack.Protocols
{
    public class IPFormat
    {
        // size of minimum IP header (wo options)
        public const int Size = 20;

        // all header fields are given in host endianness
        public class IPHeader
        {
            public byte   verLen; // 0:3 Version, 4:7 Header length in DWORDs.
            public byte   tos;
            public ushort totalLength;
            public ushort id;
            public ushort offset;
            public byte   ttl;
            public byte   protocol;
            public ushort checksum;
            internal IPv4  srcAddr;
            internal IPv4  destAddr;

            // some wrappers
            public IPv4 Source
            {
                get { return srcAddr; }
                set { srcAddr = value; }
            }

            public IPv4 Destination
            {
                get { return destAddr; }
                set { destAddr = value; }
            }

            public Protocol Protocol
            {
                get { return (Protocol) protocol; }
                set { protocol = (byte) value; }
            }

            // set default values
            public void SetDefaults(Protocol type)
            {
                verLen      = 0x45;    // version=4, header_len=5
                tos         = 0;
                totalLength = 0;
                id          = 0;
                offset      = 0;
                ttl         = DefaultTTL;
                protocol    = (byte)type;
                checksum    = 0;
                srcAddr     = IPv4.Zero;
                destAddr    = IPv4.Zero;
            }
        }

        // construct an IP header from a packet
        // if something is wrong, return the same start value
        public static bool ReadIPHeader(IBuffer! buf, out IPHeader! iphdr)
        {
            // initialize an IPHeader struct
            iphdr = new IPHeader();

            bool b;
            uint addr;

            b  = buf.Read8(out iphdr.verLen);
            b &= buf.Read8(out iphdr.tos);
            b &= buf.ReadNet16(out iphdr.totalLength);
            b &= buf.ReadNet16(out iphdr.id);
            b &= buf.ReadNet16(out iphdr.offset);
            b &= buf.Read8(out iphdr.ttl);
            b &= buf.Read8(out iphdr.protocol);
            b &= buf.ReadNet16(out iphdr.checksum);
            b &= buf.ReadNet32(out addr);
            iphdr.srcAddr = new IPv4(addr);
            b &= buf.ReadNet32(out addr);
            iphdr.destAddr = new IPv4(addr);
            return b;
        }

        // TTL default value
        public const byte DefaultTTL = 128;

        //  IP protocols identifiers
        public enum Protocol : byte
        {
            ICMP  = 1,
            IGMP  = 2,
            TCP   = 6,
            IGRP  = 9,
            UDP   = 17,
            GRE   = 47,
            ESP   = 50,
            AH    = 51,
            SKIP  = 57,
            EIGRP = 88,
            OSPF  = 89,
            L2TP  = 115
        }

        // some getters...
        public static ushort GetVersion(IPHeader! hdr)
        {
            return (ushort)(hdr.verLen & 0xF0);
        }

        // minimum value is 20, if it is 60 bytes, then
        // Options field is valid.
        public static uint GetHeaderLength(IPHeader! hdr)
        {
            return ((uint)(hdr.verLen & 0xF));
        }

        public static bool IsMoreFragSet(IPHeader! hdr)
        {
            ushort flags = (ushort)(((ushort)hdr.offset) >> 13);
            return ((flags & 0x01)==0x01);
        }

        public static bool IsDontFragSet(IPHeader! hdr)
        {
            ushort flags = (ushort)(((ushort)hdr.offset) >> 13);
            return ((flags & 0x02)==0x02);
        }

        public static void SetDontFragBit(IPHeader! hdr)
        {
            hdr.offset=(ushort)(hdr.offset|0x4000);
        }

        public static ushort GetFragOffset(IPHeader! hdr)
        {
            return (ushort)(hdr.offset & 0x1FFF);
        }

        // calculate's one's complement
        public static ushort SumShortValues(byte[]! buffer,
                                            int offset,
                                            int length)
        {
            //generate an IP checksum based on a given data buffer
            uint chksum = 0;

            int end = offset + (length & ~1);
            int i   = offset;
            while (i != end) {
                chksum += (uint)((((ushort)buffer[i++]) << 8) +
                                   (ushort)buffer[i++]);
            }

            if (i != offset + length) {
                // padding at the end!
                chksum += (uint)(((ushort)buffer[i]) << 8);
            }

            // Double-wrap chksum
            chksum = (chksum & 0xFFFF) + (chksum >> 16);
            chksum = (chksum & 0xFFFF) + (chksum >> 16);
            return (ushort)chksum;
        }

        public static ushort SumShortValues(ushort currentChecksum,
                                            ushort valueToAdd)
        {
            uint chksum = currentChecksum;
            chksum += valueToAdd;

            // Double-wrap chksum
            chksum = (chksum & 0xFFFF) + (chksum >> 16);
            chksum = (chksum & 0xFFFF) + (chksum >> 16);
            return (ushort)chksum;
        }

        public static ushort SumUInt16AndUInt32Values(ushort u16Part, uint u32Part)
        {
            u32Part += u16Part;

            // Double-wrap u32Part
            u32Part = (u32Part & 0xFFFF) + (u32Part >> 16);
            u32Part = (u32Part & 0xFFFF) + (u32Part >> 16);
            return (ushort)u32Part;
        }

        public static bool IsCheckSumOK(IPHeader! hdr)
        {
            ushort sum = (ushort) ((((int)hdr.verLen) << 8) + ((int)hdr.tos));
            sum = SumShortValues(sum, hdr.totalLength);
            sum = SumShortValues(sum, hdr.id);
            sum = SumShortValues(sum, hdr.offset);
            sum = SumShortValues(sum, (ushort) ((((int)hdr.ttl) << 8) + ((int)hdr.protocol)));
            sum = SumShortValues(sum, (ushort) (((uint)hdr.srcAddr) >> 16));
            sum = SumShortValues(sum, (ushort) (((uint)hdr.srcAddr) & 0xFFFFU));
            sum = SumShortValues(sum, (ushort) (((uint)hdr.destAddr) >> 16));
            sum = SumShortValues(sum, (ushort) (((uint)hdr.destAddr) & 0xFFFFU));

            sum = IPFormat.ComplementAndFixZeroChecksum(sum);

            if (sum != hdr.checksum) {
                DebugStub.WriteLine("Bad IP Checksum {0:x4} != {1:x4}",
                                  __arglist(hdr.checksum, sum));
            }

            return (sum == hdr.checksum);
        }

        // calculate the ip header checksum
        public static ushort Checksum(byte[]! buffer,
                                      int    ipHeaderOffset,
                                      int    ipHeaderLength)
        {
            unchecked {
                return (ushort)~SumShortValues(buffer,
                                               ipHeaderOffset,
                                               ipHeaderLength);
            }
        }

        // calc the sum of the 16bits pseudo header fields
        // (to be later used for transport level checksum calculation)
        // offset points to the start of the IP header
        // also return the protocolLength=header+data
        public static ushort SumPseudoHeader(byte[]!    pkt,
                                             int        offset,
                                             ref ushort protocolLength)
        {
            // source IP + destination IP
            uint sum = SumShortValues(pkt, offset + 12, 8);

            // add the protocol field (with zero MSB)
            sum += pkt[offset + 9];

            // add udp length = ip_total_length-ip_header_len
            ushort ipTotalLen = (ushort)(((ushort)(pkt[offset + 2] << 8)) |
                                         ((ushort)pkt[offset + 3]));
            //            ushort ipSize = (ushort)((pkt[offset] & 0x0f) * 4);
            protocolLength = (ushort)(ipTotalLen - IPFormat.Size);
            sum += protocolLength;

            // Double-wrap the sum
            sum = (sum & 0xFFFF) + (sum >> 16);
            sum = (sum & 0xFFFF) + (sum >> 16);
            return (ushort)sum;
        }

        public static ushort SumPseudoHeader(IPHeader! ipHeader)
        {
            uint sum = 0;
            uint origin = (uint)ipHeader.srcAddr;
            uint target = (uint)ipHeader.destAddr;

            sum  = (origin & 0xffff) + ((origin >> 16) & 0xffff);
            sum += (target & 0xffff) + ((target >> 16) & 0xffff);
            sum += ipHeader.protocol;
            sum += (ipHeader.totalLength - (ipHeader.verLen & 0xfu) * 4u);

            // Double-wrap the sum
            sum = (sum & 0xFFFF) + (sum >> 16);
            sum = (sum & 0xFFFF) + (sum >> 16);
            return (ushort)sum;
        }

        // writes an IP header to a packet
        // return the next place to write to, fixes the checksum field
        public static int WriteIPHeader(byte[]! pkt, int offset, IPHeader! hdr)
        {
            // check we have enough packet space
            if (pkt.Length - offset < Size)
                return offset;

            int o = offset;

            pkt[o++] = hdr.verLen;
            pkt[o++] = hdr.tos;
            pkt[o++] = (byte) (((ushort)hdr.totalLength) >> 8);
            pkt[o++] = (byte) (((ushort)hdr.totalLength) & 0xff);
            pkt[o++] = (byte) (((ushort)hdr.id) >> 8);
            pkt[o++] = (byte) (((ushort)hdr.id) & 0xff);
            pkt[o++] = (byte) (((ushort)hdr.offset) >> 8);
            pkt[o++] = (byte) (((ushort)hdr.offset) & 0xff);
            pkt[o++] = hdr.ttl;
            pkt[o++] = hdr.protocol;
            pkt[o++] = 0;
            pkt[o++] = 0;

            // set the ip addresses
            hdr.srcAddr.CopyOut(pkt, o);
            o += IPv4.Length;

            hdr.destAddr.CopyOut(pkt, o);
            o += IPv4.Length;

            // calculate checksum
            ushort chk = IPFormat.FixZeroChecksum(Checksum(pkt, offset, Size));
            pkt[offset + 10] = (byte) (((ushort)chk) >> 8);
            pkt[offset + 11] = (byte) (((ushort)chk) & 0xff);

            // save the header checksum
            hdr.checksum = chk;

            return o;
        }

        /// <summary>
        /// Update checksum when a 16-bit value that composed the original
        /// checksum changes.  Useful for recomputing checksum when
        /// TTL changes when acting as a router.
        /// </summary>
        public static ushort UpdateChecksum(ushort checksum,
                                            ushort oldValue,
                                            ushort newValue)
        {
            // From RFC1624
            ushort newChecksum;
            unchecked {
                newChecksum = (ushort)~checksum;
                newChecksum += (ushort)~oldValue;
                newChecksum += newValue;
            }
            return IPFormat.ComplementAndFixZeroChecksum(newChecksum);
        }

        internal static ushort ComplementAndFixZeroChecksum(ushort checksum)
        {
            unchecked {
                checksum = (ushort) ~checksum;
            }
            return (checksum == 0) ? (ushort)0xFFFF : checksum;
        }

        internal static ushort FixZeroChecksum(ushort checksum)
        {
            return (checksum == 0) ? (ushort)0xFFFF : checksum;
        }
    }
}
