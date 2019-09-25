// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
//

using NetStack.Common;
using System;
using System.Diagnostics;

using System.Net.IP;
using Drivers.Net;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity;

#if !SINGULARITY
using System.Net;
using System.Net.Sockets;
#endif

namespace NetStack.Protocols
{
    ///
    // A UDP formatter class
    //
    public class UdpFormat
    {
        // size of UDP header
        public const int Size = 8;

        // a UDP header
        // (all header fields are given in host endianness)
        public struct UdpHeader
        {
            public ushort srcPort;
            public ushort dstPort;
            public ushort length;  // data+header
            public ushort checksum;
        }

        // construct a UDP header from a packet
        // if something is wrong, return the same start value
        public static int ReadUdpHeader(byte[]!       packet,
                                        int           udpOffset,
                                        out UdpHeader udpHeader)
        {
            // initialize an UdpHeader struct
            udpHeader = new UdpHeader();
            udpHeader.srcPort =
                (ushort)((int)(packet[udpOffset + 0] << 8) |
                         (int)(packet[udpOffset + 1]));
            udpHeader.dstPort =
                (ushort)((int)(packet[udpOffset + 2] << 8) |
                         (int)(packet[udpOffset + 3]));
            udpHeader.length =
                (ushort)((int)(packet[udpOffset + 4] << 8) |
                         (int)(packet[udpOffset + 5]));
            udpHeader.checksum =
                (ushort)((int)(packet[udpOffset + 6] << 8) |
                         (int)(packet[udpOffset + 7]));;
            return udpOffset + Size;
        }

        public static bool ReadUdpHeader(IBuffer!       buf,
                                         out UdpHeader  udpHeader)
        {
            udpHeader = new UdpHeader();
            if (buf.ReadNet16(out udpHeader.srcPort) &&
                buf.ReadNet16(out udpHeader.dstPort) &&
                buf.ReadNet16(out udpHeader.length)  &&
                buf.ReadNet16(out udpHeader.checksum))
            {
                return true;
            }
            return false;
        }

        // writes a UDP header to a packet
        // return the next place to write to
        // the checksum must be later calculated
        // (over all the octets of the pseudo header, UDP header and data)
        public static int WriteUdpHeader(byte[]!        buffer,
                                         int            offset,
                                         ref UdpHeader  header)
        {
            // check we have enough packet space
            if (buffer.Length - offset < Size)
                return offset;

            int o = offset;

            buffer[o++] = (byte)(((ushort)header.srcPort) >> 8);
            buffer[o++] = (byte)(((ushort)header.srcPort) & 0xff);

            buffer[o++] = (byte)(((ushort)header.dstPort) >> 8);
            buffer[o++] = (byte)(((ushort)header.dstPort) & 0xff);

            buffer[o++] = (byte)(((ushort)header.length) >> 8);
            buffer[o++] = (byte)(((ushort)header.length) & 0xff);

            // checksum
            buffer[o++] = 0;
            buffer[o++] = 0;

            return o;
        }

        // set the checksum field, totalSize covers all the fields for
        // which the checksum is calculated
        // offset is points to the beginning of the IP header (!!!)
        // Should be called after the UDP header + data have been written
        public static void SetUdpChecksum(byte[]!       packet,
                                          int           ipOffset,
                                          ref UdpHeader udpHeader)
        {
            // sum IP pseudo
            ushort ipPayloadSize = 0;
            ushort headerSum = IPFormat.SumPseudoHeader(packet, ipOffset,
                                                        ref ipPayloadSize);
            Debug.Assert(((ushort)udpHeader.length) == ipPayloadSize);

            // now add it to the udp header + data
            int ipHeaderSize = (packet[ipOffset] & 0xf) * 4;
            int udpOffset     = ipOffset + ipHeaderSize;

            Debug.Assert(packet[udpOffset + 6] == 0);
            Debug.Assert(packet[udpOffset + 7] == 0);

            ushort payloadSum = IPFormat.SumShortValues(packet, udpOffset,
                                                        ipPayloadSize);

            udpHeader.checksum = IPFormat.ComplementAndFixZeroChecksum(
                IPFormat.SumShortValues(headerSum, payloadSum));

            packet[udpOffset + 6] = (byte) (udpHeader.checksum >> 8);
            packet[udpOffset + 7] = (byte) (udpHeader.checksum & 0xff);
        }

        /// <summary>
        /// Compute checksum of UDP header.
        /// </summary>
        public static ushort SumHeader(UdpHeader udpHeader)
        {
            // Do not include existing checksum.
            int x = udpHeader.srcPort + udpHeader.dstPort + udpHeader.length;
            return (ushort) ((x >> 16) + x);
        }

        public static bool IsChecksumValid(IPFormat.IPHeader! ipHeader,
                                           UdpHeader          udpHeader,
                                           NetPacket!         payload)
        {
            // Compute partial checksums of headers
            ushort checksum  = IPFormat.SumPseudoHeader(ipHeader);
            checksum = IPFormat.SumShortValues(checksum,
                                               UdpFormat.SumHeader(udpHeader));

            // Checksum payload
            int length = payload.Available;
            int end = length & ~1;
            int i = 0;
            while (i != end) {
                int x = ((((int) payload.PeekAvailable(i++)) << 8) +
                         (int) payload.PeekAvailable(i++));

                checksum = IPFormat.SumShortValues(checksum, (ushort) x);
            }

            if (i != length) {
                int x = (((int) payload.PeekAvailable(i++)) << 8);
                checksum = IPFormat.SumShortValues(checksum, (ushort) x);
            }

            checksum = IPFormat.ComplementAndFixZeroChecksum(checksum);

            if (udpHeader.checksum != checksum) {
                DebugStub.WriteLine("Bad UDP checksum {0:x4} != {1:x4}",
                                  __arglist(udpHeader.checksum, checksum));
            }
            return udpHeader.checksum == checksum;
        }

        /// <summary>
        /// Write IP and UDP headers and payload data into a
        /// byte array.
        /// </summary>
        /// <param name="pkt">Array of bytes representing
        /// packet to be sent.</param>
        /// <param name="offset">Offset of IP Header within
        /// packet.</param>
        /// <param name="ipHeader">IP header to be written
        /// to packet.</param>
        /// <param name="udpHeader">UDP header to be written
        /// to packet.</param>
        /// <param name="payload">Payload of UDP Packet.</param>
        /// <param name="payloadOffset">The offset of start
        /// of the payload data within the payload
        /// array.</param>

        /// <param name="payloadLength">The size of the payload data.</param>
        public static void WriteUdpPacket(byte[]! pkt,
                                          int offset,
                                          IPFormat.IPHeader! ipHeader,
                                          ref UdpHeader udpHeader,
                                          byte[] payload,
                                          int payloadOffset,
                                          int payloadLength)
        {
            int udpStart = IPFormat.WriteIPHeader(pkt, offset, ipHeader);
            int udpEnd   = WriteUdpHeader(pkt, udpStart, ref udpHeader);

            if (pkt != payload || udpEnd != payloadOffset) {
                Array.Copy(payload, payloadOffset,
                           pkt, udpEnd, payloadLength);
            }
            SetUdpChecksum(pkt, offset, ref udpHeader);
        }

        public static void WriteUdpPacket(byte[]! pkt,
                                          int offset,
                                          IPFormat.IPHeader! ipHeader,
                                          ref UdpHeader udpHeader,
                                          byte[]! in ExHeap payload,
                                          int payloadOffset,
                                          int payloadLength)
        {
            int udpStart = IPFormat.WriteIPHeader(pkt, offset, ipHeader);
            int udpEnd   = WriteUdpHeader(pkt, udpStart, ref udpHeader);

            Bitter.ToByteArray(payload, payloadOffset, payloadLength,
                               pkt, udpEnd);
            SetUdpChecksum(pkt, offset, ref udpHeader);
        }

        public static void WriteUdpPacket(byte[]!   packet,
                                          int       ipOffset,
                                          IPv4      srcAddress,
                                          ushort    srcPort,
                                          IPv4      dstAddress,
                                          ushort    dstPort,
                                          byte[]    payload,
                                          int       payloadOffset,
                                          int       payloadLength)
        {
            IPFormat.IPHeader ipHeader = new IPFormat.IPHeader();

            ipHeader.SetDefaults(IPFormat.Protocol.UDP);

            ipHeader.Source      = srcAddress;
            ipHeader.Destination = dstAddress;
            ipHeader.totalLength = (ushort)(IPFormat.Size +
                                            UdpFormat.Size +
                                            payloadLength);

            UdpFormat.UdpHeader udpHeader = new UdpFormat.UdpHeader();
            udpHeader.srcPort = srcPort;
            udpHeader.dstPort = dstPort;
            udpHeader.length  = (ushort)(UdpFormat.Size + payloadLength);

            WriteUdpPacket(packet, ipOffset, ipHeader, ref udpHeader,
                           payload, payloadOffset, payloadLength);
        }

        public static void WriteUdpPacket(byte[]!   packet,
                                          int       ipOffset,
                                          IPv4      srcAddress,
                                          ushort    srcPort,
                                          IPv4      dstAddress,
                                          ushort    dstPort,
                                          byte[]! in ExHeap payload,
                                          int       payloadOffset,
                                          int       payloadLength)
        {
            IPFormat.IPHeader ipHeader = new IPFormat.IPHeader();

            ipHeader.SetDefaults(IPFormat.Protocol.UDP);

            ipHeader.Source      = srcAddress;
            ipHeader.Destination = dstAddress;
            ipHeader.totalLength = (ushort)(IPFormat.Size +
                                            UdpFormat.Size +
                                            payloadLength);

            UdpFormat.UdpHeader udpHeader = new UdpFormat.UdpHeader();
            udpHeader.srcPort = srcPort;
            udpHeader.dstPort = dstPort;
            udpHeader.length  = (ushort)(UdpFormat.Size + payloadLength);

            WriteUdpPacket(packet, ipOffset, ipHeader, ref udpHeader,
                           payload, payloadOffset, payloadLength);
        }
    }
}


