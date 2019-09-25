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

#if !SINGULARITY
using System.Net;
#endif

using System.Net.IP;
using Drivers.Net;

namespace NetStack.Protocols
{
    ///
    // declaration of the ICMP header (RFC 792)
    // 
    public class IcmpFormat
    {
        // size of common ICMP header
        public const int Size = 8;

        // ICMP Types
        public enum IcmpType
        {
            ECHO_REPLY=0,
            DESTINATION_UNREACHABLE=3,
            SOURCE_QUENCH=4,
            REDIRECT_MESSAGE=5,
            ECHO_REQUEST=8,
            TIME_EXCEEDED=11,
            PARAMETER_PROBLEM=12,
            TIMESTAMP_REQUEST=13,
            TIMESTAMP_REPLY=14,
            INFO_REQUEST=15,
            INFO_REPLY=16,
            ADD_MASK_REQUEST=17,
            ADD_MASK_REPLY=18
        }

        // Destination Unreachable Codes
        public enum Type3Code
        {
            NET_UNREACHABLE=0,
            HOST_UNREACHABLE=1,
            PROT_UNREACHABLE=2
            // and some more, let's add as needed   
        }

        // the common ICMP header
        public struct IcmpHeader
        {
            public byte    type;
            public byte    code;
            public ushort  chksum;
            public ushort  id;
            public ushort  seq;
        }

        // write common ICMP header
        // (ignores the checksum field, notice that the checksum is
        //  calculated for the whole packet!)
        public static int WriteIcmpHeader(byte[]! pkt,int offset,ref IcmpHeader hdr)
        {
            int o    = offset;
            pkt[o++] = hdr.type;
            pkt[o++] = hdr.code;
            pkt[o++] = 0;
            pkt[o++] = 0;
            pkt[o++] = (byte)(hdr.id>>8);
            pkt[o++] = (byte)hdr.id;
            pkt[o++] = (byte)(hdr.seq>>8);
            pkt[o++] = (byte)hdr.seq;

            return o;
        }

        // construct an ICMP header from a packet
        public static bool ReadIcmpHeader(IBuffer! buf, out IcmpHeader hdr)
        {
            bool b;
            b  = buf.Read8(out hdr.type);
            b &= buf.Read8(out hdr.code);
            b &= buf.ReadNet16(out hdr.chksum);
            b &= buf.ReadNet16(out hdr.id);
            b &= buf.ReadNet16(out hdr.seq);
            return b;
        }

        // Timestamp or Timestamp Reply Message
        public struct TimeStamps
        {
            public IcmpHeader header;
            public uint origTimeStamp;
            public uint rcvTimeStamp;
            public uint txTimeStamp;
        }

        // various ICMP messages

        // IcmpEchoRequest
        public struct IcmpEchoRequest
        {
            public IcmpHeader  header;
            public byte[]  data;

            // get the size of the message (depends on the received data)
            public int GetSize()
            {
                return (IcmpFormat.Size+data.Length);
            }

            // ctor
            public IcmpEchoRequest(ref IcmpHeader hdr,byte[]! msgData)
            {
                header=hdr;

                // set the data
                data = new byte[msgData.Length];
                Array.Copy(msgData,0,data,0,msgData.Length);
            }

            public IcmpEchoRequest(ushort id,ushort seq,byte[]! msgData)
            {
                header.type   = (byte)IcmpFormat.IcmpType.ECHO_REQUEST;
                header.code   = 0;
                header.chksum = 0;
                header.seq    = seq;
                header.id     = id;
                // set the data
                data          = new byte[msgData.Length];
                Array.Copy(msgData,0,data,0,msgData.Length);
            }

            // write an ICMP echo request
            public static int WriteIcmpEchoRequest(byte[]! pkt,int offset,ref IcmpEchoRequest request)
            {
                int o = offset;
                // write the common header
                o = WriteIcmpHeader(pkt,offset,ref request.header);

                // dump the data (endian doesn't matter, since it is a user data)
                Array.Copy(request.data,0,pkt,o,request.data.Length);

                // calc the checksum
                ushort chk        = IPFormat.Checksum(pkt, offset,
                                                      request.GetSize());
                pkt[offset+2]     = (byte) (((ushort)chk) >> 8);
                pkt[offset+3]     = (byte) (((ushort)chk) & 0xff);
                request.header.chksum = chk;

                return o;
            }

            // write an ICMP echo reply for an ICMP Echo request
            public static int WriteIcmpEchoReply(byte[]! pkt,int offset,ref IcmpEchoRequest request)
            {
                int o = offset;

                // change the request header code to 0
                request.header.type = (byte)IcmpFormat.IcmpType.ECHO_REPLY;
                // write the common header
                o = WriteIcmpHeader(pkt,offset,ref request.header);
                // fix it again
                request.header.type = (byte)IcmpFormat.IcmpType.ECHO_REQUEST;

                // dump the data (endian doesn't matter, since it is a user data)
                Array.Copy(request.data,0,pkt,o,request.data.Length);

                // calc the checksum
                ushort chk = IPFormat.Checksum(pkt,offset,request.GetSize());
                pkt[offset + 2] = (byte) (((ushort)chk) >> 8);
                pkt[offset + 3] = (byte) (((ushort)chk) & 0xff);
                request.header.chksum = chk;

                return o;
            }
        }

        // a fast method that uses that modified the ECHO request
        // packet to an ECHO reply.
        // return true if success
        public static void CreateFastEchoReply(byte[]! pkt,int icmpPacketSize)
        {
            // 1. switch the source IP and destination IP
            // 2. change ICMP code to IcmpFormat.IcmpType.ECHO_REPLY
            // 3. should use ARP table to find out the mac address of the target
            //    (if it is on the local network)
            //    CURRENTLY: just switch MAC addresses as well.
            // 4. recompute ICMP and IP checksums

            int    ipStart   = EthernetFormat.Size;
            int    icmpStart = ipStart + IPFormat.Size;
            pkt[icmpStart]   = (byte)IcmpFormat.IcmpType.ECHO_REPLY;
            // zero checksum
            pkt[icmpStart + 2] = 0;
            pkt[icmpStart + 3] = 0;
            ushort chk       = IPFormat.Checksum(pkt, icmpStart, icmpPacketSize);
            pkt[icmpStart + 2] = (byte)(chk>>8);
            pkt[icmpStart + 3] = (byte)chk;

            // switch IPs
            byte[] tmp = new byte[6];
            Array.Copy(pkt, ipStart + 16, tmp, 0, 4); // dest->tmp
            Array.Copy(pkt, ipStart + 12, pkt, ipStart + 16, 4); // src->dest
            Array.Copy(tmp, 0, pkt, ipStart + 12, 4); // tmp->src

            // zero the checksum
            pkt[ipStart + 10] = 0;
            pkt[ipStart + 11] = 0;

            // calculate checksum
            chk = IPFormat.Checksum(pkt, ipStart, IPFormat.Size);
            pkt[ipStart + 10] = (byte) (((ushort)chk) >> 8);
            pkt[ipStart + 11] = (byte) (((ushort)chk) & 0xff);

            // TBC: currently just switch mac addresses
            Array.Copy(pkt, 6, tmp, 0, 6);  // src  -> temp
            Array.Copy(pkt, 0, pkt, 6, 6);  // dest -> src
            Array.Copy(tmp, 0, pkt, 0, 6);  // tmp  -> dest
        }
    }
}
