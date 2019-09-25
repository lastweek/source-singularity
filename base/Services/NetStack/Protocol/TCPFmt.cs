// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
//

using Microsoft.Singularity;
using NetStack.Common;
using System;
using System.Diagnostics;

using System.Net.IP;
using Drivers.Net;

#if !SINGULARITY
using System.Net;
using System.Net.Sockets;
#endif

namespace NetStack.Protocols
{
    ///
    // A TCP formatter class
    //

    public class TcpFormat
    {
        // size of minimum TCP header (wo options)
        public const int Size = 20;

        // default IP MSS
        public const int IP_DEFAULT_MTU=576; // wo negotiation
        public const int IP_MTU=1500;

        // available TCP MSS
        public const int TCP_MSS=IP_MTU-IPFormat.Size-Size;

        // all header fields are given in host endianness
        public struct TcpHeader
        {
            public ushort sourcePort;
            public ushort destPort;
            public uint  seq;
            public uint  ackSeq;
            public byte  off_res1;       // number of 32-bit words, min=5
            public byte  res2_flags;
            public ushort window;
            public ushort checksum;
            public ushort urgPtr;
        }

        // TCP states
        public enum TCPState
        {
            TCP_ESTABLISHED = 1,
            TCP_SYN_SENT,
            TCP_SYN_RECV,
            TCP_FIN_WAIT1,
            TCP_FIN_WAIT2,
            TCP_TIME_WAIT,
            TCP_CLOSE,
            TCP_CLOSE_WAIT,
            TCP_LAST_ACK,
            TCP_LISTEN,
            TCP_CLOSING,
            TCP_MAX_STATES // Leave at the end!
        };

        // construct a TCP header from a packet
        // if something is wrong, return the same start value
        public static bool ReadTcpHeader(IBuffer! buf, out TcpHeader tcphdr)
        {
            // initialize an TcpHeader struct
            tcphdr = new TcpHeader();

            bool b;
            b  = buf.ReadNet16(out tcphdr.sourcePort);
            b &= buf.ReadNet16(out tcphdr.destPort);
            b &= buf.ReadNet32(out tcphdr.seq);
            b &= buf.ReadNet32(out tcphdr.ackSeq);
            b &= buf.Read8(out tcphdr.off_res1);
            b &= buf.Read8(out tcphdr.res2_flags);
            b &= buf.ReadNet16(out tcphdr.window);
            b &= buf.ReadNet16(out tcphdr.checksum);
            b &= buf.ReadNet16(out tcphdr.urgPtr);
            return b;
        }

        //  TCP well known server ports
        public enum ReservedPort
        {
            ECHO        = 7,
            CHARGEN     = 19,
            FTP_DATA    = 20,
            FTP_CONTROL = 21,
            SSH         = 22,
            TELNET      = 23,
            SMTP        = 25,
            DOMAIN      = 53,
            FINGER      = 79,
            HTTP        = 80,
            POP3        = 110,
            SUNRPC      = 111,
            NNTP        = 119,
            NETBIOS_SSN = 139,
            IMAP        = 111,
            BGP         = 179,
            LDAP        = 389,
            HTTPS       = 443,
            MSDS        = 445,
            SOCKS       = 1080
        }

        // some getters...
        public static byte GetOffset(ref TcpHeader hdr)
        {
            // return the header len (32 bit counter)
            return ((byte)((hdr.off_res1>>4) & 0x0F));   // 4 bits
        }

        public static byte GetReserve1(ref TcpHeader hdr)
        {
            return ((byte)(hdr.off_res1&0x0F));  // 4 bits
        }

        public static byte GetReserve2(ref TcpHeader hdr)
        {
            return ((byte)((hdr.res2_flags>>6) & 0x03)); // 2 bits
        }

        // The flags: "UAPRSF"

        // urgent pointer valid
        public static bool IsUrg(ref TcpHeader hdr)
        {
            return (((hdr.res2_flags>>5) & 0x01)==1); // 1 bits
        }

        // ack filed is valid
        public static bool IsAck(ref TcpHeader hdr)
        {
            return (((hdr.res2_flags>>4) & 0x01)==1); // 1 bits
        }

        // set ack
        public static void SetACK(ref TcpHeader hdr)
        {
            hdr.res2_flags=(byte)(hdr.res2_flags|16);

        }

        // push data
        public static bool IsPush(ref TcpHeader hdr)
        {
            return (((hdr.res2_flags>>3) & 0x01)==1); // 1 bits
        }

        // reset connection
        public static bool IsReset(ref TcpHeader hdr)
        {
            return (((hdr.res2_flags>>2) & 0x01)==1); // 1 bits
        }

        // set reset bit
        public static void SetReset(ref TcpHeader hdr)
        {
            hdr.res2_flags=(byte)(hdr.res2_flags|0x4);
        }

        // synchronize sequence numbers
        public static bool IsSync(ref TcpHeader hdr)
        {
            return (((hdr.res2_flags>>1) & 0x01)==1); // 1 bits
        }

        // set syn
        public static void SetSYN(ref TcpHeader hdr)
        {
            hdr.res2_flags=(byte)(hdr.res2_flags|2);
        }

        // set fin
        public static void SetFIN(ref TcpHeader hdr)
        {
            hdr.res2_flags=(byte)(hdr.res2_flags|1);
        }

        // no more data ; finish connection
        public static bool IsFIN(ref TcpHeader hdr)
        {
            return ((hdr.res2_flags & 0x01)==1); // 1 bits
        }

        // writes a TCP header to a packet
        // return the next place to write to
        // the checksum must be later calculated and cover the
        // pseudoheader and entire TCP segment
        public static int WriteTcpHeader(byte[]! pkt, int offset, ref TcpHeader hdr)
        {
            // check we have enough packet space
            if (pkt.Length - offset < Size)
                return offset;

            int o = offset;

            pkt[o++] = (byte)(((ushort)hdr.sourcePort) >> 8);
            pkt[o++] = (byte) (((ushort)hdr.sourcePort) & 0xff);

            pkt[o++] = (byte)(((ushort)hdr.destPort) >> 8);
            pkt[o++] = (byte) (((ushort)hdr.destPort) & 0xff);

            pkt[o++] = (byte)(((uint)hdr.seq) >> 24);
            pkt[o++] = (byte)(((uint)hdr.seq) >> 16);
            pkt[o++] = (byte)(((uint)hdr.seq) >> 8);
            pkt[o++] = (byte) (((uint)hdr.seq) & 0xff);

            pkt[o++] = (byte)(((uint)hdr.ackSeq) >> 24);
            pkt[o++] = (byte)(((uint)hdr.ackSeq) >> 16);
            pkt[o++] = (byte)(((uint)hdr.ackSeq) >> 8);
            pkt[o++] = (byte) (((uint)hdr.ackSeq) & 0xff);

            pkt[o++] = hdr.off_res1;
            pkt[o++] = hdr.res2_flags;

            pkt[o++] = (byte)(((ushort)hdr.window) >> 8);
            pkt[o++] = (byte) (((ushort)hdr.window) & 0xff);

            // checksum
            pkt[o++] = 0;
            pkt[o++] = 0;

            pkt[o++] = (byte)(((ushort)hdr.urgPtr) >> 8);
            pkt[o++] = (byte) (((ushort)hdr.urgPtr) & 0xff);

            return o;
        }

        // set the checksum field
        // offset points to the beginning of the IP header (!!!)
        // Should be called after the TCP header + data have been written
        public static void SetTcpChecksum(byte[]!       packet,
                                          int           ipOffset,
                                          ref TcpHeader tcpHeader)
        {
            // sum IP pseudo
            ushort ipPayloadLength = 0;
            ushort headerSum =
                IPFormat.SumPseudoHeader(packet, ipOffset,
                                         ref ipPayloadLength);

            int ipHeaderSize = (packet[ipOffset] & 0xf) * 4;
            int tcpOffset    = ipOffset + ipHeaderSize;

            Debug.Assert(packet[tcpOffset + 16] == 0);
            Debug.Assert(packet[tcpOffset + 17] == 0);

            // now add it to the TCP header + data
            ushort payloadSum = IPFormat.SumShortValues(packet, tcpOffset,
                                                        ipPayloadLength);

            tcpHeader.checksum = (ushort)
                ~(IPFormat.SumShortValues(headerSum, payloadSum));

            // Complement and change +0 to -0 if needed.
            ushort tcpChecksum = IPFormat.ComplementAndFixZeroChecksum(
                (IPFormat.SumShortValues(headerSum, payloadSum)));

            tcpHeader.checksum = tcpChecksum;

            unchecked {
                packet[tcpOffset + 16] = (byte) (tcpChecksum >> 8);
                packet[tcpOffset + 17] = (byte) (tcpChecksum >> 0);
            }
        }

        public static ushort SumHeader(TcpHeader tcpHeader)
        {
            int checksum = tcpHeader.sourcePort;
            checksum += tcpHeader.destPort;
            checksum += (int) (tcpHeader.seq >> 16);
            checksum += (int) (tcpHeader.seq & 0xffff);
            checksum += (int) (tcpHeader.ackSeq >> 16);
            checksum += (int) (tcpHeader.ackSeq & 0xffff);
            checksum += (((int)tcpHeader.off_res1) << 8) | (int)tcpHeader.res2_flags;
            checksum += (int) tcpHeader.window;
            checksum += (int) tcpHeader.urgPtr;

            // Double-wrap checksum
            checksum = (checksum & 0xFFFF) + (checksum >> 16);
            checksum = (checksum & 0xFFFF) + (checksum >> 16);
            return (ushort)checksum;
        }

        public static bool IsChecksumValid(IPFormat.IPHeader! ipHeader,
                                           TcpHeader          tcpHeader,
                                           NetPacket!         payload)
        {
            // Compute partial checksums of headers
            ushort checksum = IPFormat.SumPseudoHeader(ipHeader);
            checksum = IPFormat.SumShortValues(checksum,
                                               SumHeader(tcpHeader));

            // Checksum payload (without potential odd byte)
            int length = payload.Available;
            int end = length & ~1;
            int i = 0;
            uint payloadChecksum = 0;
            while (i != end) {
                byte b0 = payload.PeekAvailable(i++);
                byte b1 = payload.PeekAvailable(i++);
                payloadChecksum += ((((uint) b0) << 8) + (uint) b1);
            }

            // Handle odd byte.
            if (i != length) {
                payloadChecksum += (((uint) payload.PeekAvailable(i++)) << 8);
            }

            // Merge bits from payload checksum
            checksum = IPFormat.SumUInt16AndUInt32Values(checksum, payloadChecksum);

            // Complement and change +0 to -0 if needed.
            checksum = IPFormat.ComplementAndFixZeroChecksum(checksum);

            // Check for match.
            bool checksumMatch = (tcpHeader.checksum == checksum);

            // If checksum error, unconditionally output message to debugger.
            if (checksumMatch == false) {
                DebugStub.WriteLine("Bad TCP checksum {0:x4} != {1:x4}:  SEQ {2:x8}  ACK {3:x8}",
                    __arglist(tcpHeader.checksum, checksum,
                        tcpHeader.seq,
                        tcpHeader.ackSeq
                    ));
            }

            // IsValid is a Match.
            return checksumMatch;
        }

        // a helper method to write the TCP segment (without data)
        public static void WriteTcpSegment(byte[]! pktData,
                                           ushort localPort,
                                           ushort destPort,
                                           uint   ackSeq,
                                           uint   seq,
                                           ushort wnd,
                                           IPv4   sIP,
                                           IPv4   dIP,
                                           ushort dataLen,
                                           bool   isAck,
                                           bool   isSyn,
                                           bool   isRst,
                                           bool   isFin,
                                           bool   withOptions)
        {
            // now create the IP,TCP headers!
            int start=EthernetFormat.Size;

            // prepare it...
            TcpFormat.TcpHeader tcpHeader = new TcpFormat.TcpHeader();
            tcpHeader.sourcePort       = localPort;
            tcpHeader.destPort         = destPort;
            if (withOptions) {
                tcpHeader.off_res1 = 0x60;
            }
            else {
                tcpHeader.off_res1 = 0x50;
            }

            tcpHeader.ackSeq = ackSeq;
            tcpHeader.seq    = seq;
            tcpHeader.window = wnd;

            if (isFin) {
                TcpFormat.SetFIN(ref tcpHeader);
            }
            if (isSyn) {
                TcpFormat.SetSYN(ref tcpHeader);
            }
            if (isAck) {
                TcpFormat.SetACK(ref tcpHeader);
            }
            if (isRst) {
                TcpFormat.SetReset(ref tcpHeader);
            }

            IPFormat.IPHeader ipHeader = new IPFormat.IPHeader();
            ipHeader.SetDefaults(IPFormat.Protocol.TCP);
            ipHeader.totalLength = (ushort)(IPFormat.Size + TcpFormat.Size+dataLen);
            ipHeader.srcAddr = sIP;
            ipHeader.destAddr = dIP;
            IPFormat.SetDontFragBit(ipHeader);

            // write the ip header + ip checksum
            start = IPFormat.WriteIPHeader(pktData, start, ipHeader);

            // write TCP header, no checksum
            start = TcpFormat.WriteTcpHeader(pktData, start, ref tcpHeader);

            // calc the checksum...
            TcpFormat.SetTcpChecksum(pktData, EthernetFormat.Size, ref tcpHeader);
        }

#if SINGULARITY
        private static long snBase = 133413;

        public static int GenerateSequenceNumber(IPv4 localHost,
                                                 IPv4 remoteHost,
                                                 ushort    localPort,
                                                 ushort    remotePort)
        {
            // No MD5 for now so perform a weak hash
            long isn = DateTime.UtcNow.Ticks;

            snBase = snBase + 2287 * snBase;
            isn += snBase;

            int i = 0;
            foreach (byte b in localHost.GetAddressBytes()) {
                isn ^= ((long)b) << i;
                i += 8;
            }

            foreach (byte b in localHost.GetAddressBytes()) {
                isn ^= ((long)b) << i;
                i += 8;
            }

            isn += (localPort << 16) | remotePort;
            return (int)((isn >> 32) ^ isn);
        }
#else
        public static int GenerateSequenceNumber(IPAddress localHost,IPAddress remoteHost,
                                                 ushort localPort,ushort remotePort)
        {
            // generate safer initial sequence numbers (RFC 1948)
            // ISN = M + F(localhost, localport, remotehost, remoteport).

            byte[] data=new byte[12];
            Array.Copy(localHost.GetAddressBytes(),0,data,0,4);
            Array.Copy(remoteHost.GetAddressBytes(),0,data,4,4);
            data[8]=(byte)(localPort>>8);
            data[9]=(byte)localPort;
            data[10]=(byte)(remotePort>>8);
            data[11]=(byte)remotePort;

            System.Security.Cryptography.MD5 md5 = new System.Security.Cryptography.MD5CryptoServiceProvider();
            byte[] result = md5.ComputeHash(data);
            string hashString = Convert.ToBase64String(result);
            return (int)(Convert.ToInt64(hashString,10)+(uint)DateTime.UtcNow.Ticks);
        }
#endif
    }
}
