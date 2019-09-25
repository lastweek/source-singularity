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

#if !SINGULARITY
using System.Net;
using System.Net.Sockets;   // for AddressFamily
using System.Text.RegularExpressions;
using System.Runtime.InteropServices;
#endif

namespace NetStack.Protocols
{
    // An ethernet frame format
    public class EthernetFormat
    {
        // Ethernet protocol types:
        public const ushort PROTOCOL_IP    = 0x0800;
        public const ushort PROTOCOL_ARP   = 0x0806;
        public const ushort PROTOCOL_RARP  = 0x8035;
        public const ushort PROTOCOL_IP6   = 0x86dd;
        public const ushort PROTOCOL_PAUSE = 0x8808;  // must be sent to 01-80-C2-00-00-01
        public const ushort PROTOCOL_MAP   = 0x4934;  // unassigned according to http://map-ne.com/Ethernet/type.html
        public const ushort PROTOCOL_NLB   = 0x886f;  // Network Load Balancer - type allocated to Microsoft
        public const ushort PROTOCOL_LOOP  = 0x0060;   // Ethernet Loopback packet

        public const int MaxFrameSize = 1514;  // YW: wo CRC (which is 4 bytes)
        public const int MinFrameSize = 60;
        public const int Size = 14;

        public class FrameHeader
        {
            EthernetAddress origin;
            EthernetAddress target;
            ushort          protocol;

            public FrameHeader(EthernetAddress origin,
                               EthernetAddress target,
                               ushort          protocol)
            {
                this.origin   = origin;
                this.target   = target;
                this.protocol = protocol;
            }

            public FrameHeader()
            {
            }
        }

        // parse "pkt" from "start" bytes in, and return the
        // "src" and "dst" Ethernet addresses, and the protocol
        // "type" Returns the byte offset of the next layer's
        // header.
        public static int Read(byte []!            pkt,
                               int                 start,
                               out EthernetAddress src,
                               out EthernetAddress dst,
                               out ushort          type)
        {
            dst = EthernetAddress.ParseBytes(pkt, start);
            src = EthernetAddress.ParseBytes(pkt, start+6);
            type = (ushort) ((pkt[start+12] << 8) | (pkt[start+13]));
            return start + 14;
        }

        public static bool Read(IBuffer!            buf,
                                out EthernetAddress src,
                                out EthernetAddress dst,
                                out ushort          type)
        {
            bool b;
            b  = buf.ReadEthernetAddress(out dst);
            b &= buf.ReadEthernetAddress(out src);
            b &= buf.ReadNet16(out type);
            return b;
        }

        // Write an Ethernet header to "pkt", starting at position "start".
        public static int Write(byte[]! pkt,
                                int             start,
                                EthernetAddress src,
                                EthernetAddress dst,
                                ushort          type)
        {
            dst.CopyOut(pkt, start);
            src.CopyOut(pkt, start + EthernetAddress.Length);

            pkt[start + 12] = (byte) (type >> 8);
            pkt[start + 13] = (byte) (type & 0xff);

            return start + 14;
        }

        public static bool IsEthernetProtocol(ushort id)
        {
            switch (id) {
                case PROTOCOL_IP:     return true;
                case PROTOCOL_ARP:    return true;
                case PROTOCOL_RARP:   return true;
                case PROTOCOL_IP6:    return true;
                case PROTOCOL_PAUSE:  return true;
                case PROTOCOL_MAP:    return true;
                case PROTOCOL_NLB:    return true;
                case PROTOCOL_LOOP:   return true;
            }
            return false;
        }
    }
}
