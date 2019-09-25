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

namespace NetStack.Protocols
{
    ///
    // declarations of an ARP message, RFC 826
    // 
    public class ArpFormat
    {
        // arp operations:
        public enum Type
        {
            ARP_REQUEST  = 1,
            ARP_REPLY    = 2
        }

        // ARP message size (for ethernet and IP only)
        public const int Size = 28;

        // methods:
        public static int Write(byte []!        pkt,
                                int             offset,
                                EthernetAddress srchw,
                                IPv4            srcip,
                                Type            operation,
                                EthernetAddress targethw,
                                IPv4            targetip)
        {
            int o = offset;

            pkt[o++] = 0x00; pkt[o++] = 0x01;  // hardware type = 0x0001
            pkt[o++] = 0x08; pkt[o++] = 0x00;  // protocol type = 0x0800
            pkt[o++] = 0x06; // hardware addr len (bytes)
            pkt[o++] = 0x04; // protocol address len (bytes)
            pkt[o++] = (byte) (((ushort)operation) >> 8);
            pkt[o++] = (byte) (((ushort)operation) & 0xff);

            srchw.CopyOut(pkt, o);
            o += EthernetAddress.Length;

            srcip.CopyOut(pkt, o);
            o += IPv4.Length;

            targethw.CopyOut(pkt, o);
            o += EthernetAddress.Length;

            targetip.CopyOut(pkt, o);
            o += IPv4.Length;

            return o;
        }

        // Parse "pkt" from "start" bytes in,
        // and return the sender and target Ethernet addresses, and the
        // sender and target IP addresses, along with the "opcode".
        // These may be null if the packet wasn't an ARP for 6-byte Ethernet addresses.
        // Returns the byte offset of the next layer's header.
        public static bool Read(IBuffer!            buf,
                                out Type            opcode,
                                out EthernetAddress senderhw,
                                out IPv4            senderip,
                                out EthernetAddress targethw,
                                out IPv4            targetip)
        {
            opcode   = Type.ARP_REQUEST;
            senderhw = targethw = EthernetAddress.Zero;
            senderip = targetip = IPv4.Zero;

            // check hardware type == 0x0001 (Ethernet)
            ushort hwtype;
            if (buf.ReadNet16(out hwtype) == false || hwtype != 0x1) {
                return false;
            }

            // check protocol type == 0x0800 (IP)
            ushort proto;
            if (buf.ReadNet16(out proto) == false || proto != 0x0800) {
                return false;
            }

            // check hardware address len is 6 bytes

            byte hwlen;
            if (buf.Read8(out hwlen) == false || hwlen != 6) {
                return false;
            }

            // check IP address len is 4 bytes
            byte prlen;
            if (buf.Read8(out prlen) == false || prlen != 4) {
                return false;
            }

            // Read stuff
            // operation code
            ushort temp;
            if (buf.ReadNet16(out temp) == false) {
                return false;
            }
            opcode = (Type)temp;

            if (buf.ReadEthernetAddress(out senderhw) == false) {
                return false;
            }

            uint addr;
            if (buf.ReadNet32(out addr) == false) {
                return false;
            }
            senderip = new IPv4(addr);

            // target HW & IP
            if (buf.ReadEthernetAddress(out targethw) == false) {
                return false;
            }

            if (buf.ReadNet32(out addr) == false) {
                return false;
            }
            targetip = new IPv4(addr);
            return true;
        }

        // creates an arp reply using the received packet
        // the packet must be an arp request
        // the responder should pass its own IP and MAC address
        // we assume that we have the same hw type
        // (return offset_arp size)
        public static int CreateArpReply(ref byte[]!     pkt,
                                         IPv4            selfIP,
                                         EthernetAddress selfMACAddr)
        {
            int offset = 14;           // arp message starts here.
            int o      = offset;

            // check we have enough packet
            if (pkt.Length - offset < Size)
                return offset;

            // check hardware type == 0x0001 (Ethernet)
            if (pkt[o++] != 0x00 || pkt[o++] != 0x01)
                return offset;

            // check protocol type == 0x0800 (IP)
            if (pkt[o++] != 0x08 || pkt[o++] != 0x00)
                return offset; // error

            // check addresses len
            if (pkt[o++] != 0x06)
                return offset;

            if (pkt[o++] != 0x04)
                return offset;

            // operation code
            Type opcode = (Type)(((int)pkt[o++] << 8) | (int)pkt[o++]);

            // we need a request message.
            if (opcode != Type.ARP_REQUEST)
                return offset;

            // sender HW & IP
            EthernetAddress senderhw = EthernetAddress.ParseBytes(pkt, o);
            o += EthernetAddress.Length;

            IPv4 senderIP = IPv4.ParseBytes(pkt, o);
            o += IPv4.Length;

            // target HW & IP
            // EthernetAddress targethw = EthernetAddress.ParseBytes(pkt, o);
            o += EthernetAddress.Length;

            // IPv4 targetIP = IPv4.ParseBytes(pkt, o);
            o += IPv4.Length;

            // all is well, do our stuff...
            // 1. set local hw address to arp's source ether address + fix dest addresses
            // 2. set arp type = ARP_REPLY
            // 3. set the destination's ethernet address to self
            //    and target is the source of the request.

            o = offset+6;  // opcode entry
            pkt[o++] = (byte)(((ushort)Type.ARP_REPLY) >> 8);
            pkt[o++] = (byte)Type.ARP_REPLY;

            // set hw and IP address
            selfMACAddr.CopyOut(pkt, o);
            o += EthernetAddress.Length;

            selfIP.CopyOut(pkt, o);
            o += IPv4.Length;

            // setup dest address to the requesting host address
            senderhw.CopyOut(pkt, o);
            o += EthernetAddress.Length;

            senderIP.CopyOut(pkt, o);
            o += IPv4.Length;

            // set ethernet level addresses
            Array.Copy(pkt, 6, pkt, 0, 6);  // src  -> dest
            selfMACAddr.CopyOut(pkt, 6);    // self -> src

            return offset + Size;
        }
    }
}
