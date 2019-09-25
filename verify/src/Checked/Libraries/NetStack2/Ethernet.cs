///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:
//
//  Note:
//

//#define DEBUG_ETHERNET

using System;
using System.Diagnostics;
using Drivers.Net;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity;
using Microsoft.SingSharp;

namespace Microsoft.Singularity.NetStack2
{

    public class EthernetHeader
    {
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

        // Write an Ethernet header assuming that the header begins at offset 0
        public static void Write(Bytes header,
                                EthernetAddress src,
                                EthernetAddress dst,
                                ushort          type)
        {
            dst.CopyOut(header.Array, header.Start);
            src.CopyOut(header.Array, header.Start + EthernetAddress.Length);
            header[12] = (byte) (type >> 8);
            header[13] = (byte) (type & 0xff);
        }

        public static bool GetProtocol(Bytes packet, out ushort protocol)
        {
            try {
                int offset = EthernetAddress.Length * 2;
                protocol = NetworkBitConverter.ToUInt16(packet, offset);
            }
            catch {
                protocol = 0;
                return false;
            }
            return true;
        }        //Get the protocol for this packet
    }

    //This class demuxes all packets from a particular
    //adapter and sends them off to the appropriate protocol
    public class Ethernet
    {

        [Conditional("DEBUG_ETHERNET")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("ETHERNET: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        private static ARP arp;

        public static void Initialize(ARP arpSession)
        {
            arp = arpSession;
        }

        public static void ProcessIncomingPacket(Bytes packet, IAdapter adapter)
        {
            //check the header
            //send it off to the instance of the protocol to further parse and handle
            try {
                ushort protocol;
                EthernetHeader.GetProtocol(packet, out protocol);
                switch (protocol) {
                    case EthernetHeader.PROTOCOL_IP:
                        DebugPrint("IP\n");
                        //                        DebugPrint("Received IP Packet...processing\n");
                        IP.ProcessIncomingPacket(packet, adapter);
                        DebugPrint("IP D\n");
                        break;
                    case EthernetHeader.PROTOCOL_ARP:
                        //                        DebugPrint("Received ARP Packet...processing\n");
                        DebugPrint("ARP\n");
                        arp.ProcessIncomingPacket(packet, adapter);
                        DebugPrint("ARPD\n");
                        break;
                    case EthernetHeader.PROTOCOL_NLB:
                        DebugPrint("Received NLB packet...discarding\n");
                        //delete packet;
                        break;
                    case 0x8100:
                        DebugPrint("Q/P\n");
                        break;
                    case EthernetHeader.PROTOCOL_IP6:
                        DebugPrint("IPv6\n");
                        break;
                    default :
                        DebugPrint("Unexpected Ethernet protocol ", protocol.ToString("X") + ". ");
                        //                        DebugStub.Break();
                        //delete packet;
                        break;
                }
            }
            catch (Exception e) {
                DebugStub.Print("Exception in Ethernet.ProcessIncomingPacket txt:{0}\n", DebugStub.ArgList(e));
                DebugStub.Break();
            }
        }
    }
}



