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

//#define DEBUG_IP

using System;
using Drivers.Net;
using System.Threading;
using System.Net.IP;
using System.Collections;
using System.Diagnostics;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.SingSharp;

namespace Microsoft.Singularity.NetStack2
{

    //version of the ipheader that is byte aligned...
    //ARM architectures don't do very well with unaligned accesses
    //Can this be compiled away for x86 architectures?
    public class IpHeader
    {
        public byte   verLen; // 0:3 Version, 4:7 Header length in DWORDs.
        public byte   tos;
        public ushort pad0;
        public ushort totalLength;
        public ushort pad1;
        public ushort id;
        public ushort pad2;
        public ushort offset;
        public byte   ttl;
        public byte   protocol;
        public ushort checksum;
        public ushort pad3;
        public IPv4   srcAddress;
        public IPv4   destAddress;

        public const int Size = 20;
        public const int ICMP  = 1;
        public const int IGMP  = 2;
        public const int TCP   = 6;
        public const int IGRP  = 9;
        public const int UDP = 17;
        public const int GRE   = 47;
        public const int ESP   = 50;
        public const int AH    = 51;
        public const int SKIP  = 57;
        public const int EIGRP = 88;
        public const int OSPF  = 89;
        public const int L2TP  = 115;

        // TTL default value
        public const byte DefaultTTL = 128;

        //create a byte aligned ipheader
        //index marks the starting location of the ip header within the buffer
        public IpHeader(Bytes packet, int index)
        {
            //assert that the packet is large enough for a ipheader
            VTable.Assert(packet.Length - index > 20);

            verLen = packet[index++];
            tos    = packet[index++];
            totalLength = NetworkBitConverter.ToUInt16(packet, index);
            index += 2;
            id = NetworkBitConverter.ToUInt16(packet, index);
            index += 2;
            offset = NetworkBitConverter.ToUInt16(packet, index);
            index += 2;
            ttl = packet[index++];
            protocol = packet[index++];
            checksum = NetworkBitConverter.ToUInt16(packet, index);
            index += 2;
            uint addr;
            addr = NetworkBitConverter.ToUInt32(packet, index);
            srcAddress = new IPv4(addr);
            index += 4;
            addr = NetworkBitConverter.ToUInt32(packet, index);
            destAddress = new IPv4(addr);
#if false
            DebugStub.Print("IpHeader verlen 0x{0,8:x}\n tos {1}\n"+
                       " totalLength {2}\n ttl {3}\n protocol 0x{4,4:x}\n"+
                       " checksum 0x{5,4:x}\n src {6}\n, dest {7}\n",
                            DebugStub.ArgList(verLen, tos, totalLength, ttl, protocol, checksum, srcAddress,
                                      destAddress));
#endif
            //sgc complains...
            pad0 = 0;
            pad1 = 0;
            pad2 = 0;
            pad3 = 0;
        }

        //[Microsoft.Contracts.Pure]
        public bool MoreFragmentsFollowing()
        {
            ushort chk = 0x2000;
            if ((offset & chk) > 0) {
                return true;
            }
            return false;
        }


        // calculate's one's complement
        public static ushort SumShortValues(Bytes buffer,
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

        public static  ushort SumShortValues(ushort currentChecksum,
                                             ushort valueToAdd)
        {
            uint chksum = currentChecksum;
            chksum += valueToAdd;

            // Double-wrap chksum
            chksum = (chksum & 0xFFFF) + (chksum >> 16);
            chksum = (chksum & 0xFFFF) + (chksum >> 16);
            return (ushort)chksum;
        }

        public bool IsChecksumValid()
        {
            ushort sum = (ushort) ((((int)verLen) << 8) + ((int)tos));
            sum = SumShortValues(sum, totalLength);
            sum = SumShortValues(sum, id);
            sum = SumShortValues(sum, offset);
            sum = SumShortValues(sum, (ushort) ((((int)ttl) << 8) + ((int)protocol)));
            sum = SumShortValues(sum, (ushort) (((uint)srcAddress) >> 16));
            sum = SumShortValues(sum, (ushort) (((uint)srcAddress) & 0xFFFFU));
            sum = SumShortValues(sum, (ushort) (((uint)destAddress) >> 16));
            sum = SumShortValues(sum, (ushort) (((uint)destAddress) & 0xFFFFU));
            //fix for 0 checksum
            unchecked {
                sum = (ushort)~sum;
            }
            if (sum == 0) {
                sum = (ushort) 0xFFFF;
            }
            if (sum != checksum) {
                DebugStub.WriteLine("Bad IP Checksum {0:x4} != {1:x4}",
                                  DebugStub.ArgList(checksum, sum));
            }

            return (sum == checksum);
        }

        // calc the sum of the 16bits pseudo header fields
        // (to be later used for transport level checksum calculation)
        // offset points to the start of the IP header
        // also return the protocolLength=header+data
        public static ushort SumPseudoHeader(Bytes   header,
                                             int        offset,
                                             ref ushort protocolLength)
        {
            // source IP + destination IP
            uint sum = SumShortValues(header, offset + 12, 8);

            // add the protocol field (with zero MSB)
            sum += header[offset + 9];

            // add udp length = ip_total_length-ip_header_len
            ushort ipTotalLen = (ushort)(((ushort)(header[offset + 2] << 8)) |
                                         ((ushort)header[offset + 3]));
            //            ushort ipSize = (ushort)((pkt[offset] & 0x0f) * 4);
            protocolLength = (ushort)(ipTotalLen - IpHeader.Size);
            sum += protocolLength;

            // Double-wrap the sum
            sum = (sum & 0xFFFF) + (sum >> 16);
            sum = (sum & 0xFFFF) + (sum >> 16);
            return (ushort)sum;
        }

        // calculate the ip header checksum
        public static ushort CalculateChecksum(Bytes buffer,
                                      int    ipHeaderOffset,
                                      int    ipHeaderLength)
        {
            return (ushort)~SumShortValues(buffer,
                                           ipHeaderOffset,
                                           ipHeaderLength);
        }

    }


    public class IP
    {
        //these might be static?
        //        private TCP tcp;
        private static ARP arp;
        private static HostConfiguration hostConfiguration;

        [Conditional("DEBUG_IP")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("IP: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        [Conditional("DEBUG_IP")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print("IP: {0}",
                            DebugStub.ArgList(format));
        }


        public static void Initialize(ARP arpSession)
        {
            DebugPrint("Creating new IP module\n");
            arp = arpSession;
            UDP.Initialize();
            //TCP.Initialize();
            hostConfiguration = new HostConfiguration();
        }

        public static bool IsLocalAddress(IPv4 ipAddress)
        {
            return hostConfiguration.IsLocalAddress(ipAddress);
        }


        public static HostConfiguration GetHostConfiguration()
        {
            return hostConfiguration;
        }

        //dirt simple is the name of the game
        public static void ProcessIncomingPacket(Bytes packet, IAdapter adapter)
        {
            IpHeader ipHeader = new IpHeader(packet, EthernetHeader.Size);
            //since we apparently don't support fragments yet.
            if (ipHeader.MoreFragmentsFollowing() == true) {
                DebugPrint("ACK! ip fragmentation!\n");
                return;
            }
            //            DebugStub.Assert(ipHeader.MoreFragmentsFollowing() == false);
            //VTable.Assert(ipHeader.MoreFragmentsFollowing() == false);

            if (ipHeader.IsChecksumValid() == false) {
                DebugPrint("ProcessIncomingPacket: bad checksum...dropping packets\n");
                //delete packet;
                return;
            }
            //make sure the address is 'local'
            if (hostConfiguration == null) {
                DebugPrint("ACK hostConfiguration is NULL\n");
                return;
            }

            if ((hostConfiguration.IsLocalAddress(ipHeader.destAddress) == false) &&
                (ipHeader.destAddress != IPv4.Broadcast)) {
                //                DebugPrint("ProcessIncomingPacket: wrong address ...dropping packets\n");
                //                DebugPrint("Dest address {0}\n", ipHeader.destAddress);
                //delete packet;
                return;
            }

            try {
                //figure out to which protocol the packet belongs
                switch(ipHeader.protocol) {
                    case IpHeader.TCP:
                        DebugPrint("ProcessIncomingPacket: Got TCP packet\n");
                        //TCP.ProcessIncomingPacket(packet, ipHeader);
                        break;
                    case IpHeader.UDP:
                        //DebugPrint("ProcessIncomingPacket: Got UDP packet\n");
                        UDP.ProcessIncomingPacket(packet, ipHeader);
                        break;
                    case IpHeader.ICMP :
                        DebugPrint("ProcessIncomingPacket: Got ICMP packet\n");
                        //delete packet;
                        break;
                    default:
                        DebugPrint("Got unexpected packet!!\n");
                        //delete packet;
                        DebugStub.Break();
                        break;
                }
            }
            catch (Exception e) {
                DebugStub.Print("Caught exception {0}\n", DebugStub.ArgList(e));
                DebugStub.Break();
            }
        }

        //This function will format the higher layer packet to
        //have to correct ethernet and ip header?
        //Routing to multiple cards was broken in the old netstack...
        //for now we support a single interface
        //ipheader is already written...we just need to write the ethernet header
        public static void SendOutgoingPacket(Bytes header,
                                              Bytes buffer,
                                              IPv4 destinationAddress)
        {
            DebugPrint("IP.SendOutgoingPacket: dst {0}\n", destinationAddress);

            RouteEntry e = hostConfiguration.RoutingTable.Lookup(destinationAddress);
            if (e == null) {
                //delete header;
                //delete buffer;
                DebugPrint("Packet dropped -- no route\n");
                return;
            }

            IPv4 ifaddr = e.InterfaceAddress;
            IPv4 nextHop;
            if (e.Gateway == e.InterfaceAddress) {
                nextHop = destinationAddress;
            }
            else {
                nextHop = e.Gateway;
            }

            DebugPrint("Selected destination {0}\n", nextHop);

            DebugStub.Assert(e.Gateway == e.InterfaceAddress);

            IAdapter adapter = hostConfiguration.Bindings.GetAdapter(ifaddr);
            VTable.Assert(adapter != null);

            EthernetAddress localMac = adapter.HardwareAddress;
            EthernetAddress remoteMac;

            IAdapter targetAdapter = hostConfiguration.Bindings.GetAdapter(nextHop);
            if (targetAdapter != null) {
                remoteMac = targetAdapter.HardwareAddress;
            }
            else {
                if (arp.Lookup(nextHop, out remoteMac) == false) {
                    DebugStub.WriteLine("Outgoing packet, no ARP Entry for: {0}...about to wait\n",
                                        DebugStub.ArgList(nextHop));
                    arp.ArpRequest(ifaddr, nextHop, localMac, header, buffer, adapter);
                    //                    DebugPrint("ArpRequest complete...sending packet\n");
                    //                    bool rc = arp.Lookup(nextHop, out remoteMac);
                    //                    DebugStub.Assert(rc == true);
                    return;
                }
            }
            //Format ethernet header
            EthernetHeader.Write(header, localMac, remoteMac, EthernetHeader.PROTOCOL_IP);
            //send it!
            adapter.PopulateTxRing(header, buffer);
        }
    }
}

