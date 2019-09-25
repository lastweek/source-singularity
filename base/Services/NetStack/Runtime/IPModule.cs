// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

// #define DEBUG_IP

using NetStack.Common;
using System;
using System.Collections;
using System.Diagnostics;

using System.Net.IP;
using Drivers.Net;
using NetStack.NetDrivers;
using NetStack.Protocols;

using Microsoft.Singularity;

namespace NetStack.Runtime
{
    ///
    // This module implements the IP protocol
    // NOTICE: FOR NOW WE DO NOT HANDLE FRAGMENTATION!!!!!!!!!!!!!!
    // 
    public class IPModule : IProtocol
    {
        // the version
        protected int version;

        // the icmp protocol handle (for sending control messages)
        protected IProtocol icmp;
        protected ArpModule arp;

        // IP specific stack configuration data
        HostConfiguration hostConfig;

        private const string moduleName = "IP";

        [ Conditional("DEBUG_IP") ]
        private static void DebugPrint(string format, params object [] args)
        {
            DebugStub.Print("IPModule: {0}",
                            __arglist(string.Format(format, args))
                            );
        }

        // INetModule interfaces
        // ------------------------

        string INetModule.ModuleName    { get { return moduleName; } }

        ushort INetModule.ModuleVersion { get { return 0x01; } }  // 0.1

        // called by the runtime when
        // the protocol should be started
        public bool StartModule()
        {
            // get a ref to the icmp protocol
            icmp = Core.Instance().GetProtocolByName("ICMP");
            if (icmp == null) {
                return false;
            }

            // get a ref to the arp protocol
            arp = Core.Instance().GetProtocolByName("ARP") as ArpModule;
            if (arp == null) {
                return false;
            }

            return true;
        }

        public bool StopModule()
        {
            return true;
        }

        public bool DestroyModule()
        {
            return true;
        }

        // IProtocol interfaces
        // ------------------------
        public bool Initialize(ProtocolParams parameters)
        {
            Debug.Assert(parameters == null ||
                         parameters["name"] == moduleName);

            hostConfig = new HostConfiguration();
            version = ProtocolParams.LookupInt32(parameters, "version", 4);

            bool fragment = ProtocolParams.LookupBoolean(parameters,
                                                         "fragment",
                                                         false);
            // save the routing protocol name, if exists
            if (version != 4 || fragment == true) {
                DebugPrint("Support only exists for V4 w/o fragments.\n");
                return false;
            }

            Core core = Core.Instance();

            core.RegisterProtocol(this);
            if (!core.packetTypes.RegisterTypeHandler(PacketTypes.IP, this)) {
                core.DeregisterProtocol(this);
                return false;
            }
            return true;
        }

        public ushort GetProtocolID()
        {
            return EthernetFormat.PROTOCOL_IP;
        }

        public Session CreateSession()
        {
            return null;
        }

        // handle incoming IP packets
        public NetStatus OnProtocolReceive(NetPacket! pkt)
        {
            IPFormat.IPHeader! ipHeader;
            if (IPFormat.ReadIPHeader(pkt, out ipHeader) == false) {
                DebugPrint("bad header\n");
                return NetStatus.Code.PROTOCOL_OK;
            }
            pkt.OverlapContext = ipHeader;

            Debug.Assert(IPFormat.IsMoreFragSet(ipHeader) == false);

            // check packet checksum
            if (IPFormat.IsCheckSumOK(ipHeader) == false) {
                DebugPrint("checksum error, dropping!\n");
                return NetStatus.Code.PROTOCOL_DROP_CHKSUM;
            }

            // check if the packet is for us...
            // TBC: for now we ignore broadcasts
            // (directed + limited bcast addresses)
            Core core = Core.Instance();

            // if its not ours but we are a gateway, we should route it.
            if (hostConfig.IsLocalAddress(ipHeader.Destination) == false &&
                ipHeader.Destination != IPv4.Broadcast)
            {
                if (hostConfig.IsRouter) {
                    // Not supported for the time being.
                }
                // DebugPrint("Dropping wrong destination\n");
                return NetStatus.Code.RT_DROP_WRONG_DEST;
            }

            // we should handle it..

            IProtocol prot = core.GetProtocolFromID(ipHeader.protocol);
            if (prot == null) {
                DebugPrint("Packet drop no handler for protocol id = {0}\n",
                           (ushort)ipHeader.protocol);
                return NetStatus.Code.RT_DROP_NO_HANDLER;
            }
            else {
                DebugPrint("Got packet of type {0}\n", ipHeader.protocol);
            }

            // clip the packet for the next protocol header + data
            pkt.Clip(ipHeader.totalLength - IPFormat.Size - 1);

            return prot.OnProtocolReceive(pkt);
        }

        // this method sends an IP packet. It uses the IP header
        // target address to find route and sets the packet's Mux.
        // it also sets the target and source mac addresses
        public NetStatus OnProtocolSend(NetPacket! packet)
        {
            Multiplexer mux = (Multiplexer)packet.Mux;
            if (mux != null) {
                byte[]! data = (byte[]!) packet.GetRawData();
                // Source has already resolved outbound mux.  Check
                // briefly that they've put values in for ethernet headers
                // (yes, only ethernet is supported here folks)
                int dstOkay = ((int)data[0] | (int)data[1] | (int)data[2] |
                               (int)data[3] | (int)data[4] | (int)data[5]);
                int srcOkay = ((int)data[6] | (int)data[7] | (int)data[8] |
                               (int)data[9] | (int)data[10]| (int)data[11]);
                if (dstOkay != 0 && srcOkay != 0) {
                    mux.SendBuffered(packet);
                    DebugPrint("Packet sent (had mux)\n");
                    return NetStatus.Code.PROTOCOL_OK;
                }
                // Invalid destination or source address.  Ignore request
                // to send via specific mux.
            }

            // since we may retransmit this packet, we should
            // reset the buffer to the IP boundaries!
            packet.Clip(EthernetFormat.Size,
                        packet.Length - EthernetFormat.Size - 1);

            IPFormat.IPHeader! ipHeader;
            if (IPFormat.ReadIPHeader(packet, out ipHeader) == false) {
                DebugPrint("Packet dropped error)\n");
                DebugStub.Break();
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }
            Debug.Assert(ipHeader.Destination != IPv4.Zero);

            RouteEntry e = HostConfiguration.RoutingTable.Lookup(ipHeader.Destination);
            if (e == null) {
                DebugPrint("Packet dropped no route)\n");
                return NetStatus.Code.RT_DROP_NO_ROUTE;
            }

            //            DebugPrint("{0} -> {1}\n", ipHeader.Destination, e);
            //            DebugPrint("Packet source {0}\n", ipHeader.Source);

            IPv4 ifaddr  = e.InterfaceAddress;
            IPv4 nexthop;
            if (e.Gateway == e.InterfaceAddress) {
                nexthop = ipHeader.Destination;
            }
            else {
                nexthop = e.Gateway;
            }

            //            DebugPrint("Selected destination {0}\n", nexthop);

            IAdapter adapter      = hostConfig.Bindings.GetAdapter(ifaddr);
            assert adapter != null;
            Multiplexer targetMux = Core.Instance().GetMuxForAdapter(adapter);
            assert targetMux != null;

            packet.Mux = targetMux;

            EthernetAddress localMac = adapter.HardwareAddress;
            EthernetAddress remoteMac;

            IAdapter targetAdapter = hostConfig.Bindings.GetAdapter(nexthop);
            if (targetAdapter != null) {
                remoteMac = targetAdapter.HardwareAddress;
            }
            else {
                if (arp.Lookup(nexthop, out remoteMac) == false) {
                    DebugPrint("No ARP Entry for: {0}\n", nexthop);
                    arp.ArpRequest(ipHeader.Source, nexthop, targetMux,
                                   new ArpRequestCallback(ArpResponse),
                                   packet, TimeSpan.FromSeconds(3));
                    BlockAssociatedSession(packet);
                    return NetStatus.Code.RT_RETRY_PENDING_ARP;
                }
            }

            return SendResolved(packet, targetMux, localMac, remoteMac);
        }

        private NetStatus SendResolved(NetPacket!       packet,
                                       Multiplexer!     targetMux,
                                       EthernetAddress  localMac,
                                       EthernetAddress  remoteMac)
        {
            // set the ethernet data
            // TBC: make the ARPModule setup the packet
            {
                Session session = packet.SessionContext as Session;
                if (session != null) {
                    DebugPrint("Sending packet for {0}/{1} ({2}-->{3})\n",
                               session.RemoteAddress, session.RemotePort,
                               localMac, remoteMac);
                }
                else {
                    DebugPrint("Sending packet to {0}\n", remoteMac);
                }
            }
            Debug.Assert(packet.IsOneChunk);
            EthernetFormat.Write((byte[]!)packet.GetRawData(), 0,
                                 localMac, remoteMac,
                                 EthernetFormat.PROTOCOL_IP);
            targetMux.SendBuffered(packet);
            return NetStatus.Code.PROTOCOL_OK;
        }

        private void ArpResponse(IPv4            address,
                                 EthernetAddress answer,
                                 object          cookie)
        {
            NetPacket! packet    = (NetPacket!)cookie;
            DebugPrint("Got ARP response for {0} -> {1}", address, answer);

            UnblockAssociatedSession(packet);
            if (answer != EthernetAddress.Zero) {
                Multiplexer mux = (Multiplexer!)packet.Mux;
                SendResolved(packet, mux, mux.Adapter.HardwareAddress, answer);
                Core.Instance().SignalOutboundPackets();
            }
            else {
                DebugPrint("ARP timed out for {0}", address);
            }
        }

        private void BlockAssociatedSession(NetPacket! packet)
        {
            Session! session = (!)(packet.SessionContext as Session);
            session.OutQueuePaused = true;
            DebugPrint("Blocking Session {0}\n", session.Uid);
        }

        private void UnblockAssociatedSession(NetPacket! packet)
        {
            Session! session = (!)(packet.SessionContext as Session);
            session.OutQueuePaused = false;
            DebugPrint("Unblocking session {0}\n", session.Uid);
            Core.Instance().SignalOutboundPackets();    // Kickstart
        }

        public NetStatus SetProtocolSpecific(ushort opcode, byte[]! data)
        {
            return NetStatus.Code.PROTOCOL_OK;
        }

        public NetStatus GetProtocolSpecific(ushort opcode, out byte[] data)
        {
            data = null;
            return NetStatus.Code.PROTOCOL_OK;
        }

        //
        //protected NetStatus ForwardPacket(IPFormat.IPHeader! rcvIPHeader,
        //                                NetPacket!         packet,
        //                                Multiplexer        targetMux)
        //{
        //  Debug.Assert(packet != null && packet.IsOneChunk);
        //  // TBC: this is just a preliminary imp, should
        //  // consider MTUs etc.
        //  byte[] data = packet.ToContiguous();
        //  int start   = EthernetFormat.Size;
//
        //  // decrease the ttl, if it reaches 0 discard and send
        //  // ICMP message using on the source mux, otherwise forward!
        //  if (--rcvIPHeader.ttl == 0) {
        //      // drop it! and use icmp protocol to return error
        //      // TBC: icmp.OnProtocolSend(..)  // will use packetArg.Mux  = source mux
        //      return NetStatus.Code.RT_DROP_TTL_EXPIRED;
        //  }
        //  // at last, forward it already!
        //  // modify the header + calc new checksum
        //  IPFormat.WriteIPHeader(data, start, rcvIPHeader);
        //  DebugPrint("Forwarding IP packet.\n");
//
        //  return OnProtocolSend(packet);
        //}
        //

        public HostConfiguration! HostConfiguration
        {
            get { return hostConfig; }
        }

        // ctor
        public IPModule()
        {
        }
    }
}
