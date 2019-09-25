///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Netstack / Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   UdpModule.cs
//
//  Note:
//

// #define DEBUG_UDP

using NetStack.Common;
using System;
using System.Collections;
using System.Diagnostics;

#if SINGULARITY
using Microsoft.Singularity;
#else
using System.Net;
#endif

using System.Net.IP;
using Drivers.Net;
using NetStack.Protocols;

namespace NetStack.Runtime
{
    public class UdpModule : IProtocol
    {
        protected IProtocol ip;

        public UdpModule()
        {
        }

        // INetModule interfaces
        // ---------------------
        string INetModule.ModuleName        { get { return "UDP"; } }
        ushort INetModule.ModuleVersion     { get { return 0x01; } }    // 0.1

        private bool started = false;
        public bool StartModule()
        {
            Debug.Assert(started == false);
            started = true;
            ip = Core.Instance().GetProtocolByName("IP");
            return ip != null;
        }

        public bool StopModule()
        {
            return true;
        }

        public bool DestroyModule()
        {
            return true;
        }

        public bool Initialize(ProtocolParams parameters)
        {
            Core.Instance().RegisterProtocol(this);
            return true;
        }

        public ushort GetProtocolID()
        {
            return (ushort)IPFormat.Protocol.UDP;
        }

        public Session CreateSession()
        {
            UdpSession s = new UdpSession(this);
            Core.Instance().RegisterSession(this, s);
            return s;
        }

        public UdpSession CreateUnboundSession()
        {
            UdpSession s = new UdpSession(this);
            Core.Instance().RegisterSession(this, s);
            return s;
        }

        public UdpSession! CreateBoundSession(IPv4   localAddress,
                                              ushort localPort,
                                              IPv4   remoteAddress,
                                              ushort remotePort)
        {
            UdpSession s = new UdpSession(this);
            Core.Instance().RegisterSession(this, s);
            s.BindEndPoints(localAddress, localPort,
                            remoteAddress, remotePort);
            return s;
        }

        [ Conditional("DEBUG_UDP") ]
        private static void DebugPrint(string format, params object [] args)
        {
            Core.Log(format, args);
        }

        public NetStatus OnProtocolReceive(NetPacket! packet)
        {
            DebugPrint("Received UDP packet!\n");

            UdpFormat.UdpHeader udpHeader = new UdpFormat.UdpHeader();
            if (UdpFormat.ReadUdpHeader(packet, out udpHeader) == false) {
                DebugPrint("UDP session received unreadable packet.\n");
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }

            IPFormat.IPHeader! ipHeader = (IPFormat.IPHeader!) packet.OverlapContext;
            if (udpHeader.checksum != 0 &&
                UdpFormat.IsChecksumValid(ipHeader,udpHeader, packet) == false)
            {
                DebugPrint("UDP checksum failed.  NO cigar and NO packet!");
                return NetStatus.Code.PROTOCOL_DROP_CHKSUM;
            }

            packet.OverlapContext = ipHeader;

            ArrayList udpSessions = Core.Instance().GetSessions(this);
            if (udpSessions == null) {
                DebugPrint("No UDP Sessions\n");
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }

            DebugPrint("Packet : Source {0}:{1} Destination {2}:{3}\n",
                       ipHeader.Source, udpHeader.srcPort,
                       ipHeader.Destination, udpHeader.dstPort);

            lock (udpSessions.SyncRoot) {
                foreach (UdpSession! u in udpSessions) {
                    DebugPrint("Session : Source {0}:{1} Destination {2}:{3}\n",
                               u.RemoteAddress, u.RemotePort,
                               u.LocalAddress, u.LocalPort);

                    // Match conditions
                    //
                    // Bound remote port is zero (not-specified)
                    // or matches exactly Bound remote IP is Any
                    // (not-specified) or matches exactly
                    if ((u.RemoteAddress == IPv4.Any ||
                         u.RemoteAddress == ipHeader.Source)     &&
                        (u.RemotePort == 0           ||
                         u.RemotePort == udpHeader.srcPort)      &&
                        (u.LocalAddress == IPv4.Any  ||
                         u.LocalAddress == ipHeader.Destination) &&
                        (u.LocalPort == udpHeader.dstPort))
                    {
                        DebugPrint("Delivered to UDP session\n");
                        return u.OnReceive(this, packet, udpHeader);
                    }
                }
            }

            return NetStatus.Code.PROTOCOL_DROP_ERROR;
        }

        public NetStatus OnProtocolSend(NetPacket! pkt)
        {
            return ip.OnProtocolSend(pkt);
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
    }
}
