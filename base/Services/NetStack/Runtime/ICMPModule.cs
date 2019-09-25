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
using System.Collections;
using System.Diagnostics;
using System.Net.IP;

using Drivers.Net;
using NetStack.Protocols;

using Microsoft.Singularity;

namespace NetStack.Runtime
{
    ///
    // This module implements the ICMP protocol
    // 
    public class IcmpModule : IProtocol
    {
        // the ip handler
        protected IProtocol ip;

        // INetModule interfaces
        // ------------------------
        string INetModule.ModuleName  {get {return "ICMP";} }

        ushort INetModule.ModuleVersion {get {return 0x01;}}  // 0.1

        [ Conditional("DEBUG_ICMP") ]
        private static void DebugPrint(string format, params object [] args)
        {
            Core.Log(format, args);
        }

        public bool StartModule()
        {
            DebugPrint("Starting ICMP module...");

            ip = Core.Instance().GetProtocolByName("IP");
            Debug.Assert(ip!=null);
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
            Debug.Assert(parameters == null || parameters["name"]=="ICMP");

            Core.Instance().RegisterProtocol(this);
            // no need to register at the packet level!
            return true;
        }

        public ushort GetProtocolID()
        {
            return ((ushort)IPFormat.Protocol.ICMP);
        }

        // create a protocol session and register it
        // internally
        public Session CreateSession()
        {
            Session icmp = new IcmpSession(this);
            Core.Instance().RegisterSession(this,icmp);
            // register internally
            //            sessions += new Session.OnPacketReceive(icmp.OnReceive);
            return icmp;
        }

        // the session event dispatching instance
        //        public event Session.OnPacketReceive sessions;

        // handle incoming IP packets
        public NetStatus OnProtocolReceive(NetPacket! pkt)
        {
            // handle ICMP messages
            // ---------------------
            // start analyzing the request
            Multiplexer! mux = (!)Core.Instance().GetMuxForAdapter((IAdapter!)pkt.AdapterContext);

            // IP should have passed us a context which
            // is the IPHeader... lets see...
            IPFormat.IPHeader! ipHeader = (IPFormat.IPHeader!)pkt.OverlapContext;

            // read the icmp header
            IcmpFormat.IcmpHeader icmpHeader;
            if (!IcmpFormat.ReadIcmpHeader(pkt, out icmpHeader)) {
                return NetStatus.Code.PROTOCOL_OK;
            }

            // handle various types
            switch (icmpHeader.type) {
                case (byte)IcmpFormat.IcmpType.ECHO_REQUEST:
                    if (icmpHeader.code == 0) {
                        DebugPrint("IcmpModule: Handling ECHO_REQUEST From: {0}", ipHeader.Source);

                        // send reply
                        int length = pkt.Length;
                        byte [] pktData = new byte [length];
                        Array.Copy(pkt.GetRawData(), 0, pktData, 0, length);

                        IcmpFormat.CreateFastEchoReply(
                            pktData,
                            ipHeader.totalLength-IPFormat.Size
                            );
                        NetPacket reply = new NetPacket(pktData);
                        mux.SendDirect(reply);
                        return NetStatus.Code.PROTOCOL_OK;
                    }
                    break;
                default:
                    break;
            }

            DebugPrint("IcmpModule: Dispatching packet to Sessions");

            // our sessions wants the IP header as well, IP
            // already shrinked the packet for us so no need
            // to shrink the packet
            pkt.Clip(EthernetFormat.Size,ipHeader.totalLength - 1);

            // fire the event to any interested sessions
            // (we could also use Core.Instance().Sessions to
            // choose a specific session...)

            //            if (sessions != null)
            //{
            //sessions(this, pkt, icmpHeader);
            //}

            return NetStatus.Code.PROTOCOL_OK;
        }

        // this method send a ready made ICMP packet (IP level only),
        // it uses the IP layer.
        public NetStatus OnProtocolSend(NetPacket! pkt)
        {
            ip.OnProtocolSend(pkt);
            return NetStatus.Code.PROTOCOL_OK;
        }

        public NetStatus SetProtocolSpecific(ushort opcode,byte[]! data)
        {
            return NetStatus.Code.PROTOCOL_OK;
        }


        public NetStatus GetProtocolSpecific(ushort opcode,out byte[] data)
        {
            data = null;
            return NetStatus.Code.PROTOCOL_OK;
        }

        // ctor
        public IcmpModule()
        {
        }
    }
}
