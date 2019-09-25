// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

// #define DEBUG_TCP

///
// Microsoft Research, Cambridge
// 

using System;
using System.Collections;
using System.Diagnostics;
using System.Net.IP;

#if !SINGULARITY
using System.Net;
using System.Text;
#endif

using Drivers.Net;

using NetStack.Common;
using NetStack.Protocols;

namespace NetStack.Runtime
{
    ///
    // This module implements the TCP protocol
    // Notice: It is a simplified implementation (the very basic)
    // 
    public class TcpModule : IProtocol
    {
        // the ip handler
        protected IProtocol ip;

        // the TCP retransmit timeout
        protected int retransTimeout;

        // INetModule interfaces
        // ------------------------
        string INetModule.ModuleName    { get { return "TCP"; } }
        ushort INetModule.ModuleVersion { get { return 0x01; } }  // 0.1

        public bool StartModule()
        {
#if DEBUG_TCP
            Core.Log("Starting TCP module...\n");
#endif
            ip = Core.Instance().GetProtocolByName("IP");
            Debug.Assert(ip != null);
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
            Debug.Assert(parameters == null || parameters["name"] == "TCP");
            Core.Instance().RegisterProtocol(this);
            TcpSessionPool.SetTcpModule(this);
            return true;
        }

        [ Conditional("DEBUG_TCP") ]
        private static void DebugPrint(string format, params object [] args)
        {
            Core.Log(format, args);
        }

        public ushort GetProtocolID()
        {
            return ((ushort)IPFormat.Protocol.TCP);
        }

        Session IProtocol.CreateSession()
        {
            TcpSession tcp = (TcpSession) TcpSessionPool.Get();
            Core.Instance().RegisterSession(this, tcp);
            return tcp;
        }

        public TcpSession! ReInitializeSession(TcpSession! tcp)
        {
            tcp.ReInitialize(this);
            Core.Instance().RegisterSession(this, tcp);
            return tcp;
        }

        // handle incoming TCP packets
        public NetStatus OnProtocolReceive(NetPacket! packet)
        {
            // IP should have passed us a context which
            // is the IPHeader... lets see...
            IPFormat.IPHeader! ipHeader = (IPFormat.IPHeader!) packet.OverlapContext;

            // read the TCP header
            TcpFormat.TcpHeader tcpHeader;
            if (!TcpFormat.ReadTcpHeader(packet, out tcpHeader)) {
                DebugPrint("Bad TCP Header.  Packet rejected.");
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }

            // check validity
            if (tcpHeader.checksum != 0 &&
                TcpFormat.IsChecksumValid(ipHeader,tcpHeader, packet) == false)
            {
                DebugPrint("TCP checksum failed. Packet rejected.");
                return NetStatus.Code.PROTOCOL_DROP_CHKSUM;
            }

            // where is our data?
            // skip over options (that we currently ignore)
            int tcpHeaderSize = 4 * TcpFormat.GetOffset(ref tcpHeader);
            int startIndex = EthernetFormat.Size + IPFormat.Size + tcpHeaderSize;
            int segmentSize = ipHeader.totalLength - IPFormat.Size - tcpHeaderSize;
            packet.Clip(startIndex,segmentSize - 1);

            // find the relevant session...
            Session tcpSession = FindSession(ipHeader, ref tcpHeader);
            if (tcpSession == null) {
                DebugPrint("TCP Session not found.  TCP Packet dropped.");
            }
            else {
                // Deliver the packet to the session.  The tpcHeader is passed
                //  as a context and the ipHeader is passed as a
                //  packet.OverlapContext since we will not use it anymore
                //  (and TCP may need it).
                packet.OverlapContext = ipHeader;
                return tcpSession.OnReceive(this, packet, tcpHeader);
            }

            return NetStatus.Code.PROTOCOL_DROP_ERROR;
        }

        // Find the relevant session for this connection
        protected TcpSession FindSession(IPFormat.IPHeader! ipHeader,
                                         ref TcpFormat.TcpHeader tcpHeader)
        {
            // Get the session table
            ArrayList sessions = Core.Instance().GetSessions(this);
            if (sessions == null) {
                return null;
            }

            // First priority is a full match (Loc/Rem X Addr/Port all match),
            //  but next priority is a "passive" match (a Broadcast to "me").
            TcpSession passiveSession = null;  // this is the passive session

            lock (sessions.SyncRoot) {
                // BUGBUG: This should use HashTables (KeyedCollections  // TODO
                // BUGBUG:  if we get Generics) for Performance reasons. // TODO
                // BUGBUG:  We need one for full and one for passive.    // TODO
                // BUGBUG:  The full hashtable uses local and remote     // TODO
                // BUGBUG:  addresses as the keys and can be limited to  // TODO
                // BUGBUG:  sessions without Remote Broadcast addresses; // TODO
                // BUGBUG:  the passive hashtable is limited to sessions // TODO
                // BUGBUG:  with Remote Broadcast addresses and uses the // TODO
                // BUGBUG:  local address only as the key.               // TODO
                // BUGBUG: Note that this is done for every TCP Packet.  // TODO
                foreach (TcpSession! tcpSession in sessions) {
                    bool matchLocal =
                        (tcpSession.LocalAddress == ipHeader.Destination) &&
                        (tcpSession.LocalPort == tcpHeader.destPort);

                    // Both full and passive matches require full Local match.
                    if (matchLocal) {

                        // Check the Remote Match for a Full Match
                        bool matchRemote =
                            (tcpSession.RemoteAddress == ipHeader.Source) &&
                            (tcpSession.RemotePort == tcpHeader.sourcePort);

                        // If a full match (local && remote) return the session.
                        if (matchRemote) {
                            return tcpSession;
                        }

                        // Check for "Broadcast" address.
                        bool matchBroadcast =
                            (tcpSession.RemoteAddress == IPv4.Broadcast) &&
                            (tcpSession.RemotePort == 0);

                        // No full match, but save passiveSession
                        //  if matchLocal && matchBroadcast.
                        if (matchBroadcast) {
                            passiveSession = tcpSession;
                        }
                    }
                }
            }

            // If we didn't find an exact match, return
            //  the passive match, if any (may be null).
            return passiveSession;
        }

        // Send TCP packet, constructed by the caller, using the IP layer.
        public NetStatus OnProtocolSend(NetPacket! packet)
        {
            // if the ARP hasn't resolved the address yet, the
            // runtime will try this again (on the next handle
            // of outgoing sessions' queues)
            return ip.OnProtocolSend(packet);
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

        public TcpModule()
        {
        }
    }
}
