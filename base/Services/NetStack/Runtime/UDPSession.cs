///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Netstack / Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   UdpModule.cs
//
//  Note:   This is a port of the existing code TCP Session code to a UDP
//          Session.
//

// #define DEBUG_UDP

using NetStack.Common;
using System;
using System.Diagnostics;
using System.Threading;

#if SINGULARITY
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
#else
using System.Net;
#endif

using System.Net.IP;
using Drivers.Net;

namespace NetStack.Runtime
{
    using Protocols;

    public class UdpSession : Session
    {
        // the session's transmit q size (num of packets)
        public const int TxQueueSize = 100;

        // the session's receive queue size (num of packets)
        public const int RxQueueSize = 100;

        protected bool blocking = true;   // Blocking / Non-Blocking
        private   bool closed   = false;

        public UdpSession(IProtocol! p) : base (p, TxQueueSize, RxQueueSize)
        {
        }

        ~UdpSession()
        {
        }

        [ Conditional("DEBUG_UDP") ]
        private static void DebugPrint(string format, params object [] args)
        {
            Core.Log(format, args);
        }

        public bool BindLocalEndPoint(IPv4 address, ushort port)
        {
            return SetLocalEndPoint(address, port);
        }

        public void BindRemoteEndPoint(IPv4 address, ushort port)
        {
            SetRemoteEndPoint(address, port);
        }

        public void BindEndPoints(IPv4   newLocalAddress,
                                  ushort newLocalPort,
                                  IPv4   remoteAddress,
                                  ushort remotePort)
        {
            BindRemoteEndPoint(remoteAddress, remotePort);
            if (BindLocalEndPoint(newLocalAddress, newLocalPort) == true) {
                String msg = String.Format("Successful bind to {0} (bound to {1})\n",
                           newLocalPort, LocalPort);
                Tracing.Log(Tracing.Debug,msg);
            }
            else {
                String msg = String.Format("Failed to bind to {0} (bound to {1})\n",
                           newLocalPort, LocalPort);
                Tracing.Log(Tracing.Debug,msg);
            }
        }

        override internal NetStatus OnReceive(object     sender,
                                              NetPacket! packet,
                                              object     context)
        {
            if (this.PutPacket(this.inQueue, packet, false) == true) {
                // Packet is queued for user.  Needs to be held onto.
                return NetStatus.Code.PROTOCOL_PROCESSING;
            }
            return NetStatus.Code.PROTOCOL_OK;
        }

        public bool Blocking
        {
            get { return blocking; }
            set { blocking = value; }
        }

        override public byte[] ReadCopyData()
        {
            if (!IsSessionValidForUserRead()) {
                DebugPrint("ReadData on closed UDP session");
                return null;
            }

            NetPacket netPacket = DequeuePacket(inQueue,
                                                blocking ? TimeSpan.Infinite /* forever */: TimeSpan.Zero /* don't sleep */);
            if (netPacket != null) {
                byte [] userData = netPacket.ToUser();
                Core.Instance().TheDemux.TakeFreePacket(netPacket);
                return userData;
            }

            return null;
        }

        override public int WriteData(byte[]! data)
        {
            if (this.RemoteAddress == IPv4.Any || this.RemotePort == 0) {
                Core.Log("Attempting to send UDP data to an invalid endpoint: "
                    + "{0}/{1}\n", this.RemoteAddress, this.RemotePort);
                String msg = String.Format("Attempting to send UDP data to an invalid endpoint: {0}/{1}\n", this.RemoteAddress, this.RemotePort);
                Tracing.Log(Tracing.Debug,msg);

                // Log sending to incomplete endpoint
                return 0;
            }
            return WriteDataTo(this.RemoteAddress, this.RemotePort, data);
        }

        public int WriteDataTo(IPv4    remoteAddress,
                               ushort  remotePort,
                               byte[]! data)
        {
            if (!IsSessionValidForUserWrite()) {
                DebugPrint("WriteDataTo on closed UDP session");
                return -1;
            }

            int headerSize = EthernetFormat.Size + IPFormat.Size + UdpFormat.Size;
            byte[] packet = new byte [headerSize + data.Length];
            int ipStart = EthernetFormat.Size;

            if (this.LocalAddress == IPv4.Any)
                this.SetLocalEndPoint(this.LocalAddress, this.LocalPort);

            UdpFormat.WriteUdpPacket(packet, ipStart,
                                     this.LocalAddress, this.LocalPort,
                                     remoteAddress, remotePort,
                                     data, 0, data.Length);

            NetPacket netPacket = new NetPacket(packet);
            if (base.PutPacket(outQueue, netPacket, blocking) == false) {
                Core.Log("Failed to enqueue packet for {0}/{1}",
                    remoteAddress, remotePort);
                String msg = String.Format ("Failed to enqueue packet for {0}/{1}",
                    remoteAddress, remotePort);
                Tracing.Log(Tracing.Debug,msg);
                return 0;
            }

            return data.Length;
        }

        public int WriteDataTo(IPv4    remoteAddress,
                               ushort  remotePort,
                               byte[]! in ExHeap data)
        {
            if (!IsSessionValidForUserWrite()) {
                DebugPrint("WriteDataTo on closed UDP session");
                return -1;
            }

            int headerSize = EthernetFormat.Size + IPFormat.Size + UdpFormat.Size;
            int dataLength = Math.Min(1514 - headerSize, data.Length);
            byte[] packet = new byte [headerSize + dataLength];
            int ipStart = EthernetFormat.Size;

            if (this.LocalAddress == IPv4.Any) {
                this.SetLocalEndPoint(this.LocalAddress, this.LocalPort);
            }

            UdpFormat.WriteUdpPacket(packet, ipStart,
                                     this.LocalAddress, this.LocalPort,
                                     remoteAddress, remotePort,
                                     data, 0, dataLength);

            NetPacket netPacket = new NetPacket(packet);
            if (base.PutPacket(outQueue, netPacket, blocking) == false) {
                Core.Log("Failed to enqueue packet for {0}/{1}",
                    remoteAddress, remotePort);
                String msg = String.Format ("Failed to enqueue packet for {0}/{1}",
                    remoteAddress, remotePort);
                Tracing.Log(Tracing.Debug,msg);
                return 0;
            }

            return dataLength;
        }

        public int WriteData(byte[]! in ExHeap buffer)
        {
            if (this.RemoteAddress == IPv4.Any || this.RemotePort == 0) {
                Core.Log("Attempting to send UDP data to an invalid endpoint: "
                    + "{0}/{1}\n", this.RemoteAddress, this.RemotePort);
                String msg = String.Format("Attempting to send UDP data to an invalid endpoint: {0}/{1}\n", this.RemoteAddress, this.RemotePort);
                Tracing.Log(Tracing.Debug,msg);

                // Log sending to incomplete endpoint
                return 0;
            }
            return WriteDataTo(this.RemoteAddress, this.RemotePort, buffer);
        }

        public bool WritePacket(NetPacket! netPacket)
        {
            if (!IsSessionValidForUserWrite()) {
                DebugStub.Break();
                return false;
            }
            return base.PutPacket(outQueue, netPacket, blocking);
        }

        public override bool Close()
        {
            if (closed == false) {
                DebugPrint("Closing Session");
                this.Dispose();
                closed = true;
            }
            return closed;
        }

        public bool PollSelectRead(int timeoutMillis)
        {
            return PollQueueNotEmpty(this.inQueue, timeoutMillis);
        }

        public bool PollSelectWrite(int timeoutMillis)
        {
            return PollQueueNotFull(this.outQueue, timeoutMillis);
        }

        internal override bool IsSessionValidForUserRead()
        {
            return !closed;
        }

        internal override bool IsSessionValidForUserWrite()
        {
            return !closed;
        }
    }
}
