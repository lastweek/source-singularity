// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using NetStack.Common;
using System;
using System.Threading;
using System.Collections;
using System.Diagnostics;

#if !SINGULARITY
using System.Net;
#endif

using System.Net.IP;
using Drivers.Net;

namespace NetStack.Runtime
{
    using Protocols;

    // an ICMP session
    public class IcmpSession : Session
    {
        // the session's transmit q size
        public const int TxQSize = 100;

        // the session's receive q size
        public const int RcvQSize = 100;

        public IcmpSession(IProtocol! protocol)
            : base(protocol, TxQSize, RcvQSize)
        {
        }

        // override the OnReceive
        override internal NetStatus OnReceive(object     sender,
                                              NetPacket! pkt,
                                              object     ctx)
        {
            NetStatus res = base.OnReceive(sender, pkt, ctx);
            // if the packet can be delivered to the user
            if (res != NetStatus.Code.PROTOCOL_PROCESSING) {
                // get the packet and put it on the incoming queue
                // if there is no room, drop it. this method is called
                // by the runtime when a packet destination is this session.
                this.PutPacket(inQueue, pkt, false);
            }
            return res;
        }

        // the user should create an IP+ICMP buffer
        override public int WriteData(byte[]! data)
        {
            if (!IsSessionValidForUserWrite()) {
                return -1;
            }

            byte[] pktData = new byte[EthernetFormat.Size+IPFormat.Size+data.Length];
            Array.Copy(data,0,pktData,EthernetFormat.Size,data.Length);
            NetPacket pkt=new NetPacket(pktData);
            PutPacket(outQueue,pkt,true);
            return data.Length;
        }

        override public bool Close()
        {
            Core.Instance().DeregisterSession(Protocol, this);
            return true;
        }
    }

#if Qos
    // an Qos ICMP session
    public class QosIcmpSession : Session
    {
        // the session's transmit q size
        public const int TxQSize=100;

        // the session's receive q size
        public const int RcvQSize=100;

        public QosIcmpSession(IProtocol protocol)
            : base(protocol, TxQSize, RcvQSize)
        {
        }

        // override the OnReceive (no state machine here, so don't call base)
        override internal NetStatus OnReceive(object sender,NetPacket pkt,object ctx)
        {
#if DEBUG
            Console.Out.WriteLine("QosIcmpSession:OnReceived, flow capacity={0}",capacity);
#endif
            if (!this.PutPacket(inQueue,inQueueMonitor,pkt,false)) {
                pkt.ReleaseRef();
                // increment the session capacity
                capacity++;
                return NetStatus.Code.PROTOCOL_OK;
            }
            // the packet is in the Q so, return it only after the user consumed it!
            return NetStatus.Code.PROTOCOL_PROCESSING;
        }

        override public byte[] ReadData()
        {
            NetPacket pkt = GetPacketFromQ(inQueue,inQueueMonitor,true,Timeout.Infinite,true);
            byte[] toUser=null;
            if (pkt != null)
                toUser = pkt.ToUser();

            // now the packet can be returned!
            pkt.ReleaseRef();
            Core.Instance().TheDemux.TakeFreePacket(pkt);
            // increment the session capacity
            capacity++;
#if DEBUG
            Console.Out.WriteLine("QosIcmpSession::ReadData, session capacity={0}",capacity);
#endif
            return toUser;
        }

        override public byte[] PollCopyData(int timeout)
        {
            NetPacket pkt = GetPacketFromQ(inQueue,inQueueMonitor,true,timeout,true);
            byte[] toUser=null;
            if (pkt != null) {
                toUser = pkt.ToUser();
                // now the packet can be returned!
                pkt.ReleaseRef();
                Core.Instance().TheDemux.TakeFreePacket(pkt);
                // increment the session capacity
                capacity++;
            }
            return toUser;
        }

        // the user should create an IP+ICMP buffer
        override public int WriteData(byte[] data)
        {
            if (!IsSessionValidForUserWrite()) {
                return -1;
            }

            byte[] pktData = new byte[EthernetFormat.Size+IPFormat.Size+data.Length];
            Array.Copy(data,0,pktData,EthernetFormat.Size,data.Length);
            NetPacket pkt=new NetPacket(pktData);
            PutPacket(outQueue,outQueueMonitor,pkt,true);
            return data.Length;
        }

        override public bool Close()
        {
            Core.Instance().DeregisterSession(prot,this);
            return true;
        }
    }

#region PrivateIcmpSession
    // -------------------------------------------------------
    // The internal ICMP Session (owned by the stack)
    // -------------------------------------------------------
    public class PrivateIcmpSession : QosIcmpSession
    {

        public PrivateIcmpSession(IProtocol p) : base(p)
        {
        }

        // override the OnReceive
        override internal NetStatus OnReceive(object sender,NetPacket pkt,object ctx)
        {
#if DEBUG
            Console.Out.WriteLine("PrivateIcmpSession:OnReceived, flow capacity={0}",capacity);
#endif
            Debug.Assert(ctx!=null);
            NetStatus res = NetStatus.Code.PROTOCOL_OK;
            IcmpFormat.IcmpHeader icmpHeader = (IcmpFormat.IcmpHeader)ctx;
            IPFormat.IPHeader ipHeader = pkt.OverlapContext as IPFormat.IPHeader;
            Multiplexer mux = pkt.AdapterContext as Multiplexer;  // source mux
            Debug.Assert(ipHeader!=null && mux!=null);
            bool handled=false;

            // handle various types
            switch (icmpHeader.type) {
                case (byte)IcmpFormat.IcmpType.ECHO_REQUEST:
                    if (icmpHeader.code == 0) {
#if DEBUG_IP
                        Console.WriteLine("PrivateIcmpSession: Handling ECHO_REQUEST From: {0}", ipHeader.srcAddrIP);
#endif
                        // send reply
                        // clone it since some session may use it (it is readonly!)
                        int length = pkt.Length();
                        byte [] pktData = new byte [length];
                        Array.Copy(pkt.GetRawData(), 0, pktData, 0, length);

                        IcmpFormat.CreateFastEchoReply(
                            pktData,
                            ipHeader.totalLength-IPFormat.Size
                            );
                        NetPacket reply = new NetPacket(pktData);
                        reply.SessionContext=this;
                        mux.Send(reply);
                        handled=true;
                    }
                    break;
                default:
                    break;
            }
            // return the original packet (no use for it anymore)
            pkt.ReleaseRef();
            // only increment the session capacity
            // if this is not ours..
            // this way we apply back pressure and only
            // increase the capacity once sending is done!
            if (!handled)
                capacity++;
#if DEBUG
            Console.Out.WriteLine("PrivateIcmpSession:OnReceived FINISHED, flow capacity={0}",capacity);
#endif
            return res;
        }
    }
#endregion
#endif
}

