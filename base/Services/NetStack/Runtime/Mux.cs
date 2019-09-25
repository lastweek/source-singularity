// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

//#define DEBUG_MUX

using NetStack.Common;
using System;
using System.Collections;

using System.Net.IP;
using Drivers.Net;
using NetStack.NetDrivers;

using Microsoft.Singularity;

namespace NetStack.Runtime
{
    // This class provides the basic multiplexing of packets as
    // they go out to a network device.  This component of the
    // system is critical for several reasons.  First, it must
    // handle two modes of operation (where the NIC is faster
    // than the computer, and where the computer is faster
    // than the NIC).  Second, it is the place in the
    // system where we do bandwidth resource sharing, possibly
    // including non-best-effort behaviour (such as weighted
    // share or CBR).
    public class Multiplexer
    {
        // We should of course have multiple queues and schedule
        // them cleverly.
        private Queue q;
        private IAdapter! ad;
        public  IAdapter! Adapter { get {return ad;} }
        private NetPacket [] txBuffer;
        private int maxSlotsFree;
        private int maxBackLog;

        private int directs;    // Packets sent with SendDirect that
        // may be shoved into the queue at any time - we should
        // ditch SendDirect ASAP and add sessions for ARP and ICMP.

        public Multiplexer(Queue q, IAdapter! ad)
        {
            this.q = q;
            this.ad = ad;
            int capacity = ad.TxSlotsFree;
            this.txBuffer     = new NetPacket [capacity];
            this.maxSlotsFree = ad.TxSlotsFree;
            this.maxBackLog   = ad.TxSlotsFree;

            base();

            DebugPrint("TxBuffer capacity: {0}\n", capacity);
            DebugStub.Assert(capacity > 0);
        }

        [ System.Diagnostics.Conditional("DEBUG_MUX") ]
        private static void DebugPrint(string format, params object[] args)
        {
            DebugStub.Print("Mux: {0}",
                            __arglist(String.Format(format, args))
                            );
        }

        public bool IsBackLogged
        {
            get { return this.q.Count >= this.maxBackLog; }
        }

        public int FreeBufferSpace
        {
            get { return Math.Max(this.maxBackLog - this.q.Count, 0); }
        }

        public void SendBuffered(NetPacket! packet)
        {
            // This is the preferred way of sending packets as it
            // allows us to gather up larger groups of packets to
            // send.

            DebugStub.Assert(packet.Length <= 1514);

            q.Enqueue(packet);

            DebugPrint("SendBuffered free = {0} queued = {1}\n",
                       ad.TxSlotsFree, q.Count);

            DebugStub.Assert(q.Count <= this.maxBackLog + directs);
        }

        public void PushSendBuffer()
        {
            int txCount = Math.Min(ad.TxSlotsFree, q.Count);

            DebugPrint("PushSendBuffer free = {0} queued = {1}\n",
                       ad.TxSlotsFree, q.Count);

            if (txCount > 0) {
                for (int i = 0; i < txCount; i++) {
                    txBuffer[i] = (NetPacket)q.Dequeue();
                }
                for (int i = txCount; i < txBuffer.Length; i++) {
                    // Paranoia (if it's wrong lower down, it might send
                    // a duplicate).
                    txBuffer[i] = null;
                }
                ad.PopulateTxRing(txBuffer, (uint)txCount);

                // If stack has placed packets directly in buffer for
                // send decrement counter, we only count directs to check
                // the queue does not grow unbounded.
                directs -= Math.Max(0, directs - txCount);
            }
        }

        // Simpler function for sending a single packet
        public void SendDirect(NetPacket! packet)
        {
            // This method should be deprecated
            // Everything should have an associated session and be
            // sent from the outgoing queues handler.
            directs ++;
            SendBuffered(packet);
            DebugPrint("SendDirect\n");
            PushSendBuffer();
        }

        public NetStatus OnAdapterSendComplete(Dispatcher.CallbackArgs unused)
        {
            ad.GetTransmittedPackets();
            DebugPrint("OnAdapterSendComplete free = {0} queued = {1}\n",
                       ad.TxSlotsFree, q.Count);
            Core.Instance().SignalOutboundPackets();
            return NetStatus.Code.RT_OK;
        }
    } // Multiplexer
} // NetStack.Runtime
// End
