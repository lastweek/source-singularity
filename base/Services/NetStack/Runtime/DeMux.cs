// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

using NetStack.Common;
using Microsoft.Contracts;
using Microsoft.Singularity;

using System;
using System.Collections;
using System.Diagnostics;

using System.Net.IP;
using Drivers.Net;
using NetStack.NetDrivers;
using NetStack.Protocols;

namespace NetStack.Runtime
{
    // Helper class to help feed packets from adapter into DeMultiplexer
    public class DemuxAdapterArgs : Dispatcher.CallbackArgs
    {
        private IAdapter! adapter;

        public DemuxAdapterArgs(IAdapter! adapter)
        {
            this.adapter = adapter;
            base();
        }
        public IAdapter! Adapter { get { return adapter; } }
    }

    // This class provides the basic demultiplexing of packets as
    // they come in from a network device.  This component of the
    // system is critical for several reasons.  First, it is the place
    // where backpressure is applied; this should be the only place
    // in the system where packets are thrown away because of overload
    // Second, it is the place where "flows" in the system are separated
    // and where their resource controls are applied; subsequent
    // processing can be done entirely with the resources (including
    // potentially CPU resources) belonging to the "flow".
    public class DeMultiplexer
    {
        // Private data
        private Queue! rxQueue;
        private Queue! tmpQueue;

        [NotDelayed]
        public DeMultiplexer()
        {
            this.rxQueue  = new Queue();
            this.tmpQueue = new Queue();
            base();
        }

        // Add a new packet to the free list
        public void TakeFreePacket(NetPacket! pkt)
        {
            IAdapter! adapter = (IAdapter!)pkt.AdapterContext;
            pkt.Reset();
            adapter.PopulateRxRing(pkt);
        }

        public bool PacketsReady { get { return rxQueue.Count > 0; } }

        public NetPacket! GetReceivedPacket()
        {
            NetPacket! pkt = (NetPacket!)this.rxQueue.Dequeue();
            DebugStub.Assert(pkt.AdapterContext != null);
            return pkt;
        }

        public NetStatus OnAdapterReceive(Dispatcher.CallbackArgs ca)
        {
            DemuxAdapterArgs daa      = (DemuxAdapterArgs!)ca;
            IAdapter         adapter  = daa.Adapter;

            adapter.GetReceivedPackets(this.tmpQueue);
            while (tmpQueue.Count > 0) {
                NetPacket! np     = (NetPacket!)this.tmpQueue.Dequeue();
                np.AdapterContext = adapter;
                rxQueue.Enqueue(np);
            }
            Core.Instance().SignalInboundPackets();
            return NetStatus.Code.RT_OK;
        }
    } // DeMultiplexer
} // NetStack
// End
