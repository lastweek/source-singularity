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
using System.Diagnostics;
using System.Threading;
using System.Collections;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

#if !SINGULARITY
using System.Net;
#endif

using System.Net.IP;
using Drivers.Net;

namespace NetStack.Runtime
{
    ///
    // This is the base class for all sessions.
    // The session represent an instance of a specific
    // protocol and is usually embedded in a higher level
    // library abstraction.
    // 
    public class Session : IDisposable
    {
        private static uint uids = 0;
        private uint   uid = uids++;

        public uint Uid { get { return uid; } }

        // the session identifiers
        private IPv4      localAddress;
        private ushort    localPort;
        private IPv4      remoteAddress;
        private ushort    remotePort;

        private bool      disposed;

        private  IProtocol! protocol;    // the session's protocol

        private Multiplexer mux;

        // the session's queues
        internal ArrayList! outQueue;
        private int outQueueCapacity;

        internal ArrayList! inQueue;
        private int inQueueCapacity;

        private bool outQueuePaused;    // used to pause outbound queue while
                                        // awaiting ARP response.

        // get some info
        public IPv4   RemoteAddress { get { return remoteAddress; } }
        public ushort RemotePort    { get { return remotePort; } }

        public IPv4   LocalAddress  { get { return localAddress; } }
        public ushort LocalPort     { get { return localPort; } }

        public IProtocol! Protocol  { get { return protocol; } }

        public Session(IProtocol! protocol, int outQueueSize, int inQueueSize)
        {
            this.protocol         = protocol;
            this.outQueue         = new ArrayList(outQueueSize);
            this.inQueue          = new ArrayList(inQueueSize);
            this.outQueueCapacity = outQueueSize;
            this.inQueueCapacity  = inQueueSize;
            this.outQueuePaused   = false;
            this.disposed         = false;
            base();
        }

        ~Session()
        {
            if (!disposed)
                Dispose();
        }

        public void Dispose()
        {
            if (!disposed) {
                Core.Instance().DeregisterSession(protocol, this);
                DrainQueue(inQueue);
                DrainQueue(outQueue);
            }
            disposed = true;
        }

        public void ReInitialize(IProtocol! protocol)
        {
            Core.Instance().DeregisterSession(protocol, this);

            this.protocol       = protocol;
            this.outQueuePaused = false;
            this.disposed       = false;
            this.localAddress   = IPv4.Zero;
            this.remoteAddress  = IPv4.Zero;
            this.localPort      = 0;
            this.remotePort     = 0;
            this.disposed       = false;
            DrainQueue(this.outQueue);
            DrainQueue(this.inQueue);
        }

        internal void DrainQueue(ArrayList! queue)
        {
            lock (queue.SyncRoot) {
                if (queue == this.inQueue) {
                    while (queue.Count > 0) {
                        NetPacket! p = (NetPacket!)queue[0];
                        queue.Remove(0);
                        Core.Instance().TheDemux.TakeFreePacket(p);
                    }
                }
                else {
                    queue.Clear();
                }
            }
        }

        public bool OutQueuePaused
        {
            get { return outQueuePaused; }
            set { outQueuePaused = value; }
        }

        [ Conditional("DEBUG_SESSION") ]
        private static void DebugPrint(string format, params object [] args)
        {
            Core.Log("Session: ");
            Core.Log(format, args);
        }

        // Multiplexer, if set packets are sent via multiplexer
        public Multiplexer BoundMux
        {
            get { return mux; }
            set { mux = value; }
        }

        internal void SetRemoteEndPoint(IPv4 remoteAddress, ushort remotePort)
        {
            this.remoteAddress = remoteAddress;
            this.remotePort    = remotePort;
        }

        public bool IsLocalAddress(IPv4 address)
        {
            IPModule ipModule = Core.Instance().GetProtocolByName("IP")
                as IPModule;
            if (ipModule == null) {
                return false;
            }
            return ipModule.HostConfiguration.IsLocalAddress(address);
        }

        internal bool SetLocalEndPoint(IPv4 address, ushort port)
        {
            if (address != IPv4.Zero && !IsLocalAddress(address)) {
                // Invalid address
                return false;
            }

            if (address == IPv4.Zero &&
                remoteAddress != IPv4.Zero)
            {
                IPModule ipModule = (IPModule!)Core.Instance().GetProtocolByName("IP");
                RouteEntry e = ipModule.HostConfiguration.RoutingTable.Lookup(remoteAddress);

                if (e != null) {
                    address = e.InterfaceAddress;
                    DebugPrint("local address now {0}\n", address);
                }
                else {
                    DebugPrint("No route for {0}\n", remoteAddress);
                }
            }

            localAddress = address;
            if (this.LocalPort != port) {
                Core.Instance().ChangeSessionLocalPort(this, port);
                DebugPrint("Local port {0} {1}\n", port, localPort);
            }
            return true;
        }

        /// <summary>
        /// This method should only be called by Core.ChangeSessionLocalPort
        /// which co-ordinates port allocations.
        /// </summary>
        internal void SetLocalPort(ushort newPort)
        {
            this.localPort = newPort;
        }
        // Is this session valid for users to read from?
        // This can become false for TCP sessions when the
        // remote entity closes their half of the duplex
        // connection
        internal virtual bool IsSessionValidForUserRead()
        {
            return true;
        }

        // Is this session valid for users to write to?
        // This can become false for TCP sessions when
        // the user has closed the local side of the duplex
        // connection
        internal virtual bool IsSessionValidForUserWrite()
        {
            return true;
        }

        // get a packet from a queue
        // the session may be shared in user land (so we need the sync)
        // since the core also use this version we pass a bool to differentiate between
        // stack calls/user calls
        // we let the user read packets if exist event though the session
        // is closing (for instance a web server sends the data and disconnect)
        protected NetPacket DequeuePacket(ArrayList! queue,
                                          TimeSpan   timeout)
        {
            Debug.Assert(queue == inQueue || outQueuePaused == false);

            NetPacket packet  = null;

            lock (queue.SyncRoot) {
                if ((timeout == TimeSpan.Zero) && queue.Count == 0) {
                    // Don't sleep
                    return null;
                }

                while (queue.Count == 0) {
                    if (Monitor.Wait(queue.SyncRoot, timeout) == false) {
                        return null;
                    }
                }

                packet = (NetPacket)queue[0];
                queue.RemoveAt(0);
                Monitor.PulseAll(queue.SyncRoot);
                Debug.Assert(packet != null);
                return packet;
            }
        }

        private int GetQueueCapacity(ArrayList! queue)
        {
            // Work around for lack of abstract in queues (grrr!)
            DebugStub.Assert(queue == this.outQueue || queue == this.inQueue);
            if (queue == this.outQueue) {
                return this.outQueueCapacity;
            }
            else {
                return this.inQueueCapacity;
            }
        }

        // put a packet in a Queue and notify waiters
        // return false if the packet was thrown
        protected bool EnqueuePacket(ArrayList! queue,
                                     NetPacket! packet,
                                     bool       toBlock)
        {
            lock (queue.SyncRoot) {
                if (queue.Count >= queue.Capacity && !toBlock) {
                    return false;
                }

                int queueCapacity = GetQueueCapacity(queue);
                while (queue.Count >= queueCapacity)
                    // Potential fix to stop accepting users packets until
                    // destination is ARPed   
                       //|| (queue == this.outQueue && this.outQueuePaused)   
                {
                    // Note In TcpSessions the queue length may
                    // be greater than queueCapacity because of
                    // retransmits.  Retransmits are inserted at
                    // the head of the sessions outbound queue
                    // and we don't want any more packets
                    // enqueued until we've drained below the
                    // desired water level.
                    Monitor.Wait(queue.SyncRoot);
                }

                // Enqueue packet then set packet session
                // context.  The context can be used to block
                // the sessions outqueue while waiting for
                // events such as ARP
                // (IPModule.BlockAssociatedSession does this
                // for instance)
                queue.Add(packet);
                packet.SessionContext = this;

                Monitor.PulseAll(queue.SyncRoot);
            }

            if (queue == this.outQueue) {
                // Signal to the core that outbound queues need
                // servicing...
                Core.Instance().SignalOutboundPackets();
            }
            else {
                // Race: DebugStub.Assert(packet.AdapterContext != null);
            }

            return true;
        }

        // Determine whether the queue is empty without sleeping
        internal bool QueueIsEmpty(ArrayList! queue)
        {
            lock (queue.SyncRoot) {
                return queue.Count == 0;
            }
        }

        protected bool PollQueueNotEmpty(ArrayList! queue, int timeoutMillis)
        {
            if (timeoutMillis < 0) {
                return false;
            }

            DateTime startTime = DateTime.Now;
            TimeSpan timeout   = TimeSpan.FromMilliseconds(timeoutMillis);
            TimeSpan remain    = timeout;
            bool     result    = false;

            if (Monitor.TryEnter(queue.SyncRoot, remain) == false) {
                return false;
            }

            remain = startTime + timeout - DateTime.Now;

            while (remain >= TimeSpan.Zero && result == false) {
                Monitor.PulseAll(queue.SyncRoot);

                if (Monitor.Wait(queue.SyncRoot, remain) == false) {
                    // Timed-out waiting for lock
                    return false;
                }

                result = (queue.Count > 0);
                remain = startTime + timeout - DateTime.Now;
            }

            Monitor.PulseAll(queue.SyncRoot);
            Monitor.Exit(queue.SyncRoot);
            return result;
        }

        protected bool PollQueueNotFull(ArrayList! queue, int timeoutMillis)
        {
            if (timeoutMillis < 0) {
                return false;
            }

            DateTime startTime = DateTime.Now;
            TimeSpan timeout   = TimeSpan.FromMilliseconds(timeoutMillis);
            TimeSpan remain    = timeout;
            bool     result    = false;

            if (Monitor.TryEnter(queue.SyncRoot, remain) == false) {
                return false;
            }

            remain = startTime + timeout - DateTime.Now;

            while (remain >= TimeSpan.Zero && result == false) {
                Monitor.PulseAll(queue.SyncRoot);
                if (Monitor.Wait(queue.SyncRoot, remain) == false) {
                    // Timed-out waiting for lock
                    return false;
                }
                result = (queue.Count < queue.Capacity);
                remain = startTime + timeout - DateTime.Now;
            }

            Monitor.PulseAll(queue.SyncRoot);
            Monitor.Exit(queue.SyncRoot);
            return result;
        }

        // this method is called by the Core to handle outgoing queues, should
        // be override by concrete sessions if necessary
        virtual internal NetPacket GetPacket(ArrayList! queue,
                                             bool       toBlock,
                                             TimeSpan   timeout)
        {
            return DequeuePacket(queue, timeout);
        }

        virtual internal bool PutPacket(ArrayList! queue,
                                        NetPacket! packet,
                                        bool       toBlock)
        {
            return (EnqueuePacket(queue, packet, toBlock));
        }

        virtual internal NetStatus OnReceive(object sender, NetPacket! pkt, object ctx)
        {
            return NetStatus.Code.PROTOCOL_OK;
        }

        //--------------------------------------------
        // User interface
        //--------------------------------------------

        virtual public byte[] PollCopyData(TimeSpan timeout)
        {
            // If we're out of packets and there will never be anymore,
            // don't try to sleep for any!
            if (QueueIsEmpty(inQueue) && !IsSessionValidForUserRead()) {
                return null;
            }
            // else return the enqueued packets

            NetPacket netPacket = DequeuePacket(inQueue, timeout);

            if (netPacket != null) {
                DebugStub.Assert(netPacket.AdapterContext != null);
                byte [] userData = netPacket.ToUser();
                Core.Instance().TheDemux.TakeFreePacket(netPacket);
                return userData;
            }
            return null;
        }

        public byte[] in ExHeap PollData(TimeSpan timeout)
        {
            // Duplicate of PollData, but copies to shared heap buffer.
            if (!IsSessionValidForUserRead()) {
                return null;
            }
            // else return the enqueued packets

            NetPacket netPacket = DequeuePacket(inQueue, timeout);

            if (netPacket != null) {
                byte []! in ExHeap userData =
                    Bitter.FromByteArray((!)netPacket.GetRawData(),
                                         netPacket.Position,
                                         netPacket.Available);
                Core.Instance().TheDemux.TakeFreePacket(netPacket);
                return userData;
            }
            return null;
        }

        public byte[] in ExHeap ReadData()
        {
            return PollData(Timeout.Infinite);
        }

        // read data, if no data is ready - blocks
        virtual public byte[] ReadCopyData()
        {
            return PollCopyData(Timeout.Infinite);
        }

        // write a data to a session,
        // if the queue has no room - blocks
        // return the number of written data
        // TBC: enforce data size limits
        // should be implemented by specific sessions
        // to create protocol specific packets
        virtual public int WriteData(byte[]! data)
        {
            if (!IsSessionValidForUserWrite()) {
                return -1;
            }

            byte[] pktData = new byte[data.Length];
            Array.Copy(data, pktData, data.Length);
            NetPacket pkt = new NetPacket(pktData);

            if (false == EnqueuePacket(outQueue, pkt, true))
                return -1;

            return data.Length;
        }

        // Perform a graceful shutdown (nonblocking)
        virtual public bool Close()
        {
            return false;
        }

        // Perform an immediate, hard shutdown
        virtual public bool Abort()
        {
            // By default, assume there is no distinction
            // between shutdown types
            return Close();
        }

        public class LocalPortComparer : IComparer
        {
            public int Compare (Object left, Object right)
            {
                Session lhs = left as Session;
                Session rhs = right as Session;
                if (lhs == null) {
                    return (rhs == null) ? 0 : -1;
                }
                if (rhs == null) {
                    return +1;
                }
                if (lhs.LocalPort < rhs.LocalPort) {
                    return -1;
                }
                if (lhs.LocalPort > rhs.LocalPort) {
                    return +1;
                }
                return 0;
            }
        }
    }

    // single sessions table.
    // hashed by the protocol interface
    public class SessionsTable : Hashtable
    {
    }
}
