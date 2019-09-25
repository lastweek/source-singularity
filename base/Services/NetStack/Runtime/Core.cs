// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

// #define DEBUG_CORE

using System;
using System.Collections;
using System.Diagnostics;
using System.Net.IP;
using System.Threading;

using Microsoft.Singularity;

using Drivers.Net;

using NetStack.Common;
using NetStack.NetDrivers;
using NetStack.Protocols;

namespace NetStack.Runtime
{
    ///
    // This is the heart of the networking stack.
    // - A single thread inside the core handles
    // packet reception, Qos demultiplexing and
    // later on multiplexing on a specific protocol queue.
    // - The thread also handles user send & receive in order
    // to avoid reentrancy deadlocks etc.
    // - The Runtime uses an asynchronous IO in order to
    // avoid locking and denial of service.
    // - The Core's thread, never invokes user's callbacks
    // directly, the user can poll for a message or get
    // his thread to sleep, waiting for a new message event.
    // 
    public class Core : INetModule
    {
        private bool activated = false;

#if THREAD_POOL
        private const int workerThreads = 16;
        private const int maxWorkItems = workerThreads * 128;
        private NetStackThreadPool! threadPool;
#endif

        // the single core object
        protected static Core! instance = new Core();

        // disable default lazy creation (beforefieldinit)
        static Core() {}

        private Core()
        {
            worker               = null;
            stopped              = false;
            protocols            = new SortedList();
            packetTypes          = new PacketTypes();
            adapters             = new ArrayList();
            adapterNextId        = 0;
            theDispatcher        = new Dispatcher();
            muxTable             = new ArrayList();
            sessions             = new SessionsTable();
            outboundPacketsEvent = new AutoResetEvent(false);
            inboundPacketsEvent  = new AutoResetEvent(false);
#if THREAD_POOL
            threadPool           =
                new NetStackThreadPool(workerThreads, maxWorkItems);
#endif

            base();
            // NB The demux is initialized when the first adapter is
            // registered as it depends on the Core Instance being
            // valid and it's not within this constructor.
            // theDemux = null;
        }

        // get the single core instance
        public static Core! Instance()
        {
            return instance;
        }

#if THREAD_POOL
        public NetStackThreadPool! ThreadPool {
            get { return threadPool; }
        }
#endif

        [ System.Diagnostics.Conditional("DEBUG_CORE") ]
        private static void DebugPrint(string format, params object[] args)
        {
            DebugStub.Print("Core: {0}",
                            __arglist(String.Format(format, args))
                            );
        }

        // create a session of a specific protocol
        public Session CreateSession(string protocolName)
        {
            IProtocol protocol = GetProtocolByName(protocolName);
            if (protocol == null) {
                return null;
            }
            return (protocol.CreateSession());
        }

        // register a new session in the runtime
        // notice that multiple user threads can register new
        // sessions (multiple writers).
        // In the Meanwhile the internal thread can scan the
        // sessions in order to HandleOutgoingSessions
        internal void RegisterSession(IProtocol! protocol, Session newSession)
        {
            lock (sessions.SyncRoot) {
                if (!sessions.Contains(protocol)) {
                    ArrayList sessionList = new ArrayList();
                    sessionList.Add(newSession);
                    sessions[protocol] = sessionList;
                }
                else {
                    ArrayList! sessionList = (ArrayList!)sessions[protocol];
                    lock (sessionList.SyncRoot) {
                        if (!sessionList.Contains(newSession)) {
                            sessionList.Add(newSession);
                        }
                    }
                }
            }
        }

        // Deregister a session
        internal void DeregisterSession(IProtocol! protocol, Session sessionToRemove)
        {
            lock (sessions.SyncRoot) {
                if (!sessions.Contains(protocol))
                    Core.Panic("Error: Can't deregister a session for an unknown protocol!");
                else {
                    ArrayList sessionList = (ArrayList!)sessions[protocol];
                    lock (sessionList.SyncRoot) {
                        sessionList.Remove(sessionToRemove);
                    }
                }
            }
        }

        private static int FindFreePort(ArrayList sessions)
        {
            const int PortMin = 1024;
            const int PortMax = 65535;

            if (sessions == null || sessions.Count == 0)
                return PortMin;

            int lastPort = PortMin;
            foreach (Session! s in sessions) {
                if (s.LocalPort - 1 > lastPort)
                    return s.LocalPort - 1;
                if (lastPort > PortMin)
                    lastPort = s.LocalPort;
            }
            lastPort++;
            if (lastPort > PortMax)
                return -1;
            return lastPort;
        }

        internal bool ChangeSessionLocalPort(Session! session, int newPort)
        {
            ArrayList tcpSessions = Core.Instance().GetSessions(session.Protocol);

            // If no sessions registered yet, just do it...
            if (tcpSessions == null) {
                if (newPort == 0) {
                    newPort = FindFreePort(tcpSessions);
                }

                session.SetLocalPort((ushort) newPort);
                return true;
            }

            // Take care to acquire the global sessions lock before the
            // more specific lock for the TCP sessions list
            lock (sessions.SyncRoot) {
                lock (tcpSessions.SyncRoot) {
                    if (newPort == 0) {
                        // Find FreePort
                        newPort = FindFreePort(tcpSessions);
                    }

                    if (newPort < 0) {
                        return false;
                    }

                    // Deregister session
                    Core.Instance().DeregisterSession(session.Protocol, session);

                    // Reregister session
                    session.SetLocalPort((ushort) newPort);
                    Core.Instance().RegisterSession(session.Protocol, session);
                    return true;
                }
            }
        }

        internal ArrayList GetSessions(IProtocol! protocol)
        {
            return (ArrayList)sessions[protocol];
        }

        public int GetSessionCount(IProtocol! protocol)
        {
            ArrayList tmp = (ArrayList)sessions[protocol];
            if (tmp != null) return tmp.Count;
            return 0;
        }

        private bool HandleSessionsOutboundQueue(Session! s)
        {
            DebugPrint("HandleSession {0} paused = {1} queued {2}\n",
                       s.Uid, s.OutQueuePaused, s.outQueue.Count);

            // Session may be paused if waiting on reception
            // event, e.g. ARP response triggered by first
            // outbound packet.
            if (s.OutQueuePaused == true) {
                return false;
            }

            NetPacket packet = s.GetPacket(s.outQueue, false, TimeSpan.Zero);
            if (packet == null) {
                return false;
            }

            if (packet.Mux == null)
                packet.Mux = s.BoundMux;
            s.Protocol.OnProtocolSend(packet);

            // NOTE: Special case; if this is a TCP session
            // and we just transmitted the very last packet it will
            // ever send, help out with the shutdown process by
            // signalling this session closed.
            TcpSession tcpS = s as TcpSession;

            if ((tcpS != null) &&
                (tcpS.currentState == TCPFSM.CLOSED) &&
                (tcpS.outQueue.Count == 0))
            {
                // That was the very last TCP frame for this session
                tcpS.closedEvent.Set();
            }

            return true;
        }

        private bool IsAnyMuxBackLogged()
        {
            foreach (Multiplexer! m in this.muxTable) {
                if (m.IsBackLogged) {
                    DebugPrint("BackLogged\n");
                    return true;
                }
            }
            return false;
        }

        private int GetMaxOutgoingPackets()
        {
            int n = this.muxTable.Count > 0 ? ((Multiplexer!)this.muxTable[0]).FreeBufferSpace : 0;
            for (int i = 1; i < this.muxTable.Count; i++) {
                n = Math.Min(n,
                             ((Multiplexer!)this.muxTable[i]).FreeBufferSpace);
            }
            return n;
        }

        static Random picker = new Random();

        // handle outgoing queues...
        // we handle outgoing queues of user sessions in two cases:
        // 1. periodically using a timer
        // 2. after handling received packets
        internal NetStatus HandleOutgoingQueues(Dispatcher.CallbackArgs unused)
        {
            lock (sessions.SyncRoot) {
                DebugPrint("++++ OUTGOING QUEUE PASS ++++\n");
                int todo = GetMaxOutgoingPackets();

                DebugPrint("Driving Sessions (mux avail = {0})\n",
                           GetMaxOutgoingPackets());

                DebugPrint("Mux max packets = {0}\n", todo);
                bool morePackets = true;
                while (todo > 0 && morePackets) {
                    morePackets = false;

                    // TODO: Shuffle order
                    // sessions are visited for some concept of
                    // fairness.  This probably requires
                    // redesigning The protocol session storage
                    // because it's currently a hashtable and
                    // this does not give a particularly
                    // effective means to shuffle / rotate
                    // entries.

                    foreach (IProtocol! p in sessions.Keys) {
                        ArrayList! x = (ArrayList!)sessions[p];
                        int limit  = x.Count;
                        int offset = picker.Next(x.Count);
                        for (int i = 0; i < limit; i++) {
                            Session! s = (Session!)x[(i + offset) % limit];
                            if (HandleSessionsOutboundQueue(s)) {
                                if (--todo == 0)
                                    goto DoneDrivingQueues;
                                morePackets |= true;
                            }
                        }
                    }

                    // To be really drive the outbound queue
                    // todo = GetMaxOutgoingPackets();
                }

              DoneDrivingQueues:
                DebugPrint("Driving Mux (mux avail = {0})\n",
                           GetMaxOutgoingPackets());

                for (int i = this.muxTable.Count - 1; i >= 0; i--) {
                    Multiplexer! m = (Multiplexer!)this.muxTable[i];
                    m.PushSendBuffer();
                }

                DebugPrint("Done Driving Mux (mux avail = {0})\n",
                           GetMaxOutgoingPackets());

                DebugPrint("---- OUTGOING QUEUE PASS ----\n");

                if (morePackets) {
                    // Make sure we wake up again
                    SignalOutboundPackets();
                }
            }

            return NetStatus.Code.RT_OK;
        }

        // INetModule interface
        // ---------------------
        // get the module's name
        public string ModuleName  { get { return "Core"; } }

        // get the modules version
        public ushort ModuleVersion { get { return 0x01; } }  // 0.1

        public bool Initialize(ProtocolParams args)
        {
            return true;
        }

        // start module activity, module specific.
        // it is called by the runtime
        public bool StartModule()
        {
            if (stopped) {
                worker.Start();
                stopped = false;
            }
            return true;
        }

        // stop module activity, module specific.
        // it is called by the runtime
        public bool StopModule()
        {
            if (!stopped) {
                // Signal stop to dispatcher since worker thread
                // is running dispatcher.
                theDispatcher.Stop();
                worker.Join();
                stopped = true;
            }
            return true;
        }

        // destroy module, free unmanaged resources if any.
        // it is called by the runtime
        public bool DestroyModule()
        {
            StopModule();
            return true;
        }

        // ------------------------------------------------------
        // Core's data
        // ------------------------------------------------------

        // Sorted List of adapters <adapter, adapterDetails>
        private ArrayList! adapters;

        // Id number of next adapter added
        private int adapterNextId;

        // the protocol list
        private SortedList! protocols;

        // the packet types list
        public PacketTypes packetTypes;

        // out internal thread
        protected Thread worker;

        // should the thread stop?
        protected bool stopped;

        // the dispatcher instance, implements the event driven logic
        protected Dispatcher! theDispatcher;
        internal Dispatcher! TheDispatcher { get { return theDispatcher; } }

        // the demux object, intercepts packets as they come and
        // classifies them into flows
        protected DeMultiplexer theDemux;
        internal DeMultiplexer! TheDemux { get { return theDemux; } }

        private ArrayList muxTable;

        // the runtime active sessions
        protected SessionsTable sessions;
        internal SessionsTable Sessions { get { return sessions; } }

        // This event is used to signal that there are outbound packets
        private AutoResetEvent outboundPacketsEvent;
        private AutoResetEvent inboundPacketsEvent;

        // ------------------------------------------------------
        // Core specific methods
        // ------------------------------------------------------

        internal class AdapterArgs : Dispatcher.CallbackArgs
        {
            internal IAdapter adapter;
            internal string   deviceName;
            internal int      fwQueueSize;

            internal AdapterArgs(IAdapter theAdapter,
                                 string   theDeviceName,
                                 int      theQueueSize)
            {
                adapter     = theAdapter;
                deviceName  = theDeviceName;
                fwQueueSize = theQueueSize;
            }
        }

        private NetStatus RegisterAdapterInternal(Dispatcher.CallbackArgs args)
        {
            AdapterArgs aa = (AdapterArgs!)args;

            if (theDemux == null) {
                theDemux = new DeMultiplexer();
            }

            Core.Log("Registering {0}", aa.deviceName);
            adapters.Add(new AdapterInfo(aa.adapter, aa.deviceName));

            Multiplexer mux = new Multiplexer(new Queue(aa.fwQueueSize),
                                              aa.adapter);
            muxTable.Add(mux);

            theDispatcher.AddCallback(
                new Dispatcher.Callback(mux.OnAdapterSendComplete),
                null, aa.adapter.GetWriteHandle()
                );

            theDispatcher.AddCallback(
                new Dispatcher.Callback(theDemux.OnAdapterReceive),
                new DemuxAdapterArgs(aa.adapter), aa.adapter.GetReadHandle()
                );

            Core.Log("Registered adapter: {0}", aa.deviceName);

            return NetStatus.Code.RT_OK;
        }

        private NetStatus
        DeregisterAdapterInternal(Dispatcher.CallbackArgs args)
        {
            AdapterArgs aa = (AdapterArgs!)args;
            IAdapter    ad = aa.adapter;

            // XXX IP specific hack - should be replaced by a
            // message to each module or some such.
            IPModule ip = (IPModule)protocols["IP"];
            if (ip != null) {
                ip.HostConfiguration.Bindings.Flush(ad);
            }

            theDispatcher.RemoveCallback(ad.GetReadHandle());
            theDispatcher.RemoveCallback(ad.GetWriteHandle());

            foreach (AdapterInfo! ai in adapters) {
                if (ai.Adapter == ad) {
                    adapters.Remove(ad);
                    break;
                }
            }

            foreach (Multiplexer! m in muxTable) {
                if (m.Adapter == ad) {
                    muxTable.Remove(m);
                }
            }

            Core.Log("Deregistered adapter: {0}", aa.deviceName);

            return NetStatus.Code.RT_OK;
        }

        public void RegisterAdapter(IAdapter ad,
                                    string   nsName,
                                    int      fwQueueSize)
        {
            theDispatcher.AddCallback(
                new Dispatcher.Callback(this.RegisterAdapterInternal),
                new AdapterArgs(ad, nsName, fwQueueSize)
                );
        }

        public void DeregisterAdapter(IAdapter ad)
        {
            theDispatcher.AddCallback(
                new Dispatcher.Callback(this.DeregisterAdapterInternal),
                new AdapterArgs(ad, null, 0)
                );
        }

        public IAdapter GetAdapterByDeviceName(string deviceName)
        {
            foreach (AdapterInfo! ai in adapters) {
                if (ai.DeviceName == deviceName) {
                    return ai.Adapter;
                }
            }
            return null;
        }

        /// <summary>
        /// Get collection of AdapterInfo instances associated
        /// with adapters.
        /// </summary>
        public ICollection! GetAdapterInfoCollection()
        {
            return adapters;
        }

        // return the mux for the given adapter
        internal Multiplexer GetMuxForAdapter(IAdapter ad)
        {
            foreach (Multiplexer! m in muxTable) {
                if (m.Adapter == ad) {
                    return m;
                }
            }
            return null;
        }

        public bool RegisterProtocol(IProtocol! protocol)
        {
            try {
                protocols[protocol.ModuleName] = protocol;
                return true;
            }
            catch (ArgumentException) {
                return false;
            }
        }

        public bool DeregisterProtocol(IProtocol! protocol)
        {
            IProtocol found = protocols[protocol.ModuleName] as IProtocol;
            if (found == protocol) {
                protocols.Remove(protocol.ModuleName);
                return true;
            }
            return false;
        }

        // get a protocol reference identified by name
        public IProtocol GetProtocolByName(string protocolName)
        {
            if (protocolName == null)
                return null;
            return protocols[protocolName] as IProtocol;
        }

        ///
        // Dispatch an incoming packets
        // this method actually drives the
        // packet through the stack's modules.
        // 
        private NetStatus DispatchPacket(NetPacket! pkt)
        {
            // look at the ethernet headers...
            EthernetAddress src, dst;
            ushort prot = 0;

            if (EthernetFormat.Read(pkt, out src, out dst, out prot)) {
                IProtocol protocol = packetTypes.GetHandler(prot);
                if (protocol != null) {
                    NetStatus res = protocol.OnProtocolReceive(pkt);
                    if (res == NetStatus.Code.PROTOCOL_PROCESSING) {
                        return NetStatus.Code.RT_OK;
                    }
                    if (res == NetStatus.Code.PROTOCOL_PANIC) {
                        Panic(String.Format("Protocol {0} panicked!!!",
                                            protocol.ModuleName));

                        // if the protocol has finished with the packet, return it!
                    }
                }
            }

            // no handler, return the packet
            theDemux.TakeFreePacket(pkt);
            return NetStatus.Code.RT_DROP_NO_HANDLER;
        }

        // get the protocol interface from an ID
        // (ignore packet level protocols)
        internal IProtocol GetProtocolFromID(byte prot)
        {
            IProtocol p = null;

            // checkout the protocol list for this one
            foreach (string retProtName in protocols.Keys) {
                p = (IProtocol!)protocols[retProtName];
                ushort pID = p.GetProtocolID();
                if (EthernetFormat.IsEthernetProtocol(pID))
                    continue;
                if (prot == (byte)pID)
                    break;
            }
            return p;
        }

        public static void Panic(string reason)
        {
            Core.Log("NetStack Panic: {0}", reason);
            DebugStub.Break();
#if !SINGULARITY
            Environment.Exit(1);
#endif
        }

        public static void Panic(string format, params object[] args)
        {
            Core.Panic(String.Format(format, args));
        }

        public static void Log(string message)
        {
            DebugStub.Print("NetStack: {0}\n", __arglist(message));
        }

        public static void Log(string format, params object[] args)
        {
            Core.Log(String.Format(format, args));
        }

        public static void LogData(byte []! Data)
        {
            LogData(Data, 0, Data.Length);
        }

        public static void LogData(byte []! data, int offset, int length)
        {
            length = Math.Min(length, data.Length);

            for (int i = offset; i < length; i += 16) {
                DebugStub.Print("{0:x4}  ", __arglist(i));
                int n = Math.Min(16, length - i) + i;
                for (int j = i; j < n; j++)
                    DebugStub.Print("{0:x2} ", __arglist(data[j]));
                for (int j = n; j != i + 16; j++)
                    DebugStub.Print("   ");
                DebugStub.Print("  ");
                for (int j = i; j < n; j++) {
                    char c = '.';
                    if (data[j] > 31 && data[j] < 128)
                        c = (char)data[j];
                    DebugStub.Print("{0}", __arglist(c));
                }
                DebugStub.Print("\n");
            }
        }

        // the core's activation routine, beware...
        // (this is a go/no-go method)
        public void Activate()
        {
            // Core.Log("NetStack Core Runtime Active...");

            // since all the protocols are initialized
            // start them up (start module)
            foreach (string protName in protocols.Keys) {
                IProtocol protocol = (IProtocol!)protocols[protName];
                if (protocol.StartModule() == false) {
                    Core.Panic("Module {0} failed to start, exit.",
                               protocol.ModuleName);
                }
            }

            // register a callback to handle outgoing queues
            theDispatcher.AddCallback(
                new Dispatcher.Callback(this.HandleOutgoingQueues),
                null, outboundPacketsEvent
                );

            // register a callback to handle incoming queue
            theDispatcher.AddCallback(
                new Dispatcher.Callback(this.HandleIncomingQueue),
                null, inboundPacketsEvent
                );

            // create the worker
            // now, pass control to the dispatcher...
            worker = new Thread(new ThreadStart(theDispatcher.Execute));
            worker.Start();
            activated = true;
        }

        public void ProvisionDemux(int freePacketCount, int packetSize)
        {
            if (activated == true)
                Core.Panic("Cannot provision demux after Core.Activate()");
            theDemux = new DeMultiplexer();
        }

        private NetStatus HandleIncomingQueue(Dispatcher.CallbackArgs unused)
        {
            const int PacketsToHandleBeforeYield = 25;

            int n = PacketsToHandleBeforeYield;
            while (n-- > 0 && theDemux.PacketsReady) {
                NetPacket p = theDemux.GetReceivedPacket();
                if (p == null) {
                    break;
                }
                DispatchPacket(p);
            }
            if (theDemux.PacketsReady) {
                SignalInboundPackets();
            }
            return NetStatus.Code.RT_OK;
        }

        // Call this to indicate that outbound packets are waiting
        public void SignalOutboundPackets()
        {
            outboundPacketsEvent.Set();
        }

        // Call this to indicate that outbound packets are waiting
        public void SignalInboundPackets()
        {
            inboundPacketsEvent.Set();
        }
    }
}
