// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

// #define DEBUG_ARP

using NetStack.Common;
using System;
using System.Diagnostics;
using System.Collections;
using System.Text;

#if !SINGULARITY
using System.Net;
#endif

using System.Net.IP;
using Drivers.Net;
using NetStack.Protocols;

using Microsoft.Singularity;

namespace NetStack.Runtime
{
    /// <summary>
    /// Callback for Arp Requests.
    ///
    /// This delegate is invoked when the ArpModule gets a
    /// response to a request.
    ///
    /// <param name="answer">Ethernet address corresponding to
    /// requested IP address if a response is received,
    /// EthernetAddress.Zero if request timed out.</param>
    /// </summary>
    public delegate void ArpRequestCallback(IPv4            ipAddress,
                                            EthernetAddress macAddress,
                                            object          cookie);

    ///<summary>
    ///This module implements the ARP protocol.
    ///</summary>
    public class ArpModule : IProtocol
    {
        private class PendingRequest
        {
            public IPv4               address;
            public ArpRequestCallback callback;
            public object             cookie;
            public DateTime           expiry;

            public PendingRequest(IPv4               address,
                                  ArpRequestCallback callback,
                                  object             cookie,
                                  DateTime           expiry)
            {
                this.address  = address;
                this.callback = callback;
                this.cookie   = cookie;
                this.expiry   = expiry;
            }
        }

        /// <summary>
        /// Class used to hold expiration time of Request timeouts.
        /// </summary>
        private class TimeoutArgument : Dispatcher.CallbackArgs
        {
            public DateTime now;

            public TimeoutArgument(DateTime when)
            {
                now = when;
            }
        }

        // ARP variables
        private ArpTable arpTable = null;
        private IPModule ipModule = null;
        private ArrayList pendingRequests; // <expiry, PendingRequest>

        // Pending request polling period
        private static readonly TimeSpan PollPeriod = TimeSpan.FromSeconds(1);

        // INetModule interfaces
        // ------------------------
        string INetModule.ModuleName  { get { return "ARP"; } }
        ushort INetModule.ModuleVersion { get { return 0x01; } }  // 0.1

        [Conditional("DEBUG_ARP")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("ARPModule: {0}",
                            __arglist(
                                string.Format(format, arguments))
                            );
        }

        // called by the runtime when
        // the protocol should be started
        public bool StartModule()
        {
            DebugPrint("Starting ARP.\n");

            // we have the request...
            // Notice: can be ARP_REQUEST or ARP_RESPONSE
            ipModule = Core.Instance().GetProtocolByName("IP") as IPModule;
            if (ipModule == null) {
                return false;
            }

            // ask for an aging[msec] timer
            DateTime then = DateTime.UtcNow + ArpTable.AgePeriod;
            Core.Instance().TheDispatcher.AddCallback(
                new Dispatcher.Callback(OnAgingTimer), null, (ulong)then.Ticks
                );
            return true;
        }

        // make the arp table entries older...
        // currently arg is null
        public NetStatus OnAgingTimer(Dispatcher.CallbackArgs arg)
        {
            arpTable.AgeTable();

            DateTime then = DateTime.UtcNow + ArpTable.AgePeriod;
            Core.Instance().TheDispatcher.AddCallback(
                new Dispatcher.Callback(OnAgingTimer), null, (ulong)then.Ticks
                );

            return NetStatus.Code.RT_OK;
        }

        public bool StopModule()
        {
            return true;
        }

        public bool DestroyModule()
        {
            arpTable = null;
            return true;
        }

        // IProtocol interfaces
        // ------------------------
        public bool Initialize(ProtocolParams parameters)
        {
            Debug.Assert(parameters == null || parameters["name"]=="ARP");

            int size = ProtocolParams.LookupInt32(parameters, "cacheSize",
                                                  128);
            int age  = ProtocolParams.LookupInt32(parameters, "max-age",
                                                  ArpTable.MaxAge);
            arpTable = new ArpTable(size, age, this);
            pendingRequests = new ArrayList();

            Core core = Core.Instance();
            core.RegisterProtocol(this);
            if (!core.packetTypes.RegisterTypeHandler(PacketTypes.ARP, this)) {
                core.DeregisterProtocol(this);
                return false;
            }
            return true;
        }

        public ushort GetProtocolID()
        {
            return (EthernetFormat.PROTOCOL_ARP);
        }

        public Session CreateSession()
        {
            return null;
        }

        ///
        // ARP logic: see RFC 826 http://www.faqs.org/rfcs/rfc826.html
        // 
        public NetStatus OnProtocolReceive(NetPacket! pkt)
        {
            NetStatus res = NetStatus.Code.PROTOCOL_OK;
            Debug.Assert(pkt!=null);

            ArpFormat.Type opcode;
            EthernetAddress senderMAC, targetMAC;
            IPv4 senderIP, targetIP;

            bool ok = ArpFormat.Read(pkt, out opcode,
                                     out senderMAC, out senderIP,
                                     out targetMAC, out targetIP);
            DebugPrint("ARP RESPONSE\n");

            // check for problems
            if (ok == false) {
                DebugPrint("ARP READ ERROR\n");
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }

            bool merged  = false;
            bool updated = false;
            ArpEntry target = arpTable.Lookup(senderIP);
            if (target != null && target.Dynamic == true) {
                DebugPrint("ARP UPDATE\n");
                // we have it already - just update the details...
                target.MacAddress = senderMAC;
                target.EntryAge   = arpTable.Age;
                merged            = true;
                updated           = true;
            }

            bool forSelf = ipModule.HostConfiguration.IsLocalAddress(targetIP);
            if (forSelf == false) {
                return NetStatus.Code.PROTOCOL_OK;
            }

            if (merged == false) {
                DebugPrint("ARP ADDITION\n");
                arpTable.AddEntry(new ArpEntry(senderIP, senderMAC, true));
                merged = true;
                UpdatePendingRequests(senderIP, senderMAC);
            }

            // now figure out the opcode
            if (opcode == ArpFormat.Type.ARP_REQUEST) {
                DebugPrint("Handling request ({0},{1}) ---> ({2},{3})\n",
                           senderIP, senderMAC, targetIP, targetMAC
                           );

                // send reply...
                // we reuse the received packet for sending a fast response
                // so we should NOT return it to the Demux's free list!!!
                // (we replace it with a new one instead)
                // we use the adapter from which the request arrived
                // (available in the context)
                Multiplexer mux = Core.Instance().GetMuxForAdapter((IAdapter!)pkt.AdapterContext);
                if (mux == null) {
                    // some internal bug, for now just panic
                    Core.Panic("At ArpModule.PacketReceive: " +
                               "context isn't Multiplexer!\n");
                    assert(false);
                }

                int dataLength = EthernetFormat.Size + ArpFormat.Size;
                if (dataLength < pkt.Length)
                    dataLength = pkt.Length;

                byte[]! data   = new byte[dataLength];
                Array.Copy(pkt.GetRawData(), 0, data, 0, pkt.Length);

                ArpFormat.CreateArpReply(ref data, targetIP,
                                         mux.Adapter.HardwareAddress);
                mux.SendDirect(new NetPacket(data));
            }
            else {
                // otherwise we are done
                DebugPrint(
                    "Handling reply ({2},{3}) <--- ({0},{1})\n",
                    senderIP, senderMAC, targetIP, targetMAC
                    );
            }

            if (merged && !updated) {
                DebugPrint(arpTable.ToString());
            }

            return res;
        }

        // sends an arp request only.
        // the given packet is already prepared.
        public NetStatus OnProtocolSend(NetPacket! pkt)
        {
            DebugPrint("ARPModule.OnProtocolSend\n");
            ((Multiplexer!)pkt.Mux).SendDirect(pkt);
            return NetStatus.Code.PROTOCOL_OK;
        }

        public void ArpRequest(IPv4               sourceIP,
                               IPv4               targetIP,
                               Multiplexer!       targetMux,
                               ArpRequestCallback callback,
                               object             cookie,
                               TimeSpan           timeout)
        {
            //
            //XXXX Check pending request does not already exist!
            //
            EthernetAddress localMac  = targetMux.Adapter.HardwareAddress;

            AddPendingRequest(targetIP, callback, cookie, timeout);

            // initiate an arp request...
            DebugPrint("Initiating request " +
                       "({0},{1}) --> ({2},{3})\n",
                       sourceIP, localMac, targetIP, EthernetAddress.Zero);

            byte[] data = new byte[ArpFormat.Size + EthernetFormat.Size];
            int pos     = EthernetFormat.Write(data, 0, localMac,
                                               EthernetAddress.Broadcast,
                                               EthernetFormat.PROTOCOL_ARP);

            ArpFormat.Write(data, pos, localMac, sourceIP,
                            ArpFormat.Type.ARP_REQUEST, EthernetAddress.Zero,
                            targetIP);

            NetPacket pkt = new NetPacket(data);
            pkt.Mux = targetMux;
            OnProtocolSend(pkt);
        }

        public bool Lookup(IPv4 targetIP, out EthernetAddress macAddress)
        {
            return arpTable.Lookup(targetIP, out macAddress);
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

        private void AddPendingRequest(IPv4               address,
                                       ArpRequestCallback callback,
                                       object             cookie,
                                       TimeSpan           timeout)
        {
            DateTime expiry = DateTime.UtcNow + timeout;
            pendingRequests.Add(
                new PendingRequest(address, callback, cookie, expiry)
                );

            if (pendingRequests.Count == 1) {
                DateTime nextPoll = DateTime.UtcNow + PollPeriod;
                Core.Instance().TheDispatcher.AddCallback(
                    new Dispatcher.Callback(OnRequestTimeout),
                    new TimeoutArgument(nextPoll),
                    (ulong)nextPoll.Ticks
                    );
            }
        }

        private void UpdatePendingRequests(IPv4            ipAddress,
                                           EthernetAddress macAddress)
        {
            int i = 0;
            while (i != pendingRequests.Count) {
                PendingRequest request = (PendingRequest!) pendingRequests[i];
                if (request.address == ipAddress) {
                    request.callback(ipAddress, macAddress, request.cookie);
                    pendingRequests.RemoveAt(i);
                    continue;
                }
                i++;
            }
        }

        private NetStatus OnRequestTimeout(Dispatcher.CallbackArgs args)
        {
            DateTime now = ((TimeoutArgument!) args).now;

            int i = 0;
            while (i != pendingRequests.Count) {
                PendingRequest request = (PendingRequest!) pendingRequests[i];
                if (request.expiry < now) {
                    DebugPrint("Expiring request");

                    request.callback(request.address,
                                     EthernetAddress.Zero,
                                     request.cookie);
                    pendingRequests.RemoveAt(i);
                    continue;
                }
                i++;
            }

            if (pendingRequests.Count > 0) {
                DateTime nextPoll = now + PollPeriod;
                Core.Instance().TheDispatcher.AddCallback(
                    new Dispatcher.Callback(OnRequestTimeout),
                    new TimeoutArgument(nextPoll),
                    (ulong)nextPoll.Ticks
                    );
            }
            return NetStatus.Code.RT_OK;
        }

        // ctor
        public ArpModule()
        {
        }
    }

    // an arp entry (we only deal with IPv4)
    public class ArpEntry
    {
        private IPv4            ipAddress;
        private EthernetAddress mac;
        private int             entryAge;
        private bool            dynamic;

        public int EntryAge
        {
            get { return entryAge; }
            set { entryAge = value; }
        }

        public EthernetAddress MacAddress
        {
            get { return mac; }
            set { mac = value; }
        }

        public IPv4 IPAddress
        {
            get { return ipAddress; }
        }

        public bool Dynamic
        {
            get { return dynamic; }
        }

        // create a new entry
        public ArpEntry(IPv4 ipAddress, EthernetAddress mac, bool dynamic)
        {
            this.ipAddress = ipAddress;
            this.mac       = mac;
            this.dynamic   = dynamic;
            this.entryAge  = ArpTable.MaxAge;
        }

        public override string! ToString()
        {
            return String.Format("{0} {1} {2} {3}",
                                 ipAddress, mac, entryAge,
                                 dynamic ? "dynamic" : "static");
        }
    }

    // define the arp table
    internal class ArpTable
    {
        Hashtable! arpEntries;   // <Key = IPv4 address, Value = ArpEntry>

        // max table size
        protected readonly int maxEntries;

        // default entry age
        protected int defaultAge;

        // get the default age
        public int Age { get { return defaultAge; } }

        // the default age
        public const int MaxAge = 50;

        // aging timeout [msec]
        public static readonly TimeSpan AgePeriod = TimeSpan.FromMinutes(5);

        // our parent
        protected ArpModule arp;

        // ctor
        public ArpTable(int size, int age, ArpModule arp)
        {
            ArpModule.DebugPrint("creating ArpTable size={0}, age={1}\n",
                                 size, age);

            arpEntries = new Hashtable(size);
            maxEntries = size;
            defaultAge = age;
            this.arp   = arp;
            base();
        }

        // add a new entry
        // return false if there is no more room
        public bool AddEntry(ArpEntry! e)
        {
            // if no more room, make one
            if (arpEntries.Count >= maxEntries) {
                PurgeLRUEntry();
            }
            e.EntryAge = this.defaultAge;
            arpEntries.Add(e.IPAddress, e);
            ArpModule.DebugPrint("Added entry {0}\n", e);
            return true;
        }

        private void RemoveEntry(ArpEntry! e)
        {
            arpEntries.Remove(e.IPAddress);
            ArpModule.DebugPrint("Removed entry for {0}\n", e);
        }

        public void RemoveEntry(IPv4 targetIP)
        {
            arpEntries.Remove(targetIP);
            ArpModule.DebugPrint("Removed entry for {0}\n", targetIP);
        }

        // makes a room for a new entry, get rid of
        // the least recently used entry (LRU)
        public void PurgeLRUEntry()
        {
            if (arpEntries.Count == 0)
                return;

            // can use a LRU list to avoid O(n)
            // but this is a kind of a small table...
            IDictionaryEnumerator dicEnum = arpEntries.GetEnumerator();
            dicEnum.MoveNext();  // get the first entry

            ArpEntry lruElement = (ArpEntry!)dicEnum.Value;

            while (dicEnum.MoveNext()) {
                ArpEntry current = (ArpEntry)dicEnum.Value;
                if (current.EntryAge < lruElement.EntryAge) {
                    lruElement = current;
                }
            }
            RemoveEntry(lruElement);
        }

        // age the dynamic table entries, if age drops to 0 purge entry
        internal bool AgeTable()
        {
            int startCount = arpEntries.Count;

            // Can't hold iterator and add or remove items so use
            // list to hold items to be deleted.
            ArrayList purgeItems = new ArrayList();

            foreach (ArpEntry! e in arpEntries.Values) {
                if (e.Dynamic == true && --e.EntryAge == 0) {
                    purgeItems.Add(e);
                }
            }

            foreach (ArpEntry! e in purgeItems) {
                RemoveEntry(e);
            }

            return startCount < arpEntries.Count;
        }

        public ArpEntry Lookup(IPv4 destination)
        {
            return arpEntries[destination] as ArpEntry;
        }

        // an upper layer interface to get the mac
        // to a target IP. The upper protocol must
        // provide the Mux for the target IP.
        // if we have it then we return true + macAddress
        // and refresh the age to create a LRU list
        public bool Lookup(IPv4 targetIP, out EthernetAddress macAddress)
        {
            ArpEntry e = arpEntries[targetIP] as ArpEntry;
            if (e != null) {
                e.EntryAge = Age;
                macAddress = e.MacAddress;
                return true;
            }
            macAddress = EthernetAddress.Zero;
            return false;
        }

        public override string! ToString()
        {
            StringBuilder stringBuilder = new StringBuilder();
            stringBuilder.Append("Internet Address      Physical Address    Type             \n");
            stringBuilder.Append("-----------------------------------------------------------\n");

            string [] types = { "static", "dynamic" };
            foreach (ArpEntry! e in arpEntries.Values) {
                stringBuilder.Append(e.IPAddress + "       " + e.MacAddress +
                                     "   " + types[ e.Dynamic ? 1 : 0] +
                                     " [Age=" + e.EntryAge + "]\n");
            }
            return stringBuilder.ToString();
        }
    }
}
