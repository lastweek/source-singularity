///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: ARP.sg
//
//  Note: are fun
//

//#define DEBUG_ARP

using System;
using System.Diagnostics;
using System.Collections;
using System.Text;
//using System.SchedulerTime;
using System.Threading;

using System.Net.IP;
using Drivers.Net;
using Microsoft.Singularity.NetStack.Protocols;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity;
using Microsoft.Singularity.V1.Services;
using Microsoft.SingSharp;

//using Allocation = SharedHeapService.Allocation;
using SchedulerTime = System.DateTime;

namespace Microsoft.Singularity.NetStack.Protocols{}
namespace Microsoft.Singularity.NetStack2
{

    public class ArpHeader
    {
        public ushort htype;
        public ushort pad0;
        public ushort ptype;
        public byte   hlen;
        public byte   plen;
        public ushort op;
        public ushort pad1;
        public EthernetAddress senderEthernetAddr;
        public IPv4            senderIPAddr;
        public EthernetAddress destEthernetAddr;
        public IPv4            destIPAddr;

        public static int Size = 28;
        public static ushort ARP_REQUEST = 1;
        public static ushort ARP_REPLY   = 2;

        public ArpHeader(Bytes packet, ushort index)
        {
            //since this is already known to be an arp request
            //we skip the sanity checks...

            VTable.Assert(packet.Length - index >= 96);

            // check hardware type == 0x0001 (Ethernet)
            htype = NetworkBitConverter.ToUInt16(packet, index);
            DebugStub.Assert(htype == 0x001);
            index +=2;

            // check protocol type == 0x0800 (IP)
            ptype =  NetworkBitConverter.ToUInt16(packet, index);
            DebugStub.Assert(ptype == 0x0800);
            index += 2;

            // check hardware address len is 6 bytes
            hlen = packet[index++];
            DebugStub.Assert(hlen == 6);


            // check IP address len is 4 bytes
            plen = packet[index++];
            DebugStub.Assert(plen == 4);

            op =  NetworkBitConverter.ToUInt16(packet, index);
            index += 2;

            senderEthernetAddr = EthernetAddress.ParseBytes(packet.Array, packet.Start + index);
            index += EthernetAddress.Length;

            uint addr = NetworkBitConverter.ToUInt32(packet, index);
            index += 4;
            senderIPAddr = new IPv4(addr);


            destEthernetAddr = EthernetAddress.ParseBytes(packet.Array, packet.Start + index);
            index += EthernetAddress.Length;

            addr = NetworkBitConverter.ToUInt32(packet, index);
            index += 4;
            destIPAddr = new IPv4(addr);
            //sgc complains
            pad0 = 0;
            pad1 = 0;
        }

        public static int Write(Bytes pkt,
                                EthernetAddress    srchw,
                                IPv4               srcip,
                                ushort             operation,
                                EthernetAddress    targethw,
                                IPv4               targetip)
        {
            int o = 0;

            pkt[o++] = 0x00; pkt[o++] = 0x01;  // hardware type = 0x0001
            pkt[o++] = 0x08; pkt[o++] = 0x00;  // protocol type = 0x0800
            pkt[o++] = 0x06; // hardware addr len (bytes)
            pkt[o++] = 0x04; // protocol address len (bytes)
            pkt[o++] = (byte) (operation >> 8);
            pkt[o++] = (byte) (operation & 0xff);

            srchw.CopyOut(pkt.Array, pkt.Start + o);
            o += EthernetAddress.Length;

            srcip.CopyOut(pkt.Array, pkt.Start + o);
            o += IPv4.Length;

            targethw.CopyOut(pkt.Array, pkt.Start + o);
            o += EthernetAddress.Length;

            targetip.CopyOut(pkt.Array, pkt.Start + o);
            o += IPv4.Length;

            return o;
        }
    }


    public class ARP: IThreadStart
    {
        // ARP variables
        private ArpTable arpTable = null;

        public static int ARP_REQUEST = 1;
        public static int ARP_REPLY = 2;

        //this is a soft limit
        private const int DefaultMaxPendingArpRequests = 256;
        private AutoResetEvent arpHandle;
        private Queue pendingRequestsFreelist;
        private Queue pendingRequests;
        private MonitorLock pendingRequestsLock = new MonitorLock();


        // Pending request polling period
        private static readonly TimeSpan PollPeriod = TimeSpan.FromSeconds(1);

        [Conditional("DEBUG_ARP")]
        public static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("ARP: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        private class PendingArpRequest
        {
            public IPv4            address;
            public SchedulerTime   requestExpiration;
            public AutoResetEvent  requestEvent;
            public EthernetAddress localMac;
            public bool            active;
            public IAdapter               adapter;
            public TContainerVectorQueueByte txContainer;

            public PendingArpRequest()
            {
                this.requestEvent = new AutoResetEvent(false);
                this.active = false;

                txContainer = new TContainerVectorQueueByte(
                    new VectorQueueByte()
                );
            }
        }


        private void ARPManageThread()
        {
            DebugPrint("ARP managment thread spinning up\n");
            //the pending requests list is ordered by deadline...
            //finding a requests when we rceive a reply is in the worst case O(n)...
            //Hopefully we won't have many oustanding requests, and the first request out
            //will often return first...

            //track two different timeouts here...ARP requests and ARP table aging.
            SchedulerTime  ageTableTimeout;
            SchedulerTime  now;
            SchedulerTime  nextTimer;


            ageTableTimeout = SchedulerTime.Now;
            ageTableTimeout = ageTableTimeout.AddMinutes(5);
            while(true) {
                now = SchedulerTime.Now;
                if (now > ageTableTimeout) {
                    arpTable.AgeTable();
                    ageTableTimeout = SchedulerTime.Now;
                    ageTableTimeout = ageTableTimeout.AddMinutes(5);
                }
                using (pendingRequestsLock.Lock()) {
                    nextTimer = SchedulerTime.MaxValue;
                    bool done = false;
                    while (!done) {
                        if (pendingRequests.Count == 0) {
                            done = true;
                            continue;
                        }
                        PendingArpRequest pendingArpRequest = (PendingArpRequest) pendingRequests.Peek();
                        if (pendingArpRequest == null) {
                            done = true;
                            continue;
                        }
                        if (pendingArpRequest.requestExpiration > now) {
                            nextTimer = pendingArpRequest.requestExpiration;
                            done = true;
                            continue;
                        }
                        else {
                            pendingArpRequest = (PendingArpRequest) pendingRequests.Dequeue();
                            if (pendingArpRequest.active == true) {
                                //We need error propagation here...
                                pendingArpRequest.active = false;
                                DebugStub.Assert(false);
                            }
                            pendingRequestsFreelist.Enqueue(pendingArpRequest);
                        }
                    }
                }
                if (ageTableTimeout < nextTimer) {
                    DebugPrint("setting nextTimer ageTableTimeout\n");
                    nextTimer = ageTableTimeout;
                }
                bool rc;
                rc = arpHandle.WaitOne(nextTimer);
            }
        }

        [Microsoft.Contracts.NotDelayed]
        public ARP()
        {
            DebugPrint("Initializing ARP module\n");
            arpTable = new ArpTable(this);
            pendingRequests = new Queue();
            pendingRequestsFreelist = new Queue();

            //start the array list with 256 elements to
            for(int i = 0; i < DefaultMaxPendingArpRequests; i++) {
                PendingArpRequest pendingArpRequest =
                    new PendingArpRequest();
                pendingRequestsFreelist.Enqueue(pendingArpRequest);
            }
            arpHandle = new AutoResetEvent(false);

            Thread arpThread = new Thread(this);
            DebugStub.Assert(arpThread != null);
            arpThread.Start();

        }

        public void Run()
        {
            System.DebugStub.Print("ARP@" + Kernel.CurrentThread + ". ");
            ARPManageThread();
        }

        // Original note from Yaron:
        // ARP logic: see RFC 826 http://www.faqs.org/rfcs/rfc826.html
        //

        public void ProcessIncomingPacket(Bytes packet, IAdapter adapter)
        {
            //Get the ARP packet info located after the ethernet header
            ArpHeader arpHeader = new ArpHeader(packet, 14);

            DebugPrint("ARP: ProcessIncomingPacket\n");
            //do some checks to make sure the packet is copacetic
            if (arpHeader.htype != 0x1) {
                DebugPrint("ARP: ProcessIncomingPacket got wrong hardware type? 0x{0,8:x}\n",
                           arpHeader.htype);
                //delete packet;
                return;
            }

            if (arpHeader.ptype != 0x0800) {
                DebugPrint("ARP: ProcessIncomingPacket got wrong  protocol? 0x{0,8:x}\n",
                           arpHeader.ptype);
                //delete packet;
                return;
            }
            //ethernet address should be 6 bytes
            if (arpHeader.hlen != 6) {
                DebugPrint("ARP: ProcessIncomingPacket got wrong hw length? 0x{0,8:x}\n",
                           arpHeader.hlen);
                //delete packet;
                return;
            }

            if (arpHeader.plen != 4) {
                DebugPrint("ARP: ProcessIncomingPacket got wrong protocol address length? 0x{0,8:x}\n",
                           arpHeader.plen);
                //delete packet;
                return;
            }


            DebugPrint("Incoming packet\n");

            bool merged  = false;
            bool updated = false;
            ArpEntry target = arpTable.Lookup(arpHeader.senderIPAddr);
            if (target != null && target.Dynamic == true) {
                DebugPrint("ARP UPDATE\n");
                // we have it already - just update the details...
                target.MacAddress = arpHeader.senderEthernetAddr;
                target.EntryAge   = arpTable.Age;
                merged            = true;
                updated           = true;
            }

            if (merged == false) {
                DebugPrint("ARP ADDITION\n");
                arpTable.AddEntry(new ArpEntry(arpHeader.senderIPAddr,
                                               arpHeader.senderEthernetAddr, true));
                merged = true;
                UpdatePendingRequests(arpHeader.senderIPAddr, arpHeader.senderEthernetAddr);
            }

            //Is this a local address
            bool forSelf = IP.IsLocalAddress(arpHeader.destIPAddr);
            if (forSelf == false) {
                //delete packet;
                return;
            }

            // now figure out the opcode
            if (arpHeader.op == ARP_REQUEST) {
                DebugPrint("Handling request ({0},{1}) ---> ({2},{3} \npkt dest {4} {5})\n",
                           arpHeader.senderIPAddr, arpHeader.senderEthernetAddr,
                           arpHeader.destIPAddr, adapter.HardwareAddress,
                           arpHeader.destIPAddr, arpHeader.destEthernetAddr
                           );

                int dataLength = EthernetHeader.Size + ArpHeader.Size;
                VTable.Assert(packet.Length >= dataLength);

                Bytes data = Bitter.SplitOff(ref packet, EthernetHeader.Size);

                EthernetHeader.Write(packet,
                                     adapter.HardwareAddress,
                                     arpHeader.senderEthernetAddr,
                                     EthernetHeader.PROTOCOL_ARP);

                //use arp header to format reply
                ArpHeader.Write(data, adapter.HardwareAddress,
                                arpHeader.destIPAddr, ArpHeader.ARP_REPLY,
                                arpHeader.senderEthernetAddr, arpHeader.senderIPAddr);
                adapter.PopulateTxRing(packet, data);
            }
            else {
                // otherwise we are done
                DebugPrint(
                    "Handling reply ({2},{3}) <--- ({0},{1})\n",
                    arpHeader.senderIPAddr, arpHeader.senderEthernetAddr,
                    arpHeader.destIPAddr, arpHeader.destEthernetAddr
                    );
                //delete packet;
            }

            if (merged && !updated) {
                DebugPrint(arpTable.ToString());
            }
        }

        public void ArpRequest(IPv4               sourceIP,
                               IPv4               targetIP,
                               EthernetAddress    localMac,
                               Bytes header,
                               Bytes buffer,
                               IAdapter          adapter)
        {
            //            AutoResetEvent requestComplete =
            AddPendingRequest(targetIP, TimeSpan.FromSeconds(3), localMac, header, buffer, adapter);

            // initiate an arp request...
            DebugPrint("Initiating request " +
                       "({0},{1}) --> ({2},{3})\n",
                       sourceIP, localMac, targetIP, EthernetAddress.Zero);

            //eventially we'll want to follow Orion's conservation of
            //packets philosophy
            Bytes arpHeader = new Bytes(new byte [EthernetHeader.Size]);
            Bytes arpMsg = new Bytes(new byte [ArpHeader.Size]);
            //xxx I'd like to get rid of EthernetHeader eventually...

            EthernetHeader.Write(arpHeader,
                                 localMac,
                                 EthernetAddress.Broadcast,
                                 EthernetHeader.PROTOCOL_ARP);

            ArpHeader.Write(arpMsg, localMac, sourceIP,
                            ArpHeader.ARP_REQUEST, EthernetAddress.Zero,
                            targetIP);
            adapter.PopulateTxRing(arpHeader, arpMsg);
            //            DebugPrint("ArpRequest: waiting for reply\n");
            //requestComplete.WaitOne();
            //            DebugPrint("ArpRequest: reply received!\n");
        }

        public bool Lookup(IPv4 targetIP, out EthernetAddress macAddress)
        {
            return arpTable.Lookup(targetIP, out macAddress);
        }

        private AutoResetEvent AddPendingRequest(IPv4 address,
                                                  TimeSpan timeout,
                                                  EthernetAddress    localMac,
                                                  Bytes header,
                                                  Bytes buffer,
                                                  IAdapter          adapter
                                                  )
        {

            PendingArpRequest pendingRequest = (PendingArpRequest) pendingRequestsFreelist.Dequeue();
            VTable.Assert(pendingRequest != null);
            pendingRequest.address = address;
            pendingRequest.active  = true;
            pendingRequest.localMac = localMac;
            pendingRequest.adapter = adapter;
            VectorQueueByte txBuffer = pendingRequest.txContainer.Acquire();
            txBuffer.AddTail(header);
            txBuffer.AddTail(buffer);
            pendingRequest.txContainer.Release(txBuffer);

            using (pendingRequestsLock.Lock()) {
                pendingRequests.Enqueue(pendingRequest);
            }

            SchedulerTime expiration = SchedulerTime.Now;
            expiration = expiration.Add(timeout);
            pendingRequest.requestExpiration = expiration;

            //poke the wait thread
            if (pendingRequests.Count == 1) {
                arpHandle.Set();
            }
            return pendingRequest.requestEvent;
        }

        private void UpdatePendingRequests(IPv4            ipAddress,
                                           EthernetAddress macAddress)
        {
            using (pendingRequestsLock.Lock()) {
                //Sigh...we're missing a linked list in the current Singularity C# runtime
                foreach (PendingArpRequest pendingRequest in pendingRequests) {
                    VTable.Assert(pendingRequest != null);
                    if (pendingRequest.address == ipAddress) {
                        pendingRequest.active = false;
                        DebugStub.WriteLine("found waiting arp request...sending on out");
                        VectorQueueByte txBuffer = pendingRequest.txContainer.Acquire();
                        Bytes header = txBuffer.ExtractHead();
                        Bytes buffer = txBuffer.ExtractHead();
                        VTable.Assert(header != null);
                        VTable.Assert(buffer != null);
                        pendingRequest.txContainer.Release(txBuffer);
                        //Format ethernet header
                        EthernetHeader.Write(header, pendingRequest.localMac, macAddress, EthernetHeader.PROTOCOL_IP);
                        //send it!
                        VTable.Assert(pendingRequest.adapter != null);
                        pendingRequest.adapter.PopulateTxRing(header, buffer);
                        continue;
                    }
                }
            }
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

        public override string ToString()
        {
            return String.Format("{0} {1} {2} {3}",
                                 ipAddress, mac, entryAge,
                                 dynamic ? "dynamic" : "static");
        }
    }

    // define the arp table
    internal class ArpTable
    {
        Hashtable arpEntries;   // <Key = IPv4 address, Value = ArpEntry>

        // max table size
        protected readonly int maxEntries;

        // default entry age
        protected int defaultAge;

        // get the default age
        public int Age { get { return defaultAge; } }

        // the default age
        public const int MaxAge = 50;

        public const int defaultSize = 128;

        // aging timeout [msec]
        public static readonly TimeSpan AgePeriod = TimeSpan.FromMinutes(5);

        // our parent
        protected ARP arp;

        [Conditional("DEBUG_ARP")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("ARP: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        [Conditional("DEBUG_ARP")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print("ARP: {0}",
                            DebugStub.ArgList(format));
        }

        public ArpTable(int size, int age, ARP arp)
        {
            DebugPrint("creating ArpTable size={0}, age={1}\n",
                           size, age);

            arpEntries = new Hashtable(size);
            maxEntries = size;
            defaultAge = age;
            this.arp   = arp;
        }

        public ArpTable(ARP arp)
        {
            DebugPrint("creating ArpTable size={0}, age={1}\n",
                       defaultSize, MaxAge);

            arpEntries = new Hashtable(defaultSize);
            maxEntries = defaultSize;
            defaultAge = MaxAge;
            this.arp   = arp;
        }

        // add a new entry
        // return false if there is no more room
        public bool AddEntry(ArpEntry e)
        {
            // if no more room, make one
            if (arpEntries.Count >= maxEntries) {
                PurgeLRUEntry();
            }
            e.EntryAge = this.defaultAge;
            arpEntries.Add(e.IPAddress, e);
            DebugPrint("Added entry {0}\n", e);
            return true;
        }

        private void RemoveEntry(ArpEntry e)
        {
            arpEntries.Remove(e.IPAddress);
            DebugPrint("Removed entry for {0}\n", e);
        }

        public void RemoveEntry(IPv4 targetIP)
        {
            arpEntries.Remove(targetIP);
            DebugPrint("Removed entry for {0}\n");
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

            ArpEntry lruElement = (ArpEntry)dicEnum.Value;

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

            foreach (ArpEntry e in arpEntries.Values) {
                if (e.Dynamic == true && --e.EntryAge == 0) {
                    purgeItems.Add(e);
                }
            }

            foreach (ArpEntry e in purgeItems) {
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

        public override string ToString()
        {
            StringBuilder stringBuilder = new StringBuilder();
            stringBuilder.Append("Internet Address      Physical Address    Type             \n");
            stringBuilder.Append("-----------------------------------------------------------\n");

            string [] types = { "static", "dynamic" };
            foreach (ArpEntry e in arpEntries.Values) {
                stringBuilder.Append(e.IPAddress + "       " + e.MacAddress +
                                     "   " + types[ e.Dynamic ? 1 : 0] +
                                     " [Age=" + e.EntryAge + "]\n");
            }
            return stringBuilder.ToString();
        }
    }
}

