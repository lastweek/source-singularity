///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: NicManager.sg
//
//  Note:
//
//  When a network device comes up, it registers with the
//  NicManager, who places it in the namespace under
//  /dev/nicX and advertises its existence with the netstack
//  runtime core.  The netstack runtime core will be responsible
//  for notifying the NicManager when the device has gone away.
//
//  This is a lot of jiggery-pokery just so users can see the device names
//  under /dev and the names are sequential.
//

//#define DEBUG_NIC

using System;
using System.Collections;
using System.Diagnostics;
using System.Threading;

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Io.Net;
using Microsoft.Singularity.Directory;

using Microsoft.Singularity.NetStack;
using Drivers.Net;
//using Microsoft.Singularity.NetStack2.NetDrivers;

namespace Microsoft.Singularity.NetStack2.Channels.Nic
{
    class ExRefPacketFifo
    {
        MonitorLock thisLock = new MonitorLock();
        PacketFifo o;

        internal ExRefPacketFifo(PacketFifo o, bool dummy)
        {
            VTable.Assert(o != null);
            this.o = o;
        }

        public PacketFifo Acquire() {
            thisLock.Acquire();
            return o;
        }

        public void Release(PacketFifo v) {
            o = v;
            thisLock.Release();
        }
    }

    public class Nic : NicDeviceEventContract, IAdapter, IThreadStart
    {
        // Upper bounds computed for 10Gbps with maximum sized
        // packets to give a small number of I/O requests per
        // second and be a power of 2.
        private const int MaxTxPacketsInDevice = 128 * 1024;
        private const int MaxRxPacketsInDevice = 128 * 1024;

        private TRef/*NicDeviceContract.Imp*/     nicChannel;

        string  driverName;
        string  driverVersion;
        EthernetAddress macAddress;
        string  nicName;
        int mtu;
        int maxTxPacketsInDevice;
        int maxRxPacketsInDevice;
        int maxTxFragmentsPerPacket;
        int maxRxFragmentsPerPacket;

        private ExRefPacketFifo rxFifo;

        private ExRefPacketFifo txFifo;
        private ExRefPacketFifo txFreeFifo;
        private ExRefPacketFifo txCoalesceFifo;

        private AutoResetEvent muxEvent;

        private ulong txRequests = 0;
        private ulong txComplete = 0;
        private ulong rxTotal    = 0;

        //FilterAdapter filterAdapter;

        [Microsoft.Contracts.NotDelayed]
        public Nic(NicDeviceContract/*.Imp*/ nicImp,
                   NicDeviceProperties np,
                   string nicName)
        {
            this.nicChannel = new TRef(nicImp);
                //assume np.DriverName != null;
                //assume np.MacAddress != null;
                this.driverName    = np.DriverName;
                this.driverVersion = np.DriverName;
                this.macAddress    = np.MacAddress;
            this.nicName = nicName;
            this.mtu = np.MtuBytes;
            this.maxTxPacketsInDevice    = np.MaxTxPacketsInDevice;
            this.maxRxPacketsInDevice    = np.MaxRxPacketsInDevice;
            this.maxTxFragmentsPerPacket = np.MaxTxFragmentsPerPacket;
            this.maxRxFragmentsPerPacket = np.MaxRxFragmentsPerPacket;

            this.muxEvent = new AutoResetEvent(false);
            // The following attributes are both integers yet
            // sgc is complaining it doesn't know to use
            // Math.Min(sbyte, sbyte) or Math.Min(byte, byte).
            int rxFifoSize = Math.Min(np.MaxRxPacketsInDevice,
                                      (int)Nic.MaxRxPacketsInDevice);

            this.rxFifo =
                new ExRefPacketFifo(
                    new PacketFifo(rxFifoSize),
                    false
                    );

            // The following attributes are both integers yet
            // sgc is complaining it doesn't know to use
            // Math.Min(sbyte, sbyte) or Math.Min(byte, byte).
            int txFifoSize = Math.Min(np.MaxTxPacketsInDevice,
                                      (int)Nic.MaxTxPacketsInDevice);

            this.txFifo =
                new ExRefPacketFifo(
                    new PacketFifo(txFifoSize),
                    true
                    );

            this.txFreeFifo =
                new ExRefPacketFifo(
                    new PacketFifo(txFifoSize),
                    true
                    );

            this.txCoalesceFifo =
                new ExRefPacketFifo(
                    new PacketFifo(txFifoSize),
                    true
                    );

            TxProvision();
            RxProvision();
        }

        int MaxRxPackets { get { return this.maxRxPacketsInDevice; } }

        public void NicDeviceEvent(NicEventType eventType)
        {
            if ((eventType & NicEventType.ReceiveEvent) != 0) {
                DeMuxReceivedPackets();
            }
            else {
                if ((eventType & NicEventType.TransmitEvent) != 0) {
                    this.muxEvent.Set();
                    //DebugStub.Print("Received transmit event\n");
                }
                if ((eventType & NicEventType.LinkEvent) != 0) {
                    //DebugStub.Print("UNHANDLED link event!...acking anyway\n");
                }
            }
        }

        //
        // IAdapter interface
        //
        string  IAdapter.DriverName
        {
            get { return this.driverName; }
        }

        string IAdapter.NicName
        {
            get { return this.nicName; }
        }

        string  IAdapter.DriverVersion
        {
            get { return this.driverVersion; }
        }

        uint IAdapter.LinkSpeed { get { return 100000000; } }

        EthernetAddress IAdapter.HardwareAddress
        {
            get { return this.macAddress; }
        }

        [Conditional("DEBUG_NIC")]
        internal static void DebugPrint(string format,
                                        params object [] arguments)
        {
            DebugStub.Print("Nic {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }


        //XXX On the first exchange we receive an empty fifo from the Nic
        //We fill it here...this should be special cased in the startio
        //routine...
        private void RxExchangeInternal(NicDeviceContract/*.Imp*/ imp)
        {
            int toCount, fromCount;
            PacketFifo exFifo = this.rxFifo.Acquire();
            toCount = exFifo.Count;
            try {
                exFifo = imp.GiveRxPacketsToDevice(exFifo);
                fromCount = exFifo.Count;
            }
            finally {
                this.rxFifo.Release(exFifo);
            }
            DebugPrint("RxExchange out: {0} in: {1}\n",
                       toCount, fromCount);
        }
        private void RxExchange()
        {
            NicDeviceContract/*.Imp*/ imp = (NicDeviceContract)nicChannel.Acquire();
            try {
                RxExchangeInternal(imp);
            }
            finally {
                this.nicChannel.Release(imp);
            }
        }

        // Get the received packets from the adapter
        void DeMuxReceivedPackets()
        {
            //Grab the latest set of packets
            RxExchange();

            PacketFifo newPackets = this.rxFifo.Acquire();
            try {
                int count = newPackets.Count;
                for (int i = 0; i < count; i++) {
                    Packet packet = newPackets.Pop();

                    // If packet from device has an error
                    // recycle it right away.
                    FromDeviceFlags fromFlags = packet.FromDeviceFlags;
                    if ((fromFlags & FromDeviceFlags.ReceiveError) != 0) {
                        DebugStub.Print("Packet had error???\n");
                        newPackets.Push(packet);
                        continue;
                    }
                    Bytes data = packet.ReleaseFragment(0);
                    Ethernet.ProcessIncomingPacket(data, this);
#if  false
                    if (filterAdapter == null ||
                        filterAdapter.ProcessIncomingPacket(data)) {
                        Ethernet.ProcessIncomingPacket(data, this);
                    }
                    else {
                        //delete data;
                    }
#endif
                    //XXX Totally inefficient first try immediately replaces
                    //the lost data.
                    Bytes nxtPacket = new Bytes(new byte[this.mtu]);
                    packet.SetFragment(0, nxtPacket);
                    newPackets.Push(packet);
                }
            }
            finally {
                this.rxFifo.Release(newPackets);
            }
        }

        private void TxExchange()
        {
            int toCount = 0;
            int fromCount = 0;

            NicDeviceContract/*.Imp*/ imp = (NicDeviceContract)nicChannel.Acquire();
            try {
                PacketFifo src = this.txFifo.Acquire();
                PacketFifo free = this.txFreeFifo.Acquire();

                toCount = src.Count;
                try {
                    src = imp.GiveTxPacketsToDevice(src);

                    fromCount = src.Count;
                    free.Push(src);
                }
                finally {
                    this.txFreeFifo.Release(free);
                    this.txFifo.Release(src);
                }
            }
            catch (Exception e) {
                DebugStub.Print("TxExchange FAILED arg {0}\n", DebugStub.ArgList(e.ToString()));
                DebugStub.Break();
            }
            finally {
                nicChannel.Release(imp);
            }
            DebugPrint("TxExchange out: {0} in: {1}\n",
                       toCount, fromCount);
        }


        public void Run()
        {
            System.DebugStub.Print("Nic@" + Kernel.CurrentThread + ". ");
            while(true) {
                this.muxEvent.WaitOne();
                PacketFifo txCoalesce = this.txCoalesceFifo.Acquire();
                PacketFifo txToDevice = this.txFifo.Acquire();

                try {
                    DebugPrint("coalescing {0} packets\n", txCoalesce.Count);
                    txToDevice.Push(txCoalesce);
                }
                catch (Exception e) {
                    DebugStub.Print("Mux FAILED! arg {0}\n", DebugStub.ArgList(e.ToString()));
                    DebugStub.Break();
                }
                finally {
                    this.txCoalesceFifo.Release(txCoalesce);
                    this.txFifo.Release(txToDevice);
                    TxExchange();
                }
            }
        }

        //push a single packet onto the ring
        void IAdapter.PopulateTxRing(Bytes header, Bytes data)
        {
            try {
                PacketFifo txFree = this.txFreeFifo.Acquire();
                PacketFifo txCoalesce = this.txCoalesceFifo.Acquire();
                try {
                    DebugStub.Assert(txFree.Count > 0);
                    int cnt = 0;
                    while (txFree.Count <= 0) {
                        //try again...
                        //this happens when we're hammering the outgoing connection
                        this.txCoalesceFifo.Release(txCoalesce);
                        this.txFreeFifo.Release(txFree);
                        this.muxEvent.Set();
                        Thread.Yield();
                        txFree = this.txFreeFifo.Acquire();
                        txCoalesce = this.txCoalesceFifo.Acquire();
                        if (cnt > 100) {
                            DebugStub.Print("txFree empty???\n");
                            //DebugStub.Break();
                        }
                        cnt++;
                    }
                    Packet packet = txFree.Pop();
                    packet.SetFragment(0, header);
                    packet.SetFragment(1, data);
                    if ((txCoalesce.Count + 1) > txCoalesce.Capacity) {
                        DebugStub.Break();
                    }
                    DebugStub.Assert((txCoalesce.Count + 1) <= txCoalesce.Capacity);
                    txCoalesce.Push(packet);
                }
                catch {
                    DebugStub.Print("failure in populate tx ring\n");
                    DebugStub.Break();
                    DebugStub.Assert(false);
                }
                finally {
                    this.txCoalesceFifo.Release(txCoalesce);
                    this.txFreeFifo.Release(txFree);
                    //notify the mux that there are waiting packets
                    this.muxEvent.Set();
                }
            }
            catch (Exception e) {
                DebugStub.Print("Populate tx ring failed?? {0}\n", DebugStub.ArgList(e));
                DebugStub.Break();
            }
        }

#if false
        //push a single packet onto the ring
        void IAdapter.PopulateTxRing(Bytes header, Bytes data)
        {
            try {
                PacketFifo txFree = this.txFreeFifo.Acquire();
                PacketFifo txToDevice = this.txFifo.Acquire();
                DebugPrint("populate tx ring\n");
                try {
                    Packet packet = txFree.Pop();
                    packet.SetFragment(0, header);
                    packet.SetFragment(1, data);
                    txToDevice.Push(packet);
                }
                finally {
                    this.txFreeFifo.Release(txFree);
                    this.txFifo.Release(txToDevice);
                }
            }
            catch (Exception e) {
                DebugStub.Print("Populate tx ring failed?? {0}\n", DebugStub.ArgList(e));
                DebugStub.Break();
            }
            //When to exchange?
            //how do we best manage the tradeoff of throughput and latency?
            //to begin let's just send one at a time.
            //I think i'd rather have another thread....
            using (thisLock.Lock()) {
                TxExchange();
            }
        }
#endif
        private bool
        ConfigureEventChannel(NicDeviceContract nicImp)
        {
            nicImp.RegisterForEvents(this);
            return true;
        }

        private bool
        ConfigureChecksumProperties(NicDeviceContract/*.Imp*/ nicImp)
        {
            nicImp.SetChecksumProperties(0);
            return true;
        }

        private bool Configure()
        {
            NicDeviceContract/*.Imp*/ nicImp = (NicDeviceContract)nicChannel.Acquire();
            try {
                nicImp.ConfigureIO();
                if (ConfigureEventChannel(nicImp) == true &&
                    ConfigureChecksumProperties(nicImp) == true) {
                    return true;
                }
            }
            catch (SystemException e) {
                DebugStub.WriteLine("System exception occurred in Nic.Configure().");
                DebugStub.WriteLine(e.ToString());
                DebugStub.Break();
            }
            finally {
                nicChannel.Release(nicImp);
            }
            DebugStub.Break();
            return false;
        }

        private void RxProvisionInternal(PacketFifo toDevice)
        {
            for (int i = 0; i < toDevice.Capacity; i++) {
                toDevice.Push(
                    new Packet(
                        new Bytes(new byte[this.mtu])
                        )
                    );
            }
        }

        private void RxProvision()
        {
            PacketFifo toDevice = this.rxFifo.Acquire();
            RxProvisionInternal(toDevice);
            this.rxFifo.Release(toDevice);
        }

        //since data comes from the user, the packets are empty shells
        //with a default of two fragments; one for the header and one for
        //the packet body
        private void TxProvision()
        {
            PacketFifo txFree = this.txFreeFifo.Acquire();
            for (int i = 0; i < txFree.Capacity; i++) {
                txFree.Push(
                    new Packet(2)
                    );
            }
            this.txFreeFifo.Release(txFree);
        }

        private bool StartIO()
        {
            NicDeviceContract/*.Imp*/ imp = (NicDeviceContract)nicChannel.Acquire();
            try {
                    imp.StartIO();
                    RxExchangeInternal(imp);
                    return true;
            }
            finally {
                nicChannel.Release(imp);
           }
            //DebugStub.Break();
            //return false;
        }

        private bool StopIO()
        {
            NicDeviceContract/*.Imp*/ imp = (NicDeviceContract)nicChannel.Acquire();
            try {
                    imp.StopIO();
                    return true;
            }
            finally {
                nicChannel.Release(imp);
            }
            //return false;
        }

        //
        // Factory methods
        //
        internal static NicDeviceProperties
        GetNicProperties(NicDeviceContract/*.Imp*/ imp)
        {
            return imp.GetDeviceProperties();
        }

        public static bool
        CreateAndRegister(NicDeviceContract/*.Imp*/ imp,
                          string nicName)
        {
            Nic nic = null;
            try {
                //imp.RecvSuccess();
                DebugPrint("Nic channel transition\n");

                NicDeviceProperties np = GetNicProperties(imp);
                if (np == null) {
                    //delete imp;
                    return false;
                }

                nic = new Nic(imp, np, nicName);
                //delete np;
                if (nic.Configure() == false) {
                    return false;
                }

                DebugPrint("Nic.cs: Register adapter\n");
                HostConfiguration hostConfiguration = IP.GetHostConfiguration();
//                nic.filterAdapter= null;
#if false
                nic.filterAdapter = new FilterAdapter(nic);
                hostConfiguration.RegisterAdapter(nic.filterAdapter);
#endif

                hostConfiguration.RegisterAdapter(nic);

                nic.StartIO();

                Thread muxThread = new Thread(nic);
                muxThread.Start();


                return true;
            }
            catch {
                //delete imp;
                DebugStub.Break();
                return false;
            }
        }
    }
}
