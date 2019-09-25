///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: LoopbackAdapter.cs
//

//  #define DEBUG_LOOPBACK

using System;
using System.Collections;
using System.Diagnostics;
using System.Threading;

using Microsoft.Singularity;

using Drivers.Net;

using NetStack.Common;

namespace NetStack.NetDrivers
{
    public class LoopbackAdapter : IAdapter
    {
        public const int RingSize = 256;    // TODO: Why public?

        static int instantiations = 0;

        private EthernetAddress address;

        private AutoResetEvent writeEvent;
        private AutoResetEvent readEvent;

        private Queue rxBuffer;

        private int txDeliveryComplete;
        private int rxAvailable;

        public LoopbackAdapter()
        {
            LoopbackAdapter.instantiations++;

            //
            // Microsoft OUI 00:50:F2:xx:xx:xx
            // It doesn't really matter, but something other
            // than zero is preferable for testing purposes.
            //
            int x = 0xFFFFFF - instantiations;
            address = new EthernetAddress(0x00, 0x50, 0xF2,
                                          (byte)((x >> 16) & 0xFF),
                                          (byte)((x >>  8) & 0xFF),
                                          (byte)((x >>  0) & 0xFF));

            writeEvent = new AutoResetEvent(false);
            readEvent  = new AutoResetEvent(false);

            rxBuffer = new Queue(LoopbackAdapter.RingSize);
            txDeliveryComplete = 0;
            rxAvailable = 0;
        }

        public string DriverName
        {
            get { return "Loopback Adapter"; }
        }

        public string DriverVersion
        {
            get { return "0.1"; }
        }

        public EthernetAddress HardwareAddress
        {
            get { return address; }
        }

        public uint LinkSpeed
        {
            get { return 1000 * 1000 * 1000; }
        }

        public int TxSlotsFree
        {
            get {
                int txSlotsFree;
                lock (this) {
                    txSlotsFree = LoopbackAdapter.RingSize
                                - rxBuffer.Count
                                - txDeliveryComplete;
                    DebugStub.Assert(txSlotsFree >= 0);
                }
                return txSlotsFree;
            }
        }

        public void GetReceivedPackets(Queue! outQueue)
        {
            lock (this) {
                DebugStub.Assert(rxAvailable >= 0 &&
                                 rxAvailable <= LoopbackAdapter.RingSize);

                // Move Receive packets to 'outQueue'.
                Object packet;
                while (rxAvailable > 0 &&
                       (packet = rxBuffer.Dequeue()) != null) {
                    outQueue.Enqueue(packet);
                    txDeliveryComplete++;
                    rxAvailable--;
                }

                DebugStub.Assert(rxAvailable >= 0 &&
                                 rxAvailable <= LoopbackAdapter.RingSize);
                DebugStub.Assert(
                    txDeliveryComplete <= LoopbackAdapter.RingSize);
                DebugPrint("Loopback: GetReceivedPackets() -> {0}\n",
                           __arglist(outQueue.Count));
                DebugPrintStatus();

                readEvent.Reset();
                writeEvent.Set();
            }
        }

        [Conditional("DEBUG_LOOPBACK")]
        private void DebugPrintStatus()
        {
            DebugStub.Print("-- queued: {0} txComplete {1}\n",
                            __arglist(rxBuffer.Count,
                                      txDeliveryComplete));
        }

        [Conditional("DEBUG_LOOPBACK")]
        private static void DebugPrint(string format, __arglist)
        {
            DebugStub.Print(format, new ArgIterator(__arglist));
        }

        [Conditional("DEBUG_LOOPBACK")]
        private static void DebugPrint(string format)
        {
            DebugStub.Print(format);
        }

        public uint GetTransmittedPackets()
        {
            lock (this) {
                DebugPrint("Loopback: GetTransmittedPackets() -> {0}\n",
                           __arglist(txDeliveryComplete));
                DebugPrintStatus();

                uint count = (uint)txDeliveryComplete;
                txDeliveryComplete = 0;
                return count;
            }
        }

        public void PopulateRxRing(NetPacket! packet)
        {
            DebugPrint("Loopback: PopulateRxRing()\n");
            DebugPrintStatus();
            // Do nothing
        }

        public void PopulateTxRing(NetPacket[]! packets, uint count)
        {
            lock (this) {
                DebugPrint("Loopback: PopulateTxRing({0})\n",
                           __arglist(count));
                DebugPrintStatus();
                for (uint i = 0; i < count; i++) {
                    NetPacket! packet = (!)packets[i];
                    byte[]! txdata = (!)packet.ToContiguous();
                    rxBuffer.Enqueue(new NetPacket(txdata));
                    rxAvailable++;
                }

                DebugStub.Assert(rxBuffer.Count <= RingSize);

                writeEvent.Reset();
                if (rxBuffer.Count != 0) {
                    readEvent.Set();
                }
            }
        }

        public WaitHandle GetReadHandle()
        {
            return readEvent;
        }

        public WaitHandle GetWriteHandle()
        {
            return writeEvent;
        }
    }
}
