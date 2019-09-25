///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: LoopbackAdapter.cs
//

using NetStack.Common;
using System;
using System.Collections;
using System.Threading;

using Drivers.Net;

using Microsoft.Contracts;

namespace NetStack.NetDrivers
{
    /// <summary>
    /// Interface that debug clients must implement to receive packets
    /// from DebugAdapter instances.  The DebugAdapter and client
    /// interact synchronously.
    /// </summary>
    public interface IDebugAdapterClient
    {
        void RegisterAdapter(DebugAdapter adapter);
        void Receive(NetPacket packet);
    }

    public class DebugAdapter : IAdapter
    {
        private const int RingSize = 64;

        private IDebugAdapterClient! client;
        private EthernetAddress      address;

        private AutoResetEvent! writeEvent;
        private AutoResetEvent! readEvent;

        private ArrayList! rxBuffer;
        private ArrayList! txBuffer;

        static int instantiations = 0;

        [NotDelayed]
        public DebugAdapter(IDebugAdapterClient! debugClient)
        {
            instantiations++;

            //
            // Microsoft OUI 00:50:f2:xx:xx:xx
            // It doesn't really matter, but something other
            // than zero is preferable for testing purposes.
            //
            int x = 0x222111 ^ instantiations;
            address = new EthernetAddress(0x00, 0x50, 0xf2,
                                          (byte)(x >> 16),
                                          (byte)(x >>  8),
                                          (byte)(x & 0xff));

            writeEvent = new AutoResetEvent(false);
            readEvent  = new AutoResetEvent(false);

            txBuffer = new ArrayList();
            rxBuffer = new ArrayList();

            this.client = debugClient;

            base();

            debugClient.RegisterAdapter(this);
        }

        public string DriverName
        {
            get { return "Debug Adapter"; }
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
            get { return 10 * 1000 * 1000; }
        }

        public int TxSlotsFree
        {
            get { return RingSize - rxBuffer.Count; }
        }

        /// <summary>
        /// Method to simulate arrival of a packet.
        /// </summary>
        public bool ReceivePacket(NetPacket packet)
        {
            Console.WriteLine("GetReceivePacket");
            if (rxBuffer.Count < RingSize) {
                rxBuffer.Add(packet);
                readEvent.Set();
                return true;
            }
            return false;
        }

        public void GetReceivedPackets(Queue! outQueue)
        {
            Console.WriteLine("GetReceivedPackets");
            for (int i = 0; i < rxBuffer.Count; i++) {
                outQueue.Enqueue(rxBuffer[i]);
            }
            rxBuffer.Clear();
            readEvent.Reset();
        }

        public uint GetTransmittedPackets()
        {
            uint count = (uint)txBuffer.Count;
            txBuffer.Clear();
            writeEvent.Reset();
            return count;
        }

        public void PopulateRxRing(uint count)
        {
            // Do nothing
        }

        public void PopulateTxRing(NetPacket[]! packets, uint packetCount)
        {
            for (uint i = 0; i < packetCount; i++) {
                NetPacket! packet = (!)packets[i];

                // Add an equivalently sized packet back to recycle list
                txBuffer.Add(new NetPacket(packet.Length));

                // Give packet to client
                client.Receive(packet);
            }
            writeEvent.Set();
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
