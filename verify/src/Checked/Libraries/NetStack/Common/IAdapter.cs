// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

using System;
using System.Threading;
using System.Collections;

using Drivers.Net;

namespace NetStack.Common
{
    // An Adapter interface, should exist in any environment
    // can be implemented by a driver, simulator or whatever.
    public interface IAdapter
    {
        string          DriverName      { get; }
        string          DriverVersion   { get; }
        EthernetAddress HardwareAddress { get; }
        uint            LinkSpeed       { get; }

        WaitHandle GetReadHandle();
        WaitHandle GetWriteHandle();

        // get the received packets from the adapter
        void GetReceivedPackets(Queue outQueue);

        // called when received packet has been process and can
        // be returned to the device.
        void PopulateRxRing(NetPacket packet);

        // get the number of transmitted packets just completed transmission
        uint GetTransmittedPackets();

        // populate the adapter's transmit ring with new NetPackets
        void PopulateTxRing(NetPacket[] txPackets, uint txPacketCount);

        // get the free space at the txRing
        int TxSlotsFree { get; }
    }
} // namespace Drivers.Net
