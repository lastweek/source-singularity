// ----------------------------------------------------------------------------
///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:
//
//  Note:
//

using System;
using System.Threading;
using System.Collections;

using Drivers.Net;

using Microsoft.Singularity.Channels;
using Microsoft.SingSharp;

namespace Microsoft.Singularity.NetStack2
{
    // An Adapter interface, should exist in any environment
    // can be implemented by a driver, simulator or whatever.
    public interface IAdapter
    {
        string          DriverName      { get; }
        string          DriverVersion   { get; }
        EthernetAddress HardwareAddress { get; }
        uint            LinkSpeed       { get; }
        string          NicName         { get; }

        void PopulateTxRing(Bytes header, Bytes data);
        //int  RequestMultiPacket(ref Packet[] packets, int packetsNeeded);

    }
}
