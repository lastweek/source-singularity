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
using System.Collections.Specialized;

#if !SINGULARITY
using System.Net;
#endif

using System.Net.IP;
using Drivers.Net;

namespace NetStack.Runtime
{
    ///
    // This interface represents a networking protocol.
    // It should be implemented by protocol implementations.
    // Notice: Dynamic loadable protocols should implement a
    // default constructor.
    // 
    public interface IProtocol : INetModule
    {
        ///
        // A protocol's handler for PDU reception,
        // @param pkt - the arrived packet argument, the internal packet is
        // stripped from all lower layer headers.
        //
        // @return NetStatus - the status of this invocation
        //
        // NOTICE: this protocol must set the internal: NetPacket.ActivePos for
        // next level protocol.
        // 
        NetStatus OnProtocolReceive(NetPacket! pkt);

        // A specific Protocol's send routine
        // @param pkt - a packet to send
        // @return NetStatus - the status of this invocation
        NetStatus OnProtocolSend(NetPacket! pkt);

        // create a protocol specific session
        Session CreateSession();

        // set protocol specific data
        // @return NetStatus - the status of this invocation
        NetStatus SetProtocolSpecific(ushort opcode, byte[]! data);

        // get protocol specific data
        // @return NetStatus - the status of this invocation
        NetStatus GetProtocolSpecific(ushort opcode, out byte[] data);

        // get the protocol ID (Protocols.IPFormat.Protocol or EthernetFormat.Proto)
        ushort GetProtocolID();
    }

    public interface IFlowAware
    {
        // find this protocol's session for a given packet
        Session[]! GetSessions(NetPacket! packet);
    }
}
