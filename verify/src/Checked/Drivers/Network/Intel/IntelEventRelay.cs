///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:  Right now this interface waits for acks from the receiver.
//         This adds an unnecessary context switch.  At some future point
//         we may be able to have something more akin to a one-way single
//         buffer-slot notification system, but for now we ack.

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
//using Microsoft.Singularity.Extending;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Io.Net;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.V1.Services;

using System;
using System.Threading;

namespace Microsoft.Singularity.Drivers.Network.Intel
{
    internal class IntelEventRelay
    {
        TRef/*<NicDeviceEventContract.Exp>*/ channel;
        bool channelClosed;

        internal IntelEventRelay(
                                 NicDeviceEventContract/*.Exp*/ ep)
        {
            channel       = new TRef(ep);
            channelClosed = false;
        }

        internal void ForwardEvent(NicEventType theEvent)
        {
            //            DebugStub.Print("EventRelay:ForwardEvent\n");
            if (channelClosed) {
                DebugStub.Print("unexpectedly closed\n");
                return;
            }

            NicDeviceEventContract/*.Exp*/ exp = (NicDeviceEventContract)channel.Acquire();
            try {
                exp.NicDeviceEvent(theEvent);
            }
            finally {
                channel.Release(exp);
            }
        }
    }
}
