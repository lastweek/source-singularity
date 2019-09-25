////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DeliveryHandle.cs
//
//  Note:   An indirection mechanism used by EndpointCore to abstract the
//          Delivery mechanism used to notify the another endpoint of a new
//          message and potentially marshall and copy the message to another
//          Domain.
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Memory;

namespace Microsoft.Singularity.V1.Services
{
    using DeliveryHandleImp = Microsoft.Singularity.Channels.DeliveryHandle;

    [CLSCompliant(false)]
    public struct DeliveryHandle
    {
        public readonly UIntPtr id;

        [ExternalEntryPoint]
        public static unsafe void Dispose(ref DeliveryHandle handle)
        {
            fixed (DeliveryHandle* h = &handle) {
                DeliveryHandleImp* himp = (DeliveryHandleImp*) h;
                DeliveryHandleImp.Dispose(Thread.CurrentProcess, *himp);
            }
        }
    }
}
