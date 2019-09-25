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
using Allocation = Microsoft.Singularity.Memory.SharedHeap.Allocation;

namespace Microsoft.Singularity.Channels
{
    [CLSCompliant(false)]
    public struct DeliveryHandle
    {
        public readonly UIntPtr id;

        public static readonly DeliveryHandle Zero = new DeliveryHandle();

        public DeliveryHandle(UIntPtr id)
        {
            this.id = id;
        }

        public unsafe static bool Create(
            string implName,
            Allocation* /*EndpointCore* opt(ExHeap)!*/ endpoint,
            out DeliveryHandle handle)
        {
            DeliveryImpl deliveryImpl;

            switch (implName) {

                case SingleAddrSpaceDelivery.ImplName:
                    deliveryImpl = new SingleAddrSpaceDelivery(endpoint);
                    break;
#if PAGING
                    // TODO paging
#endif
                default:
                    throw new DeliveryHandleException(
                        "Unknown channel delivery implementation \"" +
                        implName +
                        "\" requested");
            }

            if (!deliveryImpl.IsMechanismInitialized()) {
                DebugStub.Print("Ack! IsMechInit returns false!\n");
                DebugStub.Break();
                handle = Zero;
                return false;
            }

            handle = new DeliveryHandle(
                Process.kernelProcess.AllocateHandle(deliveryImpl));
#if false
            unsafe {
                DebugStub.WriteLine("DeliveryHandle.Create: got handle {0,8:x}\n", __arglist((uint)handle.id));
            }
#endif
            return true;
        }

        public static void Dispose(DeliveryHandle handle)
        {
            Dispose(Process.kernelProcess, handle);
        }

        internal static void Dispose(Process process,
                                     DeliveryHandle handle)
        {
            Tracing.Log(Tracing.Debug, "DeliveryHandle.Dispose(id={0:x8})",
                        handle.id);
            //
            // Releasing the handle will allow the deliveryImpl to be garbage-
            // collected
            //
            process.ReleaseHandle(handle.id);
        }

        public static bool Free(DeliveryHandle handle)
        {
            DeliveryImpl di = GetImpl(handle);

            // This is a pretty kludgy hack, but is necessary since static
            // methods can't be called on an object.
            switch (di.GetImplName()) {

                case SingleAddrSpaceDelivery.ImplName:
                    return SingleAddrSpaceDelivery.Free((SingleAddrSpaceDelivery)di);
#if PAGING
                    // TODO paging
#endif
                default:
                    throw new DeliveryHandleException(
                        "Free of unknown channel delivery implementation \"" +
                        di.GetImplName() +
                        "\" requested");
            }
        }


        /// <summary>
        /// Returns the delivery implementation object associated with the
        /// given handle.
        /// </summary>
        [NoHeapAllocation]
        public static DeliveryImpl GetImpl(DeliveryHandle handle) {
            DeliveryImpl di = HandleTable.GetHandle(handle.id) as DeliveryImpl;

            return di;
        }

        [NoHeapAllocation]
        public static bool operator != (DeliveryHandle d1, DeliveryHandle d2)
        {
            return d1.id != d2.id;
        }

        [NoHeapAllocation]
        public static bool operator == (DeliveryHandle d1, DeliveryHandle d2)
        {
            return d1.id == d2.id;
        }
    }

    public class DeliveryHandleException: Exception
    {
        public DeliveryHandleException (string message) : base(message)
        {
        }
    }
}
