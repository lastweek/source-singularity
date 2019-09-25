////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI Shim
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ChannelService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;

using Microsoft.Singularity;
using Microsoft.Singularity.V1.Security;
using Microsoft.Singularity.V1.Types;
using Microsoft.Singularity.V1.Threads;

namespace Microsoft.Singularity.V1.Services
{
    using Allocation = SharedHeapService.Allocation;

    [CLSCompliant(false)]
    unsafe public struct EndpointCore
    {
        ////////////////////////////////////////////////////////////////////
        // Fields
        ////////////////////////////////////////////////////////////////////
        //
        // NOTE: The fields specified here must match those in:
        //         Kernel/Singularity/Channels/EndpointCore.cs
        //         Kernel/Singularity/V1/Services/ChannelServices.cs
        //         Libraries/Singuarity.V1/Services/ChannelServices.cs

        /// <summary>
        /// Handle to the actual message delivery mechanism
        /// </summary>
        private DeliveryHandle deliveryHandle;

        /// <summary>
        /// Event handle in case this endpoint is part of a collection
        /// </summary>
        private AutoResetEventHandle collectionEvent;

        //
        // These "cached" fields are directly accessable by user programs,
        // but are not trusted by the kernel (as they could be modified by untrusted
        // code).  The kernel relies on the trusted shadow copies held in the
        // deliveryImpl object, but updates these fields to reflect any changes to user
        // apps.
        //

        /// <summary>
        /// Event on which sends are signaled to this endpoint.
        /// The handle is owned by the kernel, since the endpoint can move.
        /// The kernel deallocates the handle when the channel is deallocated.
        /// NOTE: stays valid until the entire channel gets collected.
        /// </summary>
        private AutoResetEventHandle cachedMessageEvent;

        /// <summary>
        /// Closed flag
        /// </summary>
        private bool cachedClosed;

        /// <summary>
        /// Contains the process id of the process currently owning this end of the
        /// channel.
        /// </summary>
        private int cachedOwnerProcessId;

        /// <summary>
        /// Contains the channelId (positive on the EXP endpoint, negative on the imp endpoint)
        /// </summary>
        private int cachedChannelId;

        /// <summary>
        /// Whether to marshall or not
        /// </summary>
        private bool cachedMarshall;

        /// <summary>
        /// Points to the peer endpoint
        /// </summary>
        private Allocation* /*EndpointCore* opt(ExHeap)*/ cachedPeer;

        /// <summary>
        /// If true then the peer state can be queried directly from cachedPeer
        /// </summary>
        private bool peerStateValid;

        ////////////////////////////////////////////////////////////////////
        // Methods
        ////////////////////////////////////////////////////////////////////

        /// <summary>
        /// Used to allocate a channel endpoint. The size must be correctly computed by
        /// the trusted caller (currently trusted code NewChannel)
        /// </summary>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern Allocation* //EndpointCore* opt(ExHeap)!  
        Allocate(uint size, SystemType st);

        /// <summary>
        /// Closes this end of the channel and frees associated resources, EXCEPT the block
        /// of memory for this endpoint. It must be released by the caller. Sing# does this
        /// for the programmer.
        /// Returns true for success, false for failure.
        /// </summary>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Dispose(ref EndpointCore endpoint);

        /// <summary>
        /// Deallocates this end of the channel. If other end is also
        /// deallocated, the entire channel is deallocated.
        /// </summary>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Free(Allocation* /* EndpointCore* opt(ExHeap) */ endpoint);

        /// <summary>
        /// Performs the initialization of the core part of each endpoint and cross links
        /// them to form a channel.
        /// </summary>
        public static void Connect(
            Allocation* /*EndpointCore* opt(ExHeap)!*/ imp,
            Allocation* /*EndpointCore* opt(ExHeap)!*/ exp)
        {
            Connect(imp, exp, null);
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Connect(
            Allocation* /*EndpointCore* opt(ExHeap)!*/ imp,
            Allocation* /*EndpointCore* opt(ExHeap)!*/ exp,
            Allocation* /*EndpointCore* opt(ExHeap) */ ep);

        /// <summary>
        /// Indicates if this endpoint is closed
        /// </summary>
        [NoHeapAllocation]
        public static bool Closed(ref EndpointCore ep)
        {
            return ep.cachedClosed;
        }

        [NoHeapAllocation]
        public static bool PeerClosed(ref EndpointCore ep)
        {
            if (ep.cachedPeer != null) {
                EndpointCore * peer = (EndpointCore*)SharedHeapService.GetData(ep.cachedPeer);
                return peer->cachedClosed;
            } else {
                return PeerClosedABI(ref ep);
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool PeerClosedABI(ref EndpointCore ep);

        /// <summary>
        /// Set this end to closed
        /// </summary>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Close(ref EndpointCore ep);

        /// <summary>
        /// The endpoint to which this endpoint is connected. (non ABI call version)
        /// </summary>
        [NoHeapAllocation]
        public static Allocation* /*EndpointCore* opt(ExHeap) */ GetPeer(ref EndpointCore ep,
                                                                         out bool marshall)
        {
            if (ep.cachedPeer != null) {
                marshall = ep.cachedMarshall;
                return ep.cachedPeer;
            } else {
                return GetPeerABI(ref ep, out marshall);
            }
        }

        /// <summary>
        /// The endpoint to which this endpoint is connected. (ABI version if cached peer is
        /// not valid)
        /// </summary>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern Allocation* GetPeerABI(ref EndpointCore ep,
                                                    out bool marshall);

        /// <summary>
        /// The event to wait for messages on this endpoint. Used by Select.
        /// </summary>
        [NoHeapAllocation]
        public static SyncHandle GetWaitHandle(ref EndpointCore ep)
        {
            return ep.cachedMessageEvent;
        }

        /// <summary>
        /// Notify the owner of this endpoint that a message is ready.
        /// Notifies the set owner if this endpoint is part of a set.
        /// </summary>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void NotifyPeer(ref EndpointCore ep);


        /// <summary>
        /// Wait for a message to arrive on this endpoint.
        /// </summary>
        [NoHeapAllocation]
        public static void Wait(ref EndpointCore ep) {
            SyncHandle.WaitOne(ep.cachedMessageEvent);
        }

        /// <summary>
        /// Transfer the given Allocation block to the target endpoint
        /// </summary>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void TransferBlockOwnership(Allocation* ptr, ref EndpointCore target);

        /// <summary>
        /// Transfer any contents that needs to be adjusted from the transferee to the target
        /// endpoint.
        /// </summary>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void TransferContentOwnership(
           ref EndpointCore transferee,
           ref EndpointCore target);

        [NoHeapAllocation]
        public static int GetOwnerProcessID(ref EndpointCore ep)
        {
            return ep.cachedOwnerProcessId;
        }

        [NoHeapAllocation]
        public static int GetChannelID(ref EndpointCore ep)
        {
            return ep.cachedChannelId;
        }

        [NoHeapAllocation]
        public static int GetPeerProcessID(ref EndpointCore ep)
        {
            if (ep.peerStateValid) {
                EndpointCore * peer = (EndpointCore*)SharedHeapService.GetData(ep.cachedPeer);
                return peer->cachedOwnerProcessId;
            } else {
                return GetPeerProcessIDABI(ref ep);
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetPeerProcessIDABI(ref EndpointCore ep);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void AcceptDelegation(Allocation* /*EndpointCore* opt(ExHeap)!*/ imp,
                                                   Allocation* /*EndpointCore* opt(ExHeap)!*/ exp,
                                                   Allocation* /*EndpointCore* opt(ExHeap)!*/ ep);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void EnableDelegation(ref EndpointCore ep, bool allowMediation);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern PrincipalHandle GetOwnerPrincipalHandle(ref EndpointCore ep);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern PrincipalHandle GetPeerPrincipalHandle(ref EndpointCore ep);

        /// <summary>
        /// Instruct the selectable object to signal events on the given AutoResetEvent
        /// rather than its normal event in order to aggregate signalling into a set.
        /// A selectable object need only support being part of a single collection at
        /// any point in time.
        /// </summary>
        public static void LinkIntoCollection(ref EndpointCore ep,
                                              AutoResetEventHandle ev) {
            ep.collectionEvent = ev;
        }

        /// <summary>
        /// Instruct the selectable object to stop signalling events on the given
        /// AutoResetEvent.
        /// </summary>
        public static void UnlinkFromCollection(ref EndpointCore ep,
                                                AutoResetEventHandle ev) {
            ep.collectionEvent = new AutoResetEventHandle();
        }

        /// <summary>
        /// Called when sending a message across domains. Instructs the kernel
        /// to prepare an update record to push into the peer when the peer
        /// is running.
        ///
        /// This call starts a sequence of MarshallPointer calls that will
        /// end with a call to NotifyPeer.
        /// </summary>

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        unsafe public static extern void MarshallMessage(ref EndpointCore ep,
                                                         byte* basep,
                                                         byte* source,
                                                         int* tagAddress,
                                                         int size);


        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        unsafe public static extern void MarshallPointer(ref EndpointCore ep, byte* basep, byte** target, SystemType type, byte* parent, int offset);
    }
}
