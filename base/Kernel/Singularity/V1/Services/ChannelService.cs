////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI Implementation
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EndpointCore.cs
//
//  Note:
//

using System;
using System.Threading;
using System.Runtime.CompilerServices;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Security;

using Microsoft.Singularity.Memory;
using Microsoft.Singularity.V1.Security;
using Microsoft.Singularity.V1.Threads;
using Microsoft.Singularity.V1.Types;

namespace Microsoft.Singularity.V1.Services
{
    using Allocation = SharedHeapService.Allocation;
    using EndpointCoreImplementation = Microsoft.Singularity.Channels.EndpointCore;

    [CLSCompliant(false)]
    public enum ChannelServiceEvent : ushort
    {
        TransferBlockOwnership = 1,
        TransferContentOwnership = 2,
    }


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
        [ExternalEntryPoint]
        public static Allocation* //EndpointCore* opt(ExHeap)!  
        Allocate(uint size, SystemType st)
        {
            Allocation* ep = (Allocation*) SharedHeap.CurrentProcessSharedHeap.Allocate(
                size, st.id, 0, SharedHeap.CurrentProcessSharedHeap.EndpointOwnerId);
            if (ep == null) {
                throw new ApplicationException("SharedHeap.Allocate returned null");
            }
            return ep;
        }

        /// <summary>
        /// Closes this end of the channel and frees associated resources, EXCEPT the block
        /// of memory for this endpoint. It must be released by the caller. Sing# does this
        /// for the programmer.
        /// Returns true for success, false for failure.
        /// </summary>
        [ExternalEntryPoint]
        public static bool Dispose(ref EndpointCore endpoint)
        {
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return epimp->Dispose();
            }
        }

        /// <summary>
        /// Deallocates this end of the channel. If other end is also
        /// deallocated, the entire channel is deallocated.
        /// </summary>
        [ExternalEntryPoint]
        public static void Free(Allocation* /* EndpointCore* opt(ExHeap) */ endpoint)
        {
            EndpointCoreImplementation.Free((SharedHeap.Allocation*)endpoint);
        }

        /// <summary>
        /// Performs the initialization of the core part of each endpoint and cross links
        /// them to form a channel.
        /// </summary>

        [ExternalEntryPoint]
        public static void Connect(
            Allocation* /*EndpointCore* opt(ExHeap)!*/ imp,
            Allocation* /*EndpointCore* opt(ExHeap)!*/ exp,
            Allocation* /*EndpointCore* opt(ExHeap) */ ep)
        {
            EndpointCoreImplementation.Connect((SharedHeap.Allocation*)imp,
                                               (SharedHeap.Allocation*)exp,
                                               (SharedHeap.Allocation*)ep);
        }

        /// <summary>
        /// Indicates if this endpoint is closed
        /// </summary>
        [NoHeapAllocation]
        public static bool Closed(ref EndpointCore endpoint)
        {
            // kernel methods always access the shadowed copy in deliveryImpl
            // not the user accessable copy in EndpointCore
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return epimp->Closed();
            }
        }

        /// <summary>
        /// Indicates if the peer endpoint is closed
        /// </summary>
        public static bool PeerClosed(ref EndpointCore ep)
        {
            // kernel methods always access the shadowed copy in deliveryImpl
            // not the user accessable copy in EndpointCore
            return PeerClosedABI(ref ep);
        }

        /// <summary>
        /// Indicates if the peer endpoint is closed (ABI call)
        /// </summary>
        [ExternalEntryPoint]
        public static bool PeerClosedABI(ref EndpointCore endpoint) {
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return epimp->PeerClosed();
            }
        }

        /// <summary>
        /// Set this end to closed
        /// </summary>
        [ExternalEntryPoint]
        public static void Close(ref EndpointCore endpoint) {
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                epimp->Close();
            }
        }

        /// <summary>
        /// The endpoint to which this endpoint is connected.
        /// </summary>
        public static Allocation* /*EndpointCore* opt(ExHeap) */ GetPeer(ref EndpointCore ep,
                                                                         out bool marshall)
        {
            // kernel methods always access the shadowed copy in deliveryImpl
            // not the user accessable copy in EndpointCore
            return GetPeerABI(ref ep, out marshall);
        }

        [ExternalEntryPoint]
        public static Allocation* /*EndpointCore* opt(ExHeap) */ GetPeerABI(ref EndpointCore endpoint,
                                                                            out bool marshall)
        {
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return (Allocation*) epimp->Peer(out marshall);
            }
        }

        /// <summary>
        /// The event to wait for messages on this endpoint. Used by Select.
        /// </summary>
        public static SyncHandle GetWaitHandle(ref EndpointCore endpoint)
        {
            // kernel methods always access the shadowed copy in deliveryImpl
            // not the user accessable copy in EndpointCore
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return epimp->GetWaitHandle();
            }
        }

        /// <summary>
        /// Notify the owner of this endpoint that a message is ready.
        /// Notifies the set owner if this endpoint is part of a set.
        /// </summary>
        [ExternalEntryPoint]
        public static void NotifyPeer(ref EndpointCore endpoint) {
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                epimp->NotifyPeer();
            }
        }

        /// <summary>
        /// Wait for a message to arrive on this endpoint.
        /// </summary>
        public static void Wait(ref EndpointCore ep) {
            SyncHandle.WaitOne(GetWaitHandle(ref ep));
        }

        /// <summary>
        /// Transfer the given Allocation block to the target endpoint
        /// </summary>
        [ExternalEntryPoint]
        public static void TransferBlockOwnership(Allocation* ptr, ref EndpointCore target)
        {
            fixed (EndpointCore* ep = &target) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                EndpointCoreImplementation.TransferBlockOwnership((SharedHeap.Allocation*)ptr, ref *epimp);
            }
        }

        /// <summary>
        /// Transfer any contents that needs to be adjusted from the transferee to the target
        /// endpoint. Currently, this means setting the ownerProcessId of the
        /// transferee to that of the target.
        /// </summary>
        [ExternalEntryPoint]
        public static void TransferContentOwnership(
           ref EndpointCore transferee,
           ref EndpointCore target)
        {
            fixed (EndpointCore* ep1 = &transferee, ep2 = &target) {
                EndpointCoreImplementation* epimp1 = (EndpointCoreImplementation*)ep1;
                EndpointCoreImplementation* epimp2 = (EndpointCoreImplementation*)ep2;
                EndpointCoreImplementation.TransferContentOwnership(ref *epimp1, ref *epimp2);
            }
        }

        [NoHeapAllocation]
        public static int GetChannelID(ref EndpointCore endpoint)
        {
            // kernel methods always access the shadowed copy in deliveryImpl
            // not the user accessable copy in EndpointCore
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return epimp->ChannelId;
            }
        }

        [NoHeapAllocation]
        public static int GetOwnerProcessID(ref EndpointCore endpoint)
        {
            // kernel methods always access the shadowed copy in deliveryImpl
            // not the user accessable copy in EndpointCore
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return epimp->ProcessId;
            }
        }

        [NoHeapAllocation]
        public static int GetPeerProcessID(ref EndpointCore ep)
        {
            // kernel methods always access the shadowed copy in deliveryImpl
            // not the user accessable copy in EndpointCore
            return GetPeerProcessIDABI(ref ep);
        }

        [ExternalEntryPoint]
        [NoHeapAllocation]
        public static int GetPeerProcessIDABI(ref EndpointCore endpoint)
        {
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return epimp->PeerProcessId;
            }
        }

        [ExternalEntryPoint]
        public static void AcceptDelegation(Allocation* /*EndpointCore* opt(ExHeap)!*/ imp,
                                            Allocation* /*EndpointCore* opt(ExHeap)!*/ exp,
                                            Allocation* /*EndpointCore* opt(ExHeap)!*/ ep)
        {
            EndpointCoreImplementation.AcceptDelegation((SharedHeap.Allocation*)imp,
                                                        (SharedHeap.Allocation*)exp,
                                                        (SharedHeap.Allocation*)ep);
        }

        [ExternalEntryPoint]
        public static void EnableDelegation(ref EndpointCore endpoint, bool allowMediation)
        {
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                epimp->EnableDelegation(allowMediation);
            }
        }

        [ExternalEntryPoint]
        [NoHeapAllocation]
        public static PrincipalHandle GetPeerPrincipalHandle(ref EndpointCore endpoint)
        {
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return epimp->PeerPrincipalHandle;
            }
        }


        [ExternalEntryPoint]
        [NoHeapAllocation]
        public static PrincipalHandle GetOwnerPrincipalHandle(ref EndpointCore endpoint)
        {
            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                return epimp->OwnerPrincipalHandle;
            }
        }

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

        [ExternalEntryPoint]
        unsafe public static void MarshallMessage(ref EndpointCore endpoint,
                                                  byte* basep,
                                                  byte* source,
                                                  int* tagAddress,
                                                  int msgSize)
        {

            fixed (EndpointCore* ep = &endpoint) {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                epimp->BeginUpdate(basep, source, tagAddress, msgSize);
            }
        }

        [ExternalEntryPoint]
        public static void MarshallPointer(ref EndpointCore endpoint, byte* basep, byte** target, SystemType type, byte* parent, int offset)
        {
            fixed (EndpointCore* ep = &endpoint)
            {
                EndpointCoreImplementation* epimp = (EndpointCoreImplementation*)ep;
                epimp->MarshallPointer(basep, target, type, parent, offset);
            }
        }
    }
}
