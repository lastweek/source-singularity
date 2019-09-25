////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   SingleAddrSpaceDelivery.cs
//
//  Note:   Standard single address space implementation of channel delivery
//          mechanism.
//

using System;
using System.Threading;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;
using Microsoft.Singularity.V1.Threads;
using Microsoft.Singularity.V1.Security;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.V1.Types;
using Allocation = Microsoft.Singularity.Memory.SharedHeap.Allocation;
using SharedHeap = Microsoft.Singularity.Memory.SharedHeap;
using DelegationState = Microsoft.Singularity.Channels.EndpointCore.DelegationState;

namespace Microsoft.Singularity.Channels
{

    [CLSCompliant(false)]
    public unsafe sealed class SingleAddrSpaceDelivery: DeliveryImpl
    {
        public const string ImplName = "SingleAddrSpaceChannels";

        private Allocation * /* EndpointCore */ peerEp;

        internal SingleAddrSpaceDelivery(
            Allocation* /*EndpointCore* opt(ExHeap)!*/ endpoint): base(endpoint)
        {
        }

        internal override void Initialize(DeliveryImpl peerDi)
        {
            peerEp = SharedHeap.CurrentProcessSharedHeap.Share(peerDi.EndpointAlloc,
                         SharedHeap.CurrentProcessSharedHeap.EndpointPeerOwnerId,
                         (UIntPtr)0,
                         Allocation.GetSize(peerDi.EndpointAlloc));

            this.endpoint->SetCachedPeer(peerEp);
            this.endpoint->SetPeerStateValid(true);
        }


        internal override void Connect(DeliveryImpl expDi,
                                       Allocation* /*EndpointCore* opt(ExHeap)!*/ securityEp)
        {
            base.Connect(expDi, securityEp);

            this.Initialize(expDi);
            expDi.Initialize(this);
        }

        public override void Close() {
            this.Closed = true;
            // clear the collectionEvent.
            // Needed in case we are called from the cleanup thread.
            this.endpoint->CollectionEvent = new AutoResetEventHandle();
        }


        /// <summary>
        /// Explicitly frees this end of the channel. If other end is also
        /// freed, the channel is deallocated, meaning we have to deallocate
        /// the kernel handles for the auto reset events.
        /// Since both threads on the channel could try to do this simultaneously,
        /// we use the ref counting on the underlying endpoints to let the last
        /// free operation (the one pulling the ref count to 0) to free the associated
        /// event.
        /// </summary>
        internal static bool Free(SingleAddrSpaceDelivery dm)
        {

            Tracing.Log(Tracing.Debug,
                        "Freeing endpoint {0:x8} of deliveryImpl type:" + ImplName,
                        (UIntPtr)dm.endpointAlloc);

            bool isExp = (dm.endpoint->ChannelId > 0);
            bool peerFreed = false;
            bool meFreed = false;

            if (dm.Peer() != null) {
                // release our ref count on the peer
                peerFreed = TryFreeResources(dm.Peer(),
                    SharedHeap.CurrentProcessSharedHeap.EndpointPeerOwnerId);
            }

            // release our endpoint
            meFreed = TryFreeResources(dm.endpointAlloc,
                          SharedHeap.CurrentProcessSharedHeap.EndpointOwnerId);

            // our definition of freeing the channel is if we freed the exp
            // side
            return ((isExp && meFreed) || (!isExp && peerFreed));
        }


        /// <summary>
        /// The peer thread might try this too, so we use the ref count of the
        /// underlying memory to allow only the last freeer to also free the
        /// associated auto-reset event handle.  Make sure to grab the handle
        /// before freeing the endpoint.
        /// </summary>
        unsafe private static bool TryFreeResources(
            Allocation* /*EndpointCore*/ endpoint,
            SharedHeap.AllocationOwnerId ownerId)
        {
            EndpointCore* epData =
                (EndpointCore*)Allocation.GetDataUnchecked(endpoint);

            AutoResetEventHandle areHandle = epData->GetAreHandle();
            DeliveryHandle dh = epData->dImpHandle;

            int channelId = epData->ChannelId;

            bool lastRefGone = SharedHeap.KernelSharedHeap.Free(endpoint,
                                                                ownerId);

            if (lastRefGone) {
                if (dh != DeliveryHandle.Zero) {
                    DeliveryHandle.Dispose(dh);
                }
                if (areHandle.id != UIntPtr.Zero) {
                    Process.kernelProcess.ReleaseHandle(areHandle.id);
                }
            }

            return lastRefGone;
        }

        internal override Allocation* MoveEndpoint(SharedHeap fromHeap,
                                                   SharedHeap toHeap,
                                                   Process newOwner)
        {
            DebugStub.Assert(fromHeap == toHeap);

            // Careful about the order.
            // Since we don't know if this is a release (current process owns it)
            // or an acquire (current process does not necessarily own it), we
            // have to bypass the owner check here.
            int processId = newOwner.ProcessId;
            this.ProcessId = processId;
            this.OwnerPrincipalHandle = new PrincipalHandle(newOwner.Principal.Val);
            // Don't check for delegation here since this is for kernel calls on
            // moving endpoints to SIPs.  Delegation should not be involved.
            // The following should not be necessary, but just in case:
            this.OwnerDelegationState = DelegationState.None;

            Allocation.SetOwnerProcessId(this.endpointAlloc, processId);
            Allocation.SetOwnerProcessId(this.peerEp, processId);

            Monitoring.Log(Monitoring.Provider.EndpointCore,
                           (ushort)EndpointCoreEvent.TransferToProcess, 0,
                           (uint)ChannelId, (uint)processId, 0, 0, 0);
            return this.endpointAlloc;
        }

        /// <summary>
        /// Notify the peer that a message is ready.
        /// </summary>
        internal override void NotifyPeer()
        {
            PeerImpl().Notify();

#if CHANNEL_COUNT
            //Interlocked.Increment(ref messageCount);
            PerfCounters.IncrementMsgsSent();
#endif
        }

        [NoHeapAllocation]
        public override Allocation* Peer()
        {
            return this.peerEp;
        }

        [NoHeapAllocation]
        private DeliveryImpl PeerImpl() {
            return EndpointCore.AllocationEndpointDeliveryImpl(Peer());
        }

        /// <summary>
        /// Close peer endpoint.
        /// </summary>
        internal override bool ClosePeer()
        {
            PeerImpl().Close();
            return true;
        }

        /// <summary>
        /// Is peer endpoint closed.
        /// </summary>
        internal override bool PeerClosed()
        {
            return PeerImpl().Closed;
        }

        internal override int PeerProcessId {
            [NoHeapAllocation]
            get {
                return PeerImpl().ProcessId;
            }
        }

        internal override int PeerReceiveCount {
            [NoHeapAllocation]
            get {
                return PeerImpl().ReceiveCount;
            }
        }

        internal override PrincipalHandle PeerPrincipalHandle {
            [NoHeapAllocation]
            get {
                return PeerImpl().OwnerPrincipalHandle;
            }
            set {
                PeerImpl().OwnerPrincipalHandle = value;
            }
        }

        internal override bool IsMechanismInitialized()
        {
            // is initialized at kernel start time
            return true;
        }

        //new versions for deep pointers
        internal override void BeginUpdate(byte* basep, byte* source, int* tagAddress, int msgSize)
        {
            return;
        }


        unsafe internal override void MarshallPointer(byte* basep, byte** target, SystemType type, byte* targetParent, int offset)
        {
            return;
        }

        internal override string GetImplName()
        {
            return ImplName;
        }
    }
}
