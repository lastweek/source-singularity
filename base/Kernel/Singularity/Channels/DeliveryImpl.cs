////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DeliveryImpl.cs
//
//  Note:   Abstract super-class of all channel delivery implementations
//

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Security;

namespace Microsoft.Singularity.Channels
{
    using Microsoft.Singularity.V1.Types;
    using Microsoft.Singularity.V1.Security;
    using Microsoft.Singularity.V1.Services;
    using Microsoft.Singularity.V1.Threads;
    using Allocation = Microsoft.Singularity.Memory.SharedHeap.Allocation;
    using DelegationState = Microsoft.Singularity.Channels.EndpointCore.DelegationState;
    using System.Threading;

    [CLSCompliant(false)]
    public unsafe abstract class DeliveryImpl
    {

        ////////////////////////////////////////////////////////////////////
        // Class Fields
        //

        /// <summary>
        /// Allocation which holds the endpoint core associated with this
        /// delivery implementation
        /// </summary>
        protected Allocation* /*EndpointCore* opt(ExHeap)!*/ endpointAlloc;

        /// <summary>
        /// Endpoint core associated with this delivery implementation
        /// </summary>
        protected EndpointCore* endpoint;

        /// <summary>
        /// Handle to the owning Principal
        /// </summary>
        protected PrincipalHandle principalHandle;

        /// <summary>
        /// Delegation state to control delegation through the principal
        /// </summary>
        protected DelegationState delegationState;

        /// <summary>
        /// Contains the number of sends to this endpoint.
        /// </summary>
        protected int receiveCount;

        //
        // Shadow "trusted" shadow copies of the fields in endpointCore
        //

        /// <summary>
        /// Event on which sends are signaled to this endpoint.
        /// The handle is owned by the kernel, since the endpoint can move.
        /// The kernel deallocates the handle when the channel is deallocated.
        /// NOTE: stays valid until the entire channel gets collected.
        /// </summary>
        private AutoResetEventHandle shadowMessageEvent;

        /// <summary>
        /// Closed flag
        /// </summary>
        private bool shadowClosed;

        /// <summary>
        /// Contains the process id of the process currently owning this end of the
        /// channel.
        /// </summary>
        private int shadowProcessId;

        /// <summary>
        /// Contains the channelId (positive on the EXP endpoint, negative on the imp endpoint)
        /// </summary>
        private int shadowChannelId;

        /// <summary>
        /// Whether or not to marshall messages
        /// </summary>
        private bool shadowMarshall;

        ////////////////////////////////////////////////////////////////////
        // Class Methods
        //

        internal DeliveryImpl(Allocation* /*EndpointCore* opt(ExHeap)!*/ ep)
        {
            this.endpointAlloc = ep;
            this.endpoint = ((EndpointCore*)Allocation.GetData(ep));

            // set default values (shadow cached values in EndpointCore if necessary)
            setMessageEvent(new AutoResetEventHandle(
                                Process.kernelProcess.AllocateHandle(new AutoResetEvent(false))));
            endpoint->CollectionEvent = new AutoResetEventHandle();

            endpoint->SetCachedPeer(null);    // set as null by default

            ProcessId = Thread.CurrentProcess.ProcessId;
            ChannelId = 0;                    // zero initially, corrected in connect
            Marshall = false;                 // false by default
            Closed = true;                    // opened in connect

            principalHandle = new PrincipalHandle(Thread.CurrentProcess.Principal.Val);
            delegationState = DelegationState.None;
            receiveCount = 0;
        }

        /// <summary>
        /// Closes this end of the channel and frees associated resources,
        /// EXCEPT the block of memory for this endpoint. It must be released
        /// by the caller. Sing# does this for the programmer.
        ///
        /// This runs in the kernel to avoid a race condition with Process.Stop
        /// </summary>
        internal bool Dispose()
        {
            if (this.Closed) {
                return false;
            }

            Close(); // mark our side closed before waking up peer
            NotifyPeer();

            return true;
        }

        internal virtual void Connect(DeliveryImpl expDi,
                                      Allocation* /*EndpointCore* opt(ExHeap)!*/ securityEp)
        {
            // security principals are held in the delivery impl, not the endpoint core
            // since this allows them to be kept out of user memory in paging builds
            if (securityEp != null) {
                DeliveryImpl secImpl =
                    EndpointCore.AllocationEndpointDeliveryImpl(securityEp);
                if (secImpl != null &&
                    secImpl.OwnerDelegationState == DelegationState.Mediated)
                {
                    this.OwnerPrincipalHandle = secImpl.OwnerPrincipalHandle;
                }
            }

            int newChannelId = EndpointCore.GetNextChannelId();
            this.ChannelId = -newChannelId;
            expDi.ChannelId = newChannelId;

            this.Closed = false;
            expDi.Closed = false;

        }

        /// <summary>
        /// Set this end to closed
        /// </summary>
        public abstract void Close();

        /// <summary>
        /// Notify the owner of this endpoint that a message is ready.
        /// Notifies the set owner if this endpoint is part of a set.
        /// </summary>
        public void Notify() {
            this.receiveCount++;
            Tracing.Log(Tracing.Debug, "Endpoint Notify");

            // NB: Cache the collection event to prevent
            // a race with the receiver.
            AutoResetEventHandle cached_collEvent = endpoint->CollectionEvent;
            if (cached_collEvent.id != UIntPtr.Zero) {
                AutoResetEventHandle.Set(cached_collEvent);
            }

            AutoResetEventHandle.Set(this.AreHandle);
        }

        private static SystemType EndpointCoreSystemType =
            typeof(Microsoft.Singularity.V1.Services.EndpointCore).GetSystemType();

        /// <summary>
        /// Generic copy (either from kernel or to kernel)
        /// Determines if the thing we are moving is an endpoint and copies it accordingly.
        /// </summary>
        public static Allocation* MoveData(SharedHeap fromHeap,
                                    SharedHeap toHeap,
                                    Process newOwner,
                                    Allocation* data)
        {
            if (data == null) return data;

            if (!fromHeap.Validate(data)) {
                throw new ArgumentException("Bad argument. Not visible");
            }

            // We can only transfer either into our out of the kernel's heap
            DebugStub.Assert(fromHeap == SharedHeap.KernelSharedHeap ||
                             toHeap == SharedHeap.KernelSharedHeap);

            if (SystemType.IsSubtype(data, EndpointCoreSystemType)) {
                // we have an endpoint
                DeliveryImpl di = EndpointCore.AllocationEndpointDeliveryImpl(data);
                return di.MoveEndpoint(fromHeap, toHeap, newOwner);
            }
            else {
                // we have a NON-endpoint
                // TODO FIX this!
                return null; // MoveNonEndpoint(fromHeap, toHeap, newOwner, data);
            }
        }

        internal void AcceptDelegation(DeliveryImpl expDi, DeliveryImpl epDi)
        {
            if (epDi.OwnerDelegationState == DelegationState.Mediated) {
                OwnerPrincipalHandle = epDi.OwnerPrincipalHandle;
                PeerPrincipalHandle  = epDi.OwnerPrincipalHandle;
            }
        }

        internal void EnableDelegation(bool allowMediation)
        {
            if (allowMediation)
                OwnerDelegationState = DelegationState.ByMediation;
            else
                OwnerDelegationState = DelegationState.ByCapability;
        }

        //
        // Getters and setters for fields which are shadowed in EndpointCore
        //

        internal bool Closed
        {
            [NoHeapAllocation]
            get {
                return shadowClosed;
            }
            set {
                shadowClosed = value;
                endpoint->SetCachedClose(value);
            }
        }

        internal int ChannelId {
            [NoHeapAllocation]
            get {
                return shadowChannelId;
            }
            set {
                shadowChannelId = value;
                endpoint->SetCachedChannelId(value);
            }
        }
        internal int ProcessId {
            [NoHeapAllocation]
            get {
                return shadowProcessId;
            }
            set {
                shadowProcessId = value;
                endpoint->SetCachedProcessId(value);
            }
        }
        internal int ReceiveCount {
            [NoHeapAllocation]
            get {
                return receiveCount;
            }
        }
        internal bool Marshall {
            [NoHeapAllocation]
            get {
                return shadowMarshall;
            }
            set {
                shadowMarshall = value;
                endpoint->SetCachedMarshall(value);
            }
        }

        internal AutoResetEventHandle AreHandle {
            get {
                return shadowMessageEvent;
            }
        }

        internal SyncHandle MessageEvent {
            get {
                return shadowMessageEvent;
            }
        }
        public Allocation * /* EndpointCore */ EndpointAlloc {
            get {
                return endpointAlloc;
            }
        }

        private void setMessageEvent(AutoResetEventHandle value) {
            shadowMessageEvent = value;
            endpoint->SetCachedMessageEvent(value);
        }

        internal Allocation* Peer(out bool marshall) {
            marshall = Marshall;
            return Peer();
        }

        internal EndpointCore.DelegationState OwnerDelegationState {
            [NoHeapAllocation]
            get {
                return delegationState;
            }
            set {
                delegationState = value;
            }
        }
        internal PrincipalHandle OwnerPrincipalHandle {
            [NoHeapAllocation]
            get {
                return principalHandle;
            }
            set {
                principalHandle = value;
            }
        }

        //
        // abstract methods which must be defined by actual delivery implementations
        //

        internal abstract void Initialize(DeliveryImpl peerDi);

        /// <summary>
        /// Return the associated peer of this endpoint
        /// </summary>
        [NoHeapAllocation]
        public abstract Allocation* Peer();

        /// <summary>
        /// Move endpoint data to a new process
        /// </summary>
        internal abstract Allocation* MoveEndpoint(SharedHeap fromHeap,
                                                   SharedHeap toHeap,
                                                   Process newOwner);

        // <summary>
        // Move non endpoint data to a new process
        // </summary>
        //internal abstract Allocation* MoveNonEndpoint(SharedHeap fromHeap,
        //                                              SharedHeap toHeap,
        //                                              Process newOwner);

        /// <summary>
        /// Returns true if this delivery mechanism has been initialised and
        /// can be used for channel transport.
        /// </summary>
        internal abstract bool IsMechanismInitialized();

        /// <summary>
        /// Returns the name of the delivery implementation actually being used
        /// </summary>
        internal abstract string GetImplName();

        /// <summary>
        /// Notify the peer that a message is ready.
        /// </summary>
        internal abstract void NotifyPeer();

        /// <summary>
        /// Close peer endpoint.
        /// </summary>
        internal abstract bool ClosePeer();

        /// <summary>
        /// Is peer endpoint closed.
        /// </summary>
        internal abstract bool PeerClosed();

        internal abstract int PeerProcessId {
            [NoHeapAllocation]
            get;
        }

        internal abstract int PeerReceiveCount {
            [NoHeapAllocation]
            get;
        }

        internal abstract PrincipalHandle PeerPrincipalHandle {
            [NoHeapAllocation]
            get;
            set;
        }

        //methods used for structures that contain pointers greater than one level deep
        internal abstract void BeginUpdate(byte* basep, byte* source, int* tagAddress, int msgSize);

        unsafe internal abstract void MarshallPointer(byte* basep, byte** target, SystemType type, byte* parent, int offset);
        ///////////////////////////////////////////////////////////////////
    }
}
