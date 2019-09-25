////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EndpointCore.cs
//

//  HACK: Because we currently compile this file as part of the Kernel with C#, we can't
//        make EndpointCore a rep struct, which is necessary for inheriting from it.
//        The compiler and Bartok recognize EndpointCore as special and treat it as
//        unsealed.
//        This hack can be removed, once we compile it with Sing#.
//        DON'T change the name until then!

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Diagnostics;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Security;
using Microsoft.Singularity.Memory;

namespace Microsoft.Singularity.Channels
{
    using Microsoft.Singularity.V1.Threads;
    using Microsoft.Singularity.V1.Security;
    using Microsoft.Singularity.V1.Services;
    using Microsoft.Singularity.V1.Types;
    using Allocation = Microsoft.Singularity.Memory.SharedHeap.Allocation;
    using System.Threading;
    using SharedHeap = Microsoft.Singularity.Memory.SharedHeap;

    [CLSCompliant(false)]
    public enum EndpointCoreEvent : ushort
    {
        Connect = 4,
        TransferToProcess = 5,
    }


    [CLSCompliant(false)]
    [CCtorIsRunDuringStartup]
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
        // Static Fields
        ////////////////////////////////////////////////////////////////////

        /// <summary>
        /// Number of open channels (using any delivery mechanism)
        /// </summary>
        private static int openChannelCount;     // TODO open channel count!!!

        /// <summary>
        /// Channel id generator used to create unique channel id's accross delivery
        /// mechanisms.
        /// </summary>
        private static int channelIdGenerator;


        ////////////////////////////////////////////////////////////////////
        // Types
        ////////////////////////////////////////////////////////////////////
        public enum DelegationState {None, ByCapability, ByMediation, Mediated};



        ////////////////////////////////////////////////////////////////////
        // Methods
        ////////////////////////////////////////////////////////////////////

        /// <summary>
        /// Retrieve underlying delivery mechanism for a given endpoint allocation pointer
        /// </summary>
        [NoHeapAllocation]
        internal static DeliveryImpl AllocationEndpointDeliveryImpl(
            Allocation* /*EndpointCore* opt(ExHeap)!*/ endpoint)
        {
            EndpointCore * ep = (EndpointCore *) Allocation.GetData(endpoint);
            if (ep == null) {
                return null;
            } else {
                return ep->EndpointDeliveryImpl;
            }
        }

        /// <summary>
        /// Retrieve underlying delivery mechanism for a given endpoint allocation pointer
        /// using GetDataUnchecked.
        /// </summary>
        [NoHeapAllocation]
        internal static DeliveryImpl AllocationEndpointDeliveryImplUnchecked(
            Allocation* /*EndpointCore* opt(ExHeap)!*/ endpoint)
        {
            EndpointCore * ep = (EndpointCore *) Allocation.GetDataUnchecked(endpoint);
            if (ep == null) {
                return null;
            } else {
                return ep->EndpointDeliveryImpl;
            }
        }

        /// <summary>
        /// Retrieve underlying delivery mechanism for this endpoint
        /// </summary>
        internal DeliveryImpl EndpointDeliveryImpl {
            [NoHeapAllocation]
            get {
                if (deliveryHandle != DeliveryHandle.Zero) {
                    return DeliveryHandle.GetImpl(deliveryHandle);
                } else {
                    unsafe {
                        DebugStub.WriteLine("deliveryHandle value is {0,8:x}\n", __arglist((uint) deliveryHandle.id));
                    }
                    DebugStub.Break();
                    return null;
                }
            }
        }

        /// <summary>
        /// Performs the initialization of the core part of each endpoint and cross links
        /// them to form a channel.  Uses the standard shared address space delivery
        /// mechanism.
        /// </summary>
        public static void Connect(
            Allocation* /*EndpointCore* opt(ExHeap)!*/ imp,
            Allocation* /*EndpointCore* opt(ExHeap)!*/ exp,
            Allocation* /*EndpointCore* opt(ExHeap)!*/ securityEp)
        {
            Connect(imp, exp, securityEp, SingleAddrSpaceDelivery.ImplName);
        }

        /// <summary>
        /// Performs the initialization of the core part of each endpoint and cross links
        /// them to form a channel.  Uses the given delivery mechanism.
        /// </summary>
        public static void Connect(
            Allocation* /*EndpointCore* opt(ExHeap)!*/ imp,
            Allocation* /*EndpointCore* opt(ExHeap)!*/ exp,
            Allocation* /*EndpointCore* opt(ExHeap)!*/ securityEp,
            string deliveryImplType)
        {
            if (imp == null || exp == null) {
                throw new ApplicationException("Connect called with null endpoints");
            }
            EndpointCore* impData = (EndpointCore*)Allocation.GetData(imp);
            EndpointCore* expData = (EndpointCore*)Allocation.GetData(exp);
            if (impData == null || expData == null) {
                throw new ApplicationException("SharedHeap.GetData return null");
            }

            Tracing.Log(Tracing.Debug, "connect {0:x8} and {1:x8}",
                        (UIntPtr)imp, (UIntPtr)exp);

            if (!(DeliveryHandle.Create(deliveryImplType, imp, out impData->deliveryHandle) &&
                  DeliveryHandle.Create(deliveryImplType, exp, out expData->deliveryHandle))) {
                throw new EndpointCoreException(
                    "Error trying to create EndpointCore using \"" +
                    deliveryImplType +
                    "\" delivery implementation");
            }
#if false
            DebugStub.Print("imp handle {0,8:x} exp handle {1,8:x}\n",
                            __arglist((uint)impData->deliveryHandle.id, (uint)expData->deliveryHandle.id));
#endif
            DeliveryImpl impDi = impData->EndpointDeliveryImpl;
            DeliveryImpl expDi = expData->EndpointDeliveryImpl;

            VTable.Assert(impDi != null && expDi != null);

            impDi.Connect(expDi, securityEp);

            // keep track of how many channels are open
            Interlocked.Increment(ref openChannelCount);
#if CHANNEL_COUNT
            PerfCounters.IncrementChannelsCreated();
#endif
            Monitoring.Log(Monitoring.Provider.EndpointCore,
                         (ushort)EndpointCoreEvent.Connect, 0,
                         (uint)expData->ChannelId, 0, 0, 0, 0);
        }

        /// <summary>
        /// Set this end to closed
        /// </summary>
        public void Close()
        {
            DeliveryImpl di = EndpointDeliveryImpl;
            if (di != null) {
                di.Close();
            }
        }

        [NoHeapAllocation]
        public bool Closed()
        {
            DeliveryImpl di = EndpointDeliveryImpl;
            if (di != null) {
                return di.Closed;
            } else {
                // endpoint has not yet been connected
                return true;
            }
        }

        /// <summary>
        /// Closes this end of the channel and frees associated resources, EXCEPT the block
        /// of memory for this endpoint. It must be released by the caller. Sing# does this
        /// for the programmer.
        ///
        /// This runs in the kernel to avoid a race condition with Process.Stop.
        /// </summary>
        public bool Dispose()
        {
            DeliveryImpl di = EndpointDeliveryImpl;
            if (di != null) {
                return EndpointDeliveryImpl.Dispose();
            } else {
                return true;   // endpoint was not yet connected
            }
        }

        /// <summary>
        /// Explicitly frees this end of the channel.
        ///
        /// Since both threads on the channel could try to do this simultaneously,
        /// we use the ref counting on the underlying endpoints to let the last
        /// free operation (the one pulling the ref count to 0) to free the associated
        /// event.
        /// </summary>
        public unsafe static void Free(Allocation* /*EndpointCore* opt(ExHeap)!*/ endpoint)
        {


            // Use unchecked GetData here, since this may be called from the
            // cleanup threading running in the kernel.
            EndpointCore * ep = ((EndpointCore*)Allocation.GetDataUnchecked(endpoint));
            if (ep->deliveryHandle != DeliveryHandle.Zero) {
                if (DeliveryHandle.Free(ep->deliveryHandle)) {
                    Interlocked.Decrement(ref openChannelCount);
                }
            } else {
                // was never connected, just free this endpoint
                AutoResetEventHandle areHandle = ep->cachedMessageEvent;

                SharedHeap.KernelSharedHeap.Free(endpoint,
                              SharedHeap.CurrentProcessSharedHeap.EndpointPeerOwnerId);
                if (areHandle.id != UIntPtr.Zero) {
                    Process.kernelProcess.ReleaseHandle(areHandle.id);
                }
            }
        }

        /// <summary>
        /// The event to wait for messages on this endpoint. Used by Select.
        /// </summary>
        public SyncHandle GetWaitHandle() {
            DeliveryImpl di = EndpointDeliveryImpl;
            VTable.Assert(di != null);
            return di.MessageEvent;
        }

        /// <summary>
        /// Get the AutoResetEventHandle
        /// </summary>
        public AutoResetEventHandle GetAreHandle() {
            DeliveryImpl di = EndpointDeliveryImpl;
            VTable.Assert(di != null);
            return di.AreHandle;
        }

        /// <summary>
        /// Notify the peer of this endpoint that a message is ready.
        /// Notifies the set owner if this endpoint is part of a set.
        /// </summary>
        public void NotifyPeer() {
            DeliveryImpl di = EndpointDeliveryImpl;
            VTable.Assert(di != null);
            di.NotifyPeer();
        }

        /// <summary>
        /// Used internally by the kernel to transfer an endpoint to a new owner
        ///
        /// Can be used to transfer ANY kind of shared heap data, not just endpoints.
        /// </summary>
        public static Allocation* MoveEndpoint(SharedHeap fromHeap,
                                               SharedHeap toHeap,
                                               Process newOwner,
                                               Allocation *ep)
        {
            return DeliveryImpl.MoveData(fromHeap, toHeap, newOwner, ep);
        }


        public static void AcceptDelegation(Allocation* /*EndpointCore* opt(ExHeap)!*/ imp,
                                            Allocation* /*EndpointCore* opt(ExHeap)!*/ exp,
                                            Allocation* /*EndpointCore* opt(ExHeap)!*/ ep)
        {
            DeliveryImpl impDi = AllocationEndpointDeliveryImpl(imp);
            DeliveryImpl expDi = AllocationEndpointDeliveryImpl(exp);
            DeliveryImpl epDi  = AllocationEndpointDeliveryImpl(ep);
            VTable.Assert((impDi != null && expDi != null && epDi != null));
            VTable.Assert((impDi.GetType() == expDi.GetType()) &&
                          (impDi.GetType() == epDi.GetType()));
            impDi.AcceptDelegation(expDi, epDi);
        }

        public void EnableDelegation(bool allowMediation)
        {
            EndpointDeliveryImpl.EnableDelegation(allowMediation);
        }

        public DelegationState OwnerDelegationState
        {
            [NoHeapAllocation]
            get { return EndpointDeliveryImpl.OwnerDelegationState; }
        }

        public PrincipalHandle OwnerPrincipalHandle
        {
            [NoHeapAllocation]
            get { return EndpointDeliveryImpl.OwnerPrincipalHandle; }
        }

        public PrincipalHandle PeerPrincipalHandle
        {
            [NoHeapAllocation]
            get { return EndpointDeliveryImpl.PeerPrincipalHandle; }
        }

        public int PeerReceiveCount
        {
            [NoHeapAllocation]
            get {
                DeliveryImpl di = EndpointDeliveryImpl;
                if (di != null) {
                    return di.PeerReceiveCount;
                } else {
                    // not yet connected, therefore no peer yet
                    return 0;
                }
            }
        }

        //versions of begin update and marshallpointer that handle objects with pointers
        //greater than one level deep

        internal void BeginUpdate(byte* basep, byte* source, int* tagAddress, int msgSize)
        {
            DeliveryImpl di = EndpointDeliveryImpl;
            VTable.Assert(di != null);
            //            DebugStub.Print("BeginUpdate delivery handle {0,8:x}\n", __arglist((uint)deliveryHandle.id));
            di.BeginUpdate(basep, source, tagAddress, msgSize);
        }

        public void MarshallPointer(byte* basep, byte** target, SystemType type, byte* parent, int offset)
        {
            if (target == null) return;
            DeliveryImpl di = EndpointDeliveryImpl;
            //            DebugStub.Print("Marshall Pointer delivery handle {0,8:x}\n", __arglist((uint)deliveryHandle.id));
            VTable.Assert(di != null);
            di.MarshallPointer(basep, target, type, parent, offset);
        }

        public static PrincipalHandle TransferPrincipal(PrincipalHandle oldH,
                                                        int processId,
                                                        ref DelegationState delegationState)
        {
            Process p = Process.GetProcessByID(processId);
            if (p == null)
                throw new ApplicationException("Delegate endpoint process is null");

            DelegationState newstate;
            Principal pr;
            switch (delegationState) {
                case DelegationState.ByMediation:
                    pr = PrincipalImpl.NewDelegation(
                        PrincipalImpl.MakePrincipal(oldH.val), p.Principal);
                    newstate = DelegationState.Mediated;
                    break;
                case DelegationState.ByCapability:
                    pr = PrincipalImpl.NewDelegation(
                        PrincipalImpl.MakePrincipal(oldH.val), p.Principal);
                    newstate = DelegationState.None;
                    break;
                case DelegationState.Mediated:
                    pr = p.Principal;
                    newstate = DelegationState.None;
                    break;
                case DelegationState.None:
                default:
                    pr = p.Principal;
                    newstate = DelegationState.None;
                    break;
            }

            delegationState = newstate;
            return new PrincipalHandle(pr.Val);
        }

#if SINGULARITY_KERNEL && CHANNEL_COUNT

        internal static void IncreaseBytesSentCount(long bytes)
        {
              PerfCounters.AddBytesSent(bytes);

        }

#endif // SINGULARITY_KERNEL

        /// <summary>
        /// Transfer the given Allocation block to the target endpoint
        /// </summary>
        public static void TransferBlockOwnership(Allocation* ptr, ref EndpointCore target)
        {
            Allocation.SetOwnerProcessId(ptr, target.cachedOwnerProcessId);
            // TODO MAKE THIS APROPRIATE TO BOTH SINGLE AND PAGED IMPLS
            DeliveryImpl di = target.EndpointDeliveryImpl;
            VTable.Assert(di != null);
            //Monitoring.Log(Monitoring.Provider.ChannelService,
            //               (ushort)ChannelServiceEvent.TransferBlockOwnership, 0,
            //               (uint)di.ChannelId,
            //               (uint)di.ProcessId,
            //               0, 0, 0);
#if CHANNEL_COUNT
            IncreaseBytesSentCount((long) Allocation.GetSize(ptr));
#endif
            Allocation.SetOwnerProcessId(ptr, di.ProcessId);
        }

        /// <summary>
        /// Transfer any contents that needs to be adjusted from the transferee to the target
        /// endpoint.
        /// </summary>
        // TODO: change "ref EndpointCore" to "EndpointCore"
        public static void TransferContentOwnership(
           ref EndpointCore transferee,
           ref EndpointCore target)
        {
            // TODO MAKE THIS APROPRIATE TO BOTH SINGLE AND PAGED IMPLS
            DeliveryImpl transfereeDi = transferee.EndpointDeliveryImpl;

            // XXX BUG? BUG? BUG?
            //   targetDi = transferee.EndpointDeliveryImpl
            // should be:
            //   targetDi = target.EndpointDeliveryImpl
            DeliveryImpl targetDi = transferee.EndpointDeliveryImpl;
            VTable.Assert((transfereeDi != null) && (targetDi != null));
            //Monitoring.Log(Monitoring.Provider.ChannelService,
            //               (ushort)ChannelServiceEvent.TransferContentOwnership, 0,
            //               (uint)transfereeDi.ProcessId,
            //               (uint)targetDi.ProcessId,
            //               (uint)transfereeDi.ChannelId,
            //               (uint)targetDi.ChannelId,
            //               (uint)targetDi.Peer.ChannelId);
            int toProcessId = targetDi.ProcessId;
            transfereeDi.ProcessId = toProcessId;
            DelegationState newstate = transfereeDi.OwnerDelegationState;
            transfereeDi.OwnerPrincipalHandle =
                TransferPrincipal(transfereeDi.OwnerPrincipalHandle, toProcessId, ref newstate);
            transfereeDi.OwnerDelegationState = newstate;
            Allocation* transfereePeerAllocation = transfereeDi.Peer();
            // also transfer the peer allocation
            Allocation.SetOwnerProcessId(transfereePeerAllocation, toProcessId);
        }

        public static int OpenChannelCount {
            [NoHeapAllocation]
            get { return openChannelCount; }
        }

        public static void IncOpenChannelCount () {
            Interlocked.Increment(ref openChannelCount);
        }

        public static void DecOpenChannelCount () {
            Interlocked.Decrement(ref openChannelCount);
        }

        //
        //  These getter defer to the delivery implementation, as the kernel only
        //  trusts the shadow versions held in Kernel memory space.
        //
        public bool PeerClosed()
        {
            DeliveryImpl di = EndpointDeliveryImpl;
            if (di != null) {
                return di.PeerClosed();
            } else {
                // endpoint has not yet been connected
                return true;
            }
        }

        /// <summary>
        /// Return a handle for the peer
        /// </summary>
        public Allocation* Peer(out bool marshall)
        {
            DeliveryImpl di = EndpointDeliveryImpl;
            VTable.Assert(di != null);
            return di.Peer(out marshall);
        }

        public int ChannelId
        {
            [NoHeapAllocation]
            get {
                DeliveryImpl di = EndpointDeliveryImpl;
                VTable.Assert(di != null);
                return di.ChannelId;
            }
        }

        public int ProcessId
        {
            [NoHeapAllocation]
            get {
                DeliveryImpl di = EndpointDeliveryImpl;
                VTable.Assert(di != null);
                return di.ProcessId;
            }
        }

        public int ReceiveCount
        {
            get {
                DeliveryImpl di = EndpointDeliveryImpl;
                VTable.Assert(di != null);
                return di.ReceiveCount;
            }
        }

        public int PeerProcessId
        {
            [NoHeapAllocation]
            get {
                DeliveryImpl di = EndpointDeliveryImpl;
                VTable.Assert(di != null);
                return di.PeerProcessId;
            }
        }

        public DeliveryHandle dImpHandle
        {
            get {
                return deliveryHandle;
            }
            set {
                deliveryHandle = value;
            }
        }

        public AutoResetEventHandle CollectionEvent
        {
            get {
                return collectionEvent;
            }
            set {
                collectionEvent = value;
            }
        }

        internal static int GetNextChannelId()
        {
            return Interlocked.Increment(ref channelIdGenerator);
        }

        //
        // These methods only set the user accessable cached copies, real changes should
        // be made to the delivery implementation copies.
        //
        [NoHeapAllocation]
        public void SetCachedClose(bool closed) { cachedClosed = closed; }
        [NoHeapAllocation]
        public void SetCachedProcessId(int pid) { cachedOwnerProcessId = pid; }
        [NoHeapAllocation]
        public void SetCachedChannelId(int cid) { cachedChannelId = cid; }
        [NoHeapAllocation]
        public void SetCachedMarshall(bool marshall) { cachedMarshall = marshall; }
        [NoHeapAllocation]
        public void SetCachedMessageEvent(AutoResetEventHandle mh)
        {
            cachedMessageEvent = mh;
        }
        [NoHeapAllocation]
        public void SetCachedPeer(Allocation * /* EndpointCore */ peer)
        {
            cachedPeer = peer;
        }
        [NoHeapAllocation]
        public void SetPeerStateValid(bool valid)
        {
            peerStateValid = valid;
        }

    }

    public class EndpointCoreException: Exception
    {
        public EndpointCoreException (string message) : base(message)
        {
        }
    }
}

