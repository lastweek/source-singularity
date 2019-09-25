// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

// #define DEBUG_TCP

using System;
using System.Collections;
using System.Diagnostics;
using System.Net.IP;
using System.Runtime.CompilerServices;
using System.Threading;

#if !SINGULARITY
using System.Net;
#endif

using NetStack.Common;
using NetStack.Protocols;
using NetStack.Contracts;

using Microsoft.Contracts;
using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

using Microsoft.Singularity.NetStack.Events;

using Eventing = Microsoft.Singularity.Eventing;

namespace NetStack.Runtime
{
    /// <summary>
    /// The 'TCP' specialization of the Session class.
    /// </summary>
    public class TcpSession : Session   // BUGBUG: REMOVE locks after having the incoming packets send to the TcpSession thread.  // TODO
    {
        /// <summary>
        /// Kinds of Timeout that are used in TCP.
        /// </summary>
        public enum TcpTimeoutType {
            Unknown = 0,
            Connect,
            Persist,
            Shutdown,
            Retransmit,
        };

        /// <summary>
        /// Names corresponding to Enums, above (reflection missing).
        /// </summary>
        internal static readonly string[] TcpTimeoutTypeNames = new string[] {
            "Unknown",
            "Connect",
            "Persist",
            "Shutdown",
            "Retransmit",
        };

        // the session's transmit q size (num of packets)
        public const int TxQSize=100;

        // the session's receive q size (num of packets)
        public const int RcvQSize=100;

        // the maximum number of retries to send before giving up
        private const int MaxRetries = 5;

        // the number of seconds to wait for an active connect to succeed
        private const int ActiveConnectTimeout = 15;

        // the number of seconds to wait for a passive connect to succeed
        private const int PassiveConnectTimeout = 5;

        // the number of seconds between probes of a remote host that has
        // closed its receive window
        private const int PersistTimeout = 2;

        // the number of seconds to wait for a graceful shutdown to complete
        private const int PoliteShutdownTimeout = 10;

        // 3s in ms, Per RFC 2988
        private const uint InitialRetransInterval = 3000u;

        // 200ms, more aggressive than RFC "SHOULD" of 1s
        private const uint MinimumRetransInterval = 200u;

        // Per-session retransmission state
        private uint retransInterval = InitialRetransInterval;
        private uint srtt = InitialRetransInterval;
        private uint rttvar = 0u;

        /// <summary>Object used to Lock the entire TcpSession.</summary>
        /// <remarks>"this" is not used to as it is visible.</remarks>
        private object lockHolder = new object();

        // States of the session, current and former.
        internal TcpStateEnum oldStateEnum; // our previous (FSM) state's enumeration.
        internal TcpState currentState;     // our current (FSM) state

        // Error, if any, from the last Connect request
        internal TcpError connectError;

        // accepted session list (TcpSessions)
        private ArrayList acceptedSessions;
        private int maxAcceptedSessions;

        // a monitor for the accepted session list
        private object acceptSessionMonitor;

        // the passive session (owner) of this session
        // (applied to passive sessions)
        internal TcpSession passiveSession;

        // the retransmit queue
        private const int RetransmitQSize = 100;
        private ArrayList retransmitQ;

        // TCP retransmission timer
        private RJBlack.Timer retransTimer;

        // Setup / teardown timers
        private RJBlack.Timer connectTimer;
        private RJBlack.Timer shutdownTimer;

        // Information on the "persist" state (for when the remote host
        // has closed its receive window)
        private RJBlack.Timer persistTimer;

        // An event that gets set when initial establishment either
        // succeeds or times out
        internal System.Threading.ManualResetEvent setupCompleteEvent;

        // An event that gets set when we're done shutting down this session
        internal System.Threading.ManualResetEvent closedEvent;

        // is this session is valid for USERS to read/write data
        protected bool isValidForRead, isValidForWrite;

        // Whether or not BindLocalEndPoint() has been called
        bool haveBound = false;

        public bool ValidForRead
        {
            get { return isValidForRead; }
            set { isValidForRead = value; }
        }

        public bool ValidForWrite
        {
            get { return isValidForWrite;}
            set {isValidForWrite=value;}
        }

        // TCB
        public struct TCB
        {
            public SNDValues SND;
            public RCVValues RCV;

            // send parameters
            public struct SNDValues
            {
                public uint UNA;     // UNAcknowledged send sequence number
                public uint NXT;     // send seqnum that will be transmitted
                public uint WND;     // send window
                public uint UP;      // send urgent pointer
                public uint WL1;     // segment seq number used for last window update
                public uint WL2;     // segment ack number used for last window update
                public uint ISS;     // initial send sequence number
                public uint NextSeq; // next sequence number to use when packetizing
                                     // (not the same as NXT)
            }

            // receive parameters
            public struct RCVValues
            {
                public uint NXT;     // receive next
                public uint WND;     // receive window
                public uint UP;      // receive urgent pointer
                public uint IRS;     // initial receive sequence number
            }
        }

        // the session's TCB
        internal TCB sessionTCB;

        [NotDelayed]
        public TcpSession(IProtocol! p)
            : base(p, TxQSize, RcvQSize)
        {
            sessionTCB           = new TCB();
            sessionTCB.SND.WND   = TcpFormat.TCP_MSS;
            sessionTCB.RCV.WND   = TcpFormat.TCP_MSS;
            retransmitQ          = new ArrayList(RetransmitQSize);
            acceptedSessions     = new ArrayList();
            maxAcceptedSessions  = 0;                   // Changed by Listen()
            acceptSessionMonitor = new object();

            setupCompleteEvent = new System.Threading.ManualResetEvent(false);
            closedEvent        = new System.Threading.ManualResetEvent(false);
            passiveSession     = null;

            // at first the session is valid (user can interact with it)
            isValidForRead  = true;
            isValidForWrite = true;

            // Assign the undifferentiated state (the parent of the
            //  specialized states) and then change the state to CLOSED.
            this.oldStateEnum = TcpStateEnum.Undefined;
            this.currentState = TcpState.InstanceOfUndefined();
            ChangeState(TCPFSM.CLOSED);
        }

        public new void ReInitialize(IProtocol! protocol)
        {
            base.ReInitialize(protocol);
            sessionTCB          = new TCB();
            sessionTCB.SND.WND  = TcpFormat.TCP_MSS;
            sessionTCB.RCV.WND  = TcpFormat.TCP_MSS;
            maxAcceptedSessions = 0;
            passiveSession      = null;
            isValidForRead      = true;
            isValidForWrite     = true;

            DrainQueue(outQueue);
            DrainQueue(inQueue);
            retransmitQ.Clear();
            acceptedSessions.Clear();
            setupCompleteEvent.Reset();
            closedEvent.Reset();

            // create and initialize the init state
            this.oldStateEnum = TcpStateEnum.Undefined;
            if (!IsClosed) {
                ChangeState(TCPFSM.CLOSED);
            }

            DestroyConnectTimer();
            DestroyShutdownTimer();
            DestroyPersistTimer();

            retransInterval = InitialRetransInterval;
        }

        public bool IsClosed
        {
            get { return this.currentState == TCPFSM.CLOSED; }
        }

        private void DestroyTimer(ref RJBlack.Timer timer, string timerName)
        {
            if (timer == null) {
                DebugPrint("TCP: Ses{0,3} ({1}) No {2} Timer to Destroy.",
                           this.Uid, this.currentState.StateName, timerName);
            }

            if (timer != null) {    // BUGBUG: Lock done on "timers" in RemoveTimeoutCallback.  Is there a nulling race?  // TODO
                bool removeWorked =
                    Core.Instance().TheDispatcher.RemoveTimeoutCallback(timer);
                DebugPrint("TCP: Ses{0,3} ({1}) Destroy {2} Timer {3}.",
                           this.Uid,
                           this.currentState.StateName,
                           timerName,
                           (removeWorked) ? "Worked" : "Failed");
                timer = null;
            }
        }

        internal void DestroyConnectTimer()
        {
            DestroyTimer(ref connectTimer, "Connect");
        }

        internal void DestroyPersistTimer()
        {
            DestroyTimer(ref persistTimer, "Persist");
        }

        internal void DestroyShutdownTimer()
        {
            DestroyTimer(ref shutdownTimer, "Shutdown");
        }

        internal void DestroyRetransmitTimer()
        {
            DestroyTimer(ref retransTimer, "Retransmit");
        }

        [ Conditional("DEBUG_TCP") ]
        private static void DebugPrint(string format, params object [] args)
        {
            Core.Log(format, args);
        }

        public void LogStateChangeContractCall(TcpSessionEventsSource.TcpSessionContractEntrypoints entrypoint)
        {
            TcpSessionEventsSource.EventLog.LogSessionStateChangeContractCall(
                            Uid,
                            currentState.StateEnum,
                            entrypoint);
        }

        public void LogDataTransferContractCall(TcpSessionEventsSource.TcpSessionContractEntrypoints entrypoint)
        {
            TcpSessionEventsSource.EventLog.LogSessionDataTransferContractCall(
                            Uid,
                            currentState.StateEnum,
                            entrypoint);
        }

        public void LogQueryContractCall(TcpSessionEventsSource.TcpSessionContractEntrypoints entrypoint)
        {
            TcpSessionEventsSource.EventLog.LogSessionQueryContractCall(
                            Uid,
                            currentState.StateEnum,
                            entrypoint);
        }

        public void LogInfoContractCall(TcpSessionEventsSource.TcpSessionContractEntrypoints entrypoint)
        {
            TcpSessionEventsSource.EventLog.LogSessionInfoContractCall(
                            Uid,
                            currentState.StateEnum,
                            entrypoint);
        }

        internal void StartConnectTimer()
        {
            ulong timeout;

            if (passiveSession != null) {
                timeout = PassiveConnectTimeout;
            }
            else {
                timeout = ActiveConnectTimeout;
            }

            Dispatcher.Callback fun = new Dispatcher.Callback(OnConnectTimeout);
            ulong expiryTime = (ulong)DateTime.UtcNow.Ticks + (timeout * DateTime.TicksPerSecond);
            connectTimer = Core.Instance().TheDispatcher.AddCallback(fun, null, expiryTime);
        }

        internal NetStatus OnConnectTimeout(Dispatcher.CallbackArgs args)
        {
            // We failed to become established in time. Bail out.
            TcpSessionEventsSource.EventLog.LogTimeout(
                Uid,
                currentState.StateEnum,
                TcpTimeoutType.Connect);

            Terminate(null, TcpError.Timeout);
            return NetStatus.Code.PROTOCOL_OK;
        }

        internal void InitializeServerSession(uint recvSequence, uint window)
        {
            this.InitializeSession(recvSequence,
                                   (uint)DateTime.UtcNow.Ticks,
                                   window);
        }

        internal void InitializeSession(uint recvSequence,
                                        uint sendSequence,
                                        uint window)
        {
            sessionTCB.RCV.IRS = recvSequence;
            sessionTCB.RCV.NXT = recvSequence + 1;
            sessionTCB.SND.ISS = sendSequence;
            sessionTCB.SND.UNA = sendSequence;
            sessionTCB.SND.NXT = sendSequence + 1;
            sessionTCB.SND.NextSeq = sendSequence + 1;
            sessionTCB.SND.WND = window;
            sessionTCB.RCV.WND = TcpFormat.TCP_MSS;
        }

        // change the state of this session
        internal void ChangeState(TcpState! newState)
        {
            lock (this.lockHolder)
            {
                assert(currentState != null);

                // Log upcoming State Change
                TcpSessionEventsSource.EventLog.LogSessionStateChange(
                    Uid,
                    currentState.StateEnum,
                    newState.StateEnum);
#if false
                TcpSessionEvents.EventLog.TcpSessionStateChangeEvent(
                    (ushort)Uid,
                    (TcpSessionEvents.TcpSessionState)currentState.StateEnum,
                    (TcpSessionEvents.TcpSessionState)newState.StateEnum);
#endif
                // Old State's Exit Processing
                currentState.OnStateLeave(this, newState);

                // Actual State Change
                oldStateEnum = currentState.StateEnum;
                currentState = newState;

                // New State's Entry Processing
                currentState.OnStateEnter(this);
            }
        }

        // the message is dispatched to the sessions. the sender
        // is the protocol and the context is session specific
        // (i.e., TCP can pass the TCP header to avoid
        // processing it again at the session instance)
        public delegate NetStatus OnPacketReceive(object     sender,
                                                  NetPacket! packet,
                                                  object     context);

        // this is the state's delegate for handling the
        // protocol triggered event
        // the object parameter will be set to IProtocol interface
        internal override NetStatus OnReceive(object     sender,
                                              NetPacket! packet,
                                              object     context)
        {
            assert(context != null);
            assert(currentState != null);

            NetStatus returnCode;

            // Log "Received Packet" Event.
            TcpSessionEventsSource.EventLog.LogReceivedPacket(
                Uid,
                currentState.StateEnum,
                ((TcpFormat.TcpHeader)context).res2_flags,
                (uint) packet.Available);

            // Perform State-specific Packet Receive
            //  handling (and potential StateChange) under lock.
            lock (this.lockHolder)
            {
                // process it in the current state's context
                returnCode = currentState.OnPacketReceive(this, packet, context);
            }

            return returnCode;
        }

        private void StartPersistTimer()
        {
            Dispatcher.Callback fun = new Dispatcher.Callback(OnPersistTimeout);
            ulong expiryTime = (ulong)DateTime.UtcNow.Ticks + (PersistTimeout * DateTime.TicksPerSecond);
            persistTimer = Core.Instance().TheDispatcher.AddCallback(fun, null, expiryTime);
        }

        internal void StopPersistTimer()
        {
            if (persistTimer != null) {
                DestroyPersistTimer();
            }
        }

        internal bool InPersistState()
        {
            return persistTimer != null;
        }

        internal uint FreeRemoteWindowBytes()
        {
            // The portion of the remote window that is available is the most recently
            // advertised window size minus any outstanding unacknowledged data
            return sessionTCB.SND.WND - (sessionTCB.SND.NXT - sessionTCB.SND.UNA);
        }

        // Called when SND.WND is updated
        internal void HandleWindowUpdate()
        {
            uint newWindow = sessionTCB.SND.WND;

            if (InPersistState() && (newWindow > 0)) {
                // The remote receive window just reopened
                StopPersistTimer();
            }

            // The window update may have made it newly possible to transmit
            // queued data.
            if ((FreeRemoteWindowBytes() > 0) &&
                (outQueue.Count > 0)) {
                Core.Instance().SignalOutboundPackets();
            }
        }

        private NetStatus OnPersistTimeout(Dispatcher.CallbackArgs timeoutArg)
        {
            //
            // NOTE: This is a hack. A proper TCP stack is supposed to
            // transmit a packet consisting of just one byte when probing the
            // remote host to see if it has reopened its receive window.
            // However, we prepacketize data, so we don't have that option.
            // Instead, we probe using full packets.
            //
            TcpSessionEventsSource.EventLog.LogTimeout(
                Uid,
                currentState.StateEnum,
                TcpTimeoutType.Persist);

            TcpSegment seg = null;

            if (retransmitQ.Count > 0) {
                // Use the oldest unacknowledged packet to probe
                seg = (TcpSegment)retransmitQ[0];

            }
            else {
                // Nothing in the retransmit queue; probe using the next
                // normal packet. This will transition the packet to the
                // retransmission queue.
                seg = GetNextPacket(true /*ignore window*/ );
            }

            if (seg != null) {
                seg.Mux = BoundMux;
                NetStatus err = Protocol.OnProtocolSend(seg);
                assert err == NetStatus.Code.PROTOCOL_OK;
            }

            if (currentState != TCPFSM.CLOSED) {
                // rearm
                StartPersistTimer();
            }

            return NetStatus.Code.PROTOCOL_OK;
        }

        private TcpSegment GetNextPacket(bool ignoreReceiverWindow)
        {
            // No Packets if the OutQueue is Empty OR IF the Session is Closed.
            // BUGBUG: Need some way to prevent Closed Sessions from retransmitting.  // TODO
            if ((outQueue.Count == 0) /*|| (currentState == TCPFSM.CLOSED)*/ ) {
                return null;
            }

            lock (outQueue.SyncRoot) {
                // recheck after lock
                if (outQueue.Count == 0) {
                    return null;
                }

                if (((TcpSegment!)outQueue[0]).retries > 0) {
                    // Special case: the head packet is a retransmission. No special work.
                    return (TcpSegment)base.GetPacket(outQueue, false, TimeSpan.Zero); // non blocking

                }
                else {
                    // The head packet is *not* a retransmission. Make sure we
                    // have room to to move it to the retransmission queue.
                    if (retransmitQ.Count < retransmitQ.Capacity) {
                        TcpSegment nextSegment = (TcpSegment)outQueue[0];
                        assert nextSegment != null;
                        uint segSize = nextSegment.GetSegmentLength();

                        if ((!ignoreReceiverWindow) && (segSize > FreeRemoteWindowBytes())) {
                            return null; // Don't overrun the receiver
                        }

                        // Call the base class to dequeue the packet in an orderly way
                        TcpSegment! seg = (TcpSegment!)base.GetPacket(outQueue, false, TimeSpan.Zero); // non blocking
                        assert seg == nextSegment;

                        if (!seg.isAck) {
                            // save it for RTT adjustments
                            seg.sendTime = (ulong)DateTime.UtcNow.Ticks;
                            retransmitQ.Add(seg);

                            // Make sure the retransmitQ stays sorted
                            if (retransmitQ.Count > 1) {
                                TcpSegment! previousTail = (TcpSegment!)retransmitQ[retransmitQ.Count - 2];
                                assert TCPFSM.TCPSeqGreater(seg.seq, previousTail.seq);
                            }

                            // Kick off the retransmit timer if we are first
                            if (retransTimer == null) {
                                RestartRetransTimer();
                            }

                        }
                        else if (segSize == 0) {
                            segSize = 1; // ACKs take up one segment number
                        }

                        // Advance the NXT counter since we're about to put this
                        // segment on the wire
                        sessionTCB.SND.NXT = seg.seq + segSize;
                        return seg;
                    }
                }
            }

            return null;
        }

        // NB: call *after* removing or adding items to the retransmitQ
        internal void RestartRetransTimer()
        {
            DestroyRetransmitTimer();

            if (retransmitQ.Count > 0) {
                // TODO: We should use a dynamically-calculated timeout interval
                ulong expirationTime =
                    (ulong)DateTime.UtcNow.Ticks +
                    (ulong)TimeSpan.FromMilliseconds(retransInterval).Ticks;

                retransTimer = Core.Instance().TheDispatcher.AddCallback(
                    new Dispatcher.Callback(OnRetransmitTimeout),
                    null,
                    expirationTime);
#if false
                if (currentState == TCPFSM.CLOSED) {
                    DestroyRetransmitTimer();  // TEMP FOR DEBUGGING - REMOVE  // TODO
                }
#endif
            } // else all data has been acknowledged
        }

        internal void FlushRetransmissions()
        {
            DestroyRetransmitTimer();
            retransmitQ.Clear();
        }

        private void UpdateRTT(uint measurement)
        {
            const uint MaxCredibleMeasurement = 10000; // 10s in ms
            uint newInterval;

            if (measurement > MaxCredibleMeasurement) {
                // Garbage
                return;
            }

            if (retransInterval == InitialRetransInterval) {
                // We have never set the session RTT.
                srtt = measurement;
                rttvar = srtt / 2;
                newInterval = measurement * 2;
            }
            else {
                // Second or subsequent measurement. Per RFC 2988
                uint abs_srtt_meas = (srtt > measurement)
                    ? srtt - measurement : measurement - srtt;
                rttvar = ((rttvar * 3) / 4) + (abs_srtt_meas / 4);
                srtt = ((7 * srtt) / 8) + (measurement / 8);
                newInterval = srtt + (4 * rttvar);
            }

            this.retransInterval = (newInterval < MinimumRetransInterval)
                ? MinimumRetransInterval : newInterval;
        }

        // Process a remote acknowledgement of data up to the given sequence number
        internal void ACKThrough(uint seqNum)
        {
            ulong nowTicks = (ulong)DateTime.UtcNow.Ticks;
            int removed = 0;

            // Pop packets off the retransmitQ through the acked seqnum
            TcpSegment tcpSegmentOrNull;
            while (retransmitQ.Count > 0) {
                TcpSegment! headSeg = (TcpSegment!)retransmitQ[0];
                uint headNextBytesSequenceNumber =
                    headSeg.seq + headSeg.GetSegmentLength();

                // If this head segment is still needed, break out of the loop.
                if (TCPFSM.TCPSeqGreater(headNextBytesSequenceNumber, seqNum)) {
                    break;
                }

                // Make sure the queue is in exact order
                if (retransmitQ.Count > 1) {
                    TcpSegment! nextSeg = (TcpSegment!)retransmitQ[1];
                //  assert TCPFSM.TCPSeqEQ(headNextBytesSequenceNumber,
                //                         nextSeg.seq);
                    assert TCPFSM.TCPSeqLess(headSeg.seq, nextSeg.seq); // Old, Weak: Remove // TODO
                }

                // Otherwise, head segment isn't needed anymore.  Remove it.
                retransmitQ.RemoveAt(0);
                removed++;

                // Use this ACK for RTT calculations.
                // Ignore ACKs for retransmitted data.
                if (headSeg.retries == 0) {
                    UpdateRTT(headSeg.GetRTT(nowTicks));
                }
            }

            if (removed > 0) {
                RestartRetransTimer();
            }
            // else this ACK didn't acknowledge any new data

            // INVARIANT: the head of the retransmit queue must contain
            // the first unacked seqnum.
            if (retransmitQ.Count > 0) {
                TcpSegment! headSeg = (TcpSegment!)retransmitQ[0];

                bool hasFirstUnacked =
                    TCPFSM.TCPSeqLEQ(headSeg.seq, sessionTCB.SND.UNA) &&
                    TCPFSM.TCPSeqGEQ(headSeg.seq + headSeg.GetSegmentLength(), sessionTCB.SND.UNA);

                if (hasFirstUnacked == false) {
                    Core.Log("TCP: Ses{0,3} ({1}) RETRANSMIT QUEUE SEQUENCE " +
                             "NUMBER FAILURE; FirstSegmentStart,End = {2}, {3};"
                             + "Unacknowledged = {4}.",
                             this.Uid,
                             this.currentState.StateName,
                             headSeg.seq,
                             headSeg.seq + headSeg.GetSegmentLength() - 1,
                             sessionTCB.SND.UNA);
                }

                //assert hasFirstUnacked;   // BUGBUG: Must reactivate before Sprint End // TODO
            }

            // We may have paused transmission so as to not overrun the receiver.
            // Poke the netstack core to be sure we get serviced if we have data
            // to send.
            if ((FreeRemoteWindowBytes() > 0) &&
                (outQueue.Count > 0)) {
                Core.Instance().SignalOutboundPackets();
            }
        }

        // we need to override GetPacket. We transmit the packet
        // and put it in the retransmit queue until we get an ack.
        // (we only do it for data segments including SYN which counts for one)
        // if a timer expired before ack, we retransmit it until we give up.
        override internal NetPacket GetPacket(ArrayList! q, bool toBlock, TimeSpan timeout)
        {
            // We only concern ourselves with the remote host's receive window in states
            // where we are transmitting
            bool shouldRespectRemoteWindow =
                (currentState != TCPFSM.CLOSED) &&
                (currentState != TCPFSM.LISTEN) &&
                (currentState != TCPFSM.SYN_SENT) &&
                (currentState != TCPFSM.SYN_RECVD);

            // There needs to be at least one packet-worth of space in the send-window for us
            // to be sure we won't overrun the remote host.
            if (shouldRespectRemoteWindow && (sessionTCB.SND.WND == 0)) {
                // Make sure the persist timer is ticking

                if (!InPersistState()) {
                    StartPersistTimer();
                } // else already in the persist state

            }
            else {
                StopPersistTimer();
                return GetNextPacket(false);
            }

            return null;
        }

        private void PriorityEnqueuePacket(ArrayList! queue, NetPacket! packet)
        {
            lock (queue.SyncRoot) {
                // This may increase the capacity of the queue.  We probably want
                // watermark limit for user additions to the queue and not worry about
                // internal additions to the queue.
                queue.Insert(0, packet);
            }

            // Poke the core to service our queue
            Core.Instance().SignalOutboundPackets();
        }

        // Handler for TCP timeouts
        internal NetStatus OnRetransmitTimeout(Dispatcher.CallbackArgs timeoutArg)
        {
            TcpSessionEventsSource.EventLog.LogTimeout(
                Uid,
                currentState.StateEnum,
                TcpTimeoutType.Retransmit);

            if (!InPersistState()) {
                // Retransmit the oldest unacknowledged packet
                assert retransmitQ.Count > 0;
                TcpSegment! oldest = (TcpSegment!)retransmitQ[0];
                ++oldest.retries;

                if (oldest.retries >= MaxRetries) {
                    // Give up
                    Abort(TcpError.Timeout);
                    return NetStatus.Code.PROTOCOL_OK;
                }

                // INVARIANT: the head of the retransmit queue must contain
                // the first unacked seqnum
                if (retransmitQ.Count > 0) {
                    // TODO: make this an assert
                    TcpSegment! headSeg = (TcpSegment!)retransmitQ[0];

                    bool hasFirstUnacked =
                        TCPFSM.TCPSeqLEQ(headSeg.seq, sessionTCB.SND.UNA) &&
                        TCPFSM.TCPSeqGreater(headSeg.seq + headSeg.GetSegmentLength(), sessionTCB.SND.UNA);

                    assert hasFirstUnacked;
                }

                PriorityEnqueuePacket(outQueue, oldest);
            }
            else {
                // we're in the persist state and retransmissions are suspended.
            }

            // Back off!
            retransInterval = retransInterval * 2;

            RestartRetransTimer();
            return NetStatus.Code.PROTOCOL_OK;
        }

        internal override bool IsSessionValidForUserRead()
        {
            return isValidForRead;
        }

        internal override bool IsSessionValidForUserWrite()
        {
            return isValidForWrite;
        }

        // data can be still available on a non-valid session
        public bool IsDataAvailable()
        {
            return (inQueue.Count>0);
        }

        // Callback type for packetizing data
        private delegate void CopyDataDelegate(byte[]! intoArray, int sourceOffset,
                                               int destOffset, int length);

        // Helper delegate for dealing with GC data
        private class GCDataCopier
        {
            private byte[] gcData;

            public GCDataCopier(byte[] gcData)
            {
                this.gcData = gcData;
            }

            public void CopyData(byte[]! intoArray, int sourceOffset,
                                 int destOffset, int length)
            {
                if (sourceOffset + length > gcData.Length) {
                    throw new Exception("Overrun of GC data helper");
                }

                Array.Copy(gcData, sourceOffset, intoArray,
                           destOffset, length);
            }
        }

        // Helper class for dealing with ExHeap data
        private class ExHeapDataCopier
        {
            VContainer<byte> exHeapData;

            public ExHeapDataCopier([Claims] byte[]! in ExHeap exHeapData)
            {
                this.exHeapData = new VContainer<byte>(exHeapData);
            }

            public void CopyData(byte[]! intoArray, int sourceOffset,
                                 int destOffset, int length)
            {
                if (this.exHeapData == null) {
                    throw new Exception("ExHeapDataCopier used after Destroy()");
                }

                byte[]! in ExHeap exHeapData = this.exHeapData.Acquire();

                try {
                    if (sourceOffset + length > exHeapData.Length) {
                        throw new Exception("Overrun of ExHeap data helper");
                    }

                    Bitter.ToByteArray(exHeapData, sourceOffset, length,
                                       intoArray, destOffset);
                }
                finally {
                    this.exHeapData.Release(exHeapData);
                }
            }

            public void Destroy()
            {
                // Explicitly discard our ExHeap object
                byte[]! in ExHeap data = this.exHeapData.Acquire();
                delete data;
                this.exHeapData = null;
            }
        }

        public int WriteData([Claims] byte[]! in ExHeap data)
        {
            int dataLength = data.Length;
            ExHeapDataCopier helper = new ExHeapDataCopier(data);
            int retval = InternalWrite(new CopyDataDelegate(helper.CopyData), dataLength);

            // Make sure the ExHeap block gets thrown away immediately to
            // reduce pressure on the finalizer thread
            helper.Destroy();

            return retval;
        }

        override public int WriteData(byte[]! data)
        {
            GCDataCopier helper = new GCDataCopier(data);
            return InternalWrite(new CopyDataDelegate(helper.CopyData), data.Length);
        }

        // here we create the segments from the data
        // The user is blocked until we have more room.
        // we return -1 if we can't write (session is not established)
        // TBC: according to the spec, when TCP is about to send it, if there is not
        // enough space at the peer receive buffer it can split it
        // to several smaller segments.
        private int InternalWrite(CopyDataDelegate! dataCopier, int dataSize)
        {
            if (!ValidForWrite) {
                return -1;
            }

            // This is the number of full packets to send
            uint mssCount = (uint)(dataSize / TcpFormat.TCP_MSS);

            // This is the size of the last (non-full) packet.
            uint mssResidue = (uint)(dataSize % TcpFormat.TCP_MSS);

            int readIndex = 0;
            uint segSequence = sessionTCB.SND.NextSeq;

            const int baseFrameSize = EthernetFormat.Size + IPFormat.Size + TcpFormat.Size;

            while (mssCount != 0) {
                // create a TCP segment without options

                // handle the data first
                byte[] pktData = new byte[baseFrameSize + TcpFormat.TCP_MSS];
                dataCopier(pktData, readIndex, baseFrameSize, TcpFormat.TCP_MSS);

                TcpFormat.WriteTcpSegment(pktData,this.LocalPort,
                                          this.RemotePort, sessionTCB.RCV.NXT,
                                          segSequence, TcpFormat.TCP_MSS,
                                          this.LocalAddress,
                                          this.RemoteAddress,
                                          TcpFormat.TCP_MSS,
                                          true,false,false,false,false);

                TcpSegment seg = new TcpSegment(pktData, this,
                                                segSequence, false);

                // Send to Event Log.
                TcpSessionEventsSource.EventLog.LogSendingPacket(
                    Uid,
                    (currentState == null) ? TcpStateEnum.Undefined
                                           : currentState.StateEnum,
                    /*((TcpFormat.TcpHeader)context).res2_flags,*/ 0,   // BUGBUG: Get Transmit Flags.  // TODO
                    (uint) seg.GetSegmentLength());

                // the next segment sequence
                segSequence += TcpFormat.TCP_MSS;
                readIndex += TcpFormat.TCP_MSS;
                base.PutPacket(outQueue, seg, true);
                mssCount--;
            }

            if (mssResidue != 0) {
                byte[] pktData = new byte[baseFrameSize + mssResidue];
                dataCopier(pktData, readIndex, baseFrameSize, (int)mssResidue);

                TcpFormat.WriteTcpSegment(pktData,
                                          this.LocalPort,
                                          this.RemotePort,
                                          sessionTCB.RCV.NXT,
                                          segSequence, TcpFormat.TCP_MSS,
                                          this.LocalAddress,
                                          this.RemoteAddress,
                                          (ushort)mssResidue,
                                          true,false,false,false,false);

                TcpSegment seg = new TcpSegment(pktData, this,
                                                segSequence, false);

                // Send to Event Log.
                TcpSessionEventsSource.EventLog.LogSendingPacket(
                    Uid,
                    (currentState == null) ? TcpStateEnum.Undefined
                                           : currentState.StateEnum,
                    /*((TcpFormat.TcpHeader)context).res2_flags,*/ 0,   // BUGBUG: Get Transmit Flags.  // TODO
                    (uint) seg.GetSegmentLength());

                segSequence += mssResidue;
                base.PutPacket(outQueue,seg,true);
            }

            sessionTCB.SND.NextSeq = segSequence;
            // since we always send it all...
            return dataSize;
        }

        public bool BindLocalEndPoint(IPv4 address, ushort port)
        {
            return BindLocalEndPointInternal(address, port);
        }

        public bool BindLocalEndPointInternal(IPv4 address, ushort port)
        {
            lock (this.lockHolder) {
                haveBound = true;
                SetRemoteEndPoint(IPv4.Broadcast, 0);
                return SetLocalEndPoint(address, port);
            }
        }

        // the method is used to make a session active (i.e., active open)
        // TBC: manage local ports automatically
        // we're currently more restrictive regarding user
        // interaction (can't change passive to active etc.)
        public bool Connect(IPv4 dstIP, ushort dstPort, out TcpError error)
        {
            DebugPrint("TCP: Ses{0,3} ({1}) Connect: {2:x8}/{3}",
                       Uid, currentState.StateName, dstIP, dstPort);

            if (currentState != TCPFSM.CLOSED) {
                DebugPrint("TCP: Ses{0,3} ({1}) Connect: Failed because " +
                           "session already connected (not in '{2}' state)",
                           Uid,
                           currentState.StateName,
                           TCPFSM.CLOSED.StateName);
                error = TcpError.AlreadyConnected;
                return false;
            }

            // init the session's parameters
            SetRemoteEndPoint(dstIP, dstPort);

            // Set the local endpoint to "don't care" if the user
            // hasn't called BindLocalEndPoint() previously
            if (!haveBound) {
                SetLocalEndPoint(IPv4.Any, 0);
            }

            sessionTCB.RCV = new TcpSession.TCB.RCVValues();
            sessionTCB.SND = new TcpSession.TCB.SNDValues();

            DrainQueue(outQueue);
            DrainQueue(inQueue);
            retransmitQ.Clear();

            // change this session state to SYNSENT.
            // a SYN message will be sent to the destination
            ChangeState(TCPFSM.SYN_SENT);

            // provide a default error
            this.connectError = TcpError.Unknown;

            // block the user until the session is ready
            setupCompleteEvent.WaitOne();
            setupCompleteEvent.Reset();

            // Check Result; Optional Log; and Return true/false.
            if (currentState != TCPFSM.ESTABLISHED) {
                // The connect failed.
                error = this.connectError;
                DebugPrint("TCP: Ses{0,3} ({1}) Connect: SetupCompleteEvent " +
                           "signalled; Result = failed {2}",
                           Uid, currentState.StateName, error);
                return false;
            }
            else {
                // The connection is up and running properly.
                error = TcpError.Unknown;
                DebugPrint("TCP: Ses{0,3} ({1}) Connect: SetupCompleteEvent " +
                           "signalled; Result = success",
                           Uid, currentState.StateName);
                return true;
            }
        }

        private NetStatus OnShutdownTimedout(Dispatcher.CallbackArgs args)
        {
            TcpSessionEventsSource.EventLog.LogTimeout(
                Uid,
                currentState.StateEnum,
                TcpTimeoutType.Shutdown);

            // No more Mr. Nice Guy
            Abort(TcpError.Timeout);
            return NetStatus.Code.PROTOCOL_OK;
        }

        // close the session
        override public bool Close()
        {
            // Signal that sending is complete; this will start the polite
            // shutdown process.  Changes state to FinWait1 or LastAck.
            // Can block.
            DoneSending();

            // Start a timer to make sure we don't wait for the shutdown
            // forever. TODO: we should use a value passed in by the
            // caller for the timeout rather than hard-coding it.
            Dispatcher.Callback fun = new Dispatcher.Callback(OnShutdownTimedout);
            ulong expiryTime = (ulong)DateTime.UtcNow.Ticks +
                (PoliteShutdownTimeout * DateTime.TicksPerSecond);
            shutdownTimer =
                Core.Instance().TheDispatcher.AddCallback(fun, null, expiryTime);

            // Wait while we complete the shutdown,
            //  drain the outbound queue, etc.
            closedEvent.WaitOne();
            closedEvent.Reset();

            // Remove the Shutdown Timer.
            DestroyShutdownTimer();

            // After a Close() completes, pending data isn't available anymore!
            DrainQueue(inQueue);

            return true;
        }

        // hard-shutdown
        override public bool Abort()
        {
            return Abort(TcpError.Unknown);
        }

        public bool Abort(TcpError error)
        {
            // Abort our connection with a RST segment
            Terminate(TCPFSM.CreateResetSegment(this, true), error);
            return true;
        }

        private void Terminate(TcpSegment finalPacket, TcpError error)
        {
            StopPersistTimer();

            if (currentState == TCPFSM.CLOSED) {
                // Signal anyone waiting, for good measure.
                setupCompleteEvent.Set();
            }
            else {
                // This will set the setup-complete event as a side effect
                TCPFSM.HandleTerminateSession(this, finalPacket, error);
            }
        }

        // passively open a session
        public bool Listen(int backlog)
        {
            if (currentState != TCPFSM.CLOSED)
                return false;

            // User must have previously bound
            if (!haveBound) {
                return false;
            }

            maxAcceptedSessions = backlog;
            ChangeState(TCPFSM.LISTEN);
            return true;
        }

        /// <summary>
        /// Block until a new connection is available,
        /// accept it, and return a new TcpSession.
        /// </summary>
        /// <remarks>
        /// The TcpSession (this) must be in the "Listen" state.
        /// </remarks>
        public TcpSession Accept()
        {
            if (currentState != TCPFSM.LISTEN)
                return null;

            TcpSession tcpSession = null;

            // block the user until a session is available
            lock (acceptSessionMonitor) {
                while (acceptedSessions.Count == 0) {
                    Monitor.Wait(acceptSessionMonitor);
                }

                tcpSession = (TcpSession)acceptedSessions[0];
                acceptedSessions.RemoveAt(0);
            }

            return tcpSession;
        }

        // Returns false if our queue is full
        internal bool AddAcceptedSession(TcpSession newSession)
        {
            lock (acceptSessionMonitor) {
                if (AcceptQueueIsFull()) {
                    return false;
                }
                else {
                    acceptedSessions.Add(newSession);
                    Monitor.PulseAll(acceptSessionMonitor);
                    return true;
                }
            }
        }

        // Indicate whether there are queued sessions waiting to be Accept()ed
        public int GetNumWaitingListenSessions()
        {
            lock (acceptSessionMonitor) {
                return acceptedSessions.Count;
            }
        }

        // Determine whether the accept queue is full or not
        internal bool AcceptQueueIsFull()
        {
            return GetNumWaitingListenSessions() >= maxAcceptedSessions;
        }

        /// <summary>
        /// Client informs TcpSession that no more data will be sent.
        /// </summary>
        public void DoneSending()
        {
            lock (this.lockHolder) {
                if (!isValidForWrite) {
                    // Nothing to do
                    return;
                }

                isValidForWrite = false;

                switch (currentState.StateEnum) {
                    case TcpStateEnum.Established:
                        // This side first to Close, goto FinWait1
                        TCPFSM.SendFin(this, true); // can block
                        ChangeState(TCPFSM.FIN_WAIT1);
                        break;
                    case TcpStateEnum.CloseWait:
                        // Other side first to Close, goto LastAck
                        TCPFSM.SendFin(this, true); // can block
                        ChangeState(TCPFSM.LAST_ACK);
                        break;
                    default:
                        // We're in some transitory setup or teardown
                        // state; just abort the connection.
                        Abort(TcpError.Closed);
                        break;
                }
            }
        }

        // Indicate that we're done receiving
        public void DoneReceiving()
        {
            ValidForRead = false;
        }
    }

    // a TCP segment
    public class TcpSegment : NetPacket
    {
        // segment identifier
        internal uint seq;          // the segment sequence number
        internal uint retries;      // number of retransmit retries
        internal bool isAck;        // is it an ack segment (no retrans for ack!)
        internal ulong sendTime;    // used to dynamically adjust the RTT

        // create a TcpSegment, add room for lower level protocols
        public TcpSegment(byte[]! buffer) : base(buffer)
        {
            seq=0;
            retries=0;
            isAck=false;
            sendTime=0;
        }

        // the isAck indicates that this is an ack segment
        // (we never ack an ack segment without data)
        [NotDelayed]
        public TcpSegment(byte[]! buffer, TcpSession! tcpSession, uint seqNum, bool isAck) : base(buffer)
        {
            seq=seqNum;
            retries=0;
            this.isAck=isAck;
            sendTime=0;
            this.SessionContext = tcpSession;
        }

        public TcpSession owner
        {
            // owner was a field in TcpSegment, but it mirrors field
            // in NetPacket and one we now use for unblocking after
            // the ARP response comes back.
            get { return this.SessionContext as TcpSession; }
            set { this.SessionContext = value; }
        }

        // return the TCP data segment size
        public uint GetSegmentLength()
        {
            return ((uint)(base.Length - EthernetFormat.Size - IPFormat.Size - TcpFormat.Size));
        }

        public uint GetRTT(ulong receiveTime)
        {
            ulong deltaTime = (receiveTime>sendTime ? receiveTime-sendTime : 0 );
            return (uint)(TimeSpan.FromTicks((long)deltaTime)).Milliseconds;
        }
    }
}
