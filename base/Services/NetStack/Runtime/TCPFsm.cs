// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

// #define DEBUG_TCP

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading;

#if !SINGULARITY
using System.Net;
#endif

using Microsoft.Contracts;

using NetStack.Common;
using TcpError = NetStack.Contracts.TcpError;

namespace NetStack.Runtime
{
    using Protocols;

    public enum TcpStateEnum
    {
        Undefined   = 0,
        Closed      = 1,
        Listen      = 2,
        SynRecvd    = 3,
        SynSent     = 4,
        Established = 5,
        CloseWait   = 6,
        LastAck     = 7,
        FinWait1    = 8,
        FinWait2    = 9,
        Closing    = 10,
    }

    internal class TcpState
    {
        /// <summary>
        /// Names corresponding to Enums, above (reflection missing).
        /// </summary>
        internal static readonly string[] TcpStateNames = new string[] {
            "Undefined",
            "Closed   ",
            "Listen   ",
            "SynRecvd ",
            "SynSent  ",
            "Establish",
            "CloseWait",
            "LastAck  ",
            "FinWait1 ",
            "FinWait2 ",
            "Closing  ",
        };

        private static TcpState! instance = new TcpState();

        internal static TcpState! InstanceOfUndefined()
        {
            return TcpState.instance;
        }

        // ctor
        internal TcpState()
        {
        }

        // make a state transition
        protected void ChangeState(TcpSession! tcpSession, TcpState newState)
        {
            tcpSession.ChangeState((!)newState);
        }

        // enter the new state
        virtual internal void OnStateEnter(TcpSession! tcpSession)
        {
        }

        // a new packet(=event) received, should handle it
        // according to the current state.
        virtual internal NetStatus OnPacketReceive(TcpSession! tcpSession,
                                                   NetPacket! packet,
                                                   object     context)
        {
            return NetStatus.Code.PROTOCOL_OK;
        }

        // leave the current state to the new one
        virtual internal void OnStateLeave(TcpSession! tcpSession, TcpState newState)
        {
        }

        // Handle timeout events.
        // args is a session argument which is session specific
        virtual internal NetStatus OnTimeout(TcpSession! tcpSession, Dispatcher.CallbackArgs args)
        {
            TcpSessionEventsSource.EventLog.LogTimeout(
                tcpSession.Uid,
                tcpSession.currentState.StateEnum,
                TcpSession.TcpTimeoutType.Unknown);

            return NetStatus.Code.PROTOCOL_OK;
        }

        // Get the state name for debugging
        internal string GetStateName()
        {
            return TcpState.TcpStateNames[(int)this.StateEnum];
        }

        // get state enum for eventing (tracing)
        virtual internal TcpStateEnum GetStateEnum()
        {
            return TcpStateEnum.Undefined;
        }

        // State's Enumeration as a Property
        internal TcpStateEnum StateEnum
        {
            get { return this.GetStateEnum(); }
        }

        // State's Name as a Property
        internal string StateName
        {
            get { return TcpState.TcpStateNames[(int)this.StateEnum]; }
        }

        [ Conditional("DEBUG_TCP") ]
        internal static void DebugPrint(string format, params object [] args)
        {
            Core.Log(format, args);
        }

        [ Conditional("DEBUG_TCP") ]
        internal static void DebugPrintLine(string format, params object [] args)
        {
            TcpState.DebugPrint(format, args);
        }
    }

    ///
    // This the TCP Finite State Machine Implementation
    // NOTICE: This is just a quick implementation...
    // should handle FIN, RST, window management, slow start, double acks...
    // 
    internal class TCPFSM
    {

        // Definition of the TCP states
        internal static TcpState! CLOSED { get {return TCPStateClosed.Instance();}}

        internal static TcpState! LISTEN { get {return TCPStateListen.Instance();}}
        internal static TcpState! SYN_RECVD { get {return TCPStateSynRcv.Instance();}}
        internal static TcpState! SYN_SENT  { get {return TCPStateSynSent.Instance();}}
        internal static TcpState! ESTABLISHED  { get {return TCPStateEstab.Instance();}}
        internal static TcpState! CLOSE_WAIT  { get {return TCPCloseWait.Instance();}}
        internal static TcpState! LAST_ACK  { get {return TCPLastAck.Instance();}}

        internal static TcpState! FIN_WAIT1 { get {return TCPFINWait1.Instance();}}
        internal static TcpState! FIN_WAIT2 { get {return TCPFINWait2.Instance();}}
        internal static TcpState! CLOSING { get {return TCPClosing.Instance();}}

        //----------------------------------------------------------------------------

        // Compare two TCP sequence numbers:
        //  - means A < B, 0 means A == B and + means A > B
        [Pure]
        [Inline]
        private static int TcpSequenceNumberCompare(uint seqA, uint seqB)
        {
            // Exploit integer underflow to compare correctly even in the case
            // of sequence number wraparound. This assumes the two numbers are
            // always in the same half of the numberspace.

            return unchecked((int)(unchecked(seqA - seqB)));
        }

        [Pure]
        internal static bool TCPSeqEQ(uint seqA, uint seqB)
        {
            return TCPFSM.TcpSequenceNumberCompare(seqA, seqB) == 0;
        }

        [Pure]
        internal static bool TCPSeqNEQ(uint seqA, uint seqB)
        {
            return TCPFSM.TcpSequenceNumberCompare(seqA, seqB) != 0;
        }

        [Pure]
        internal static bool TCPSeqLEQ(uint seqA, uint seqB)
        {
            return TCPFSM.TcpSequenceNumberCompare(seqA, seqB) <= 0;
        }

        [Pure]
        internal static bool TCPSeqLess(uint seqA, uint seqB)
        {
            return TCPFSM.TcpSequenceNumberCompare(seqA, seqB) < 0;
        }

        [Pure]
        internal static bool TCPSeqGEQ(uint seqA, uint seqB)
        {
            return TCPFSM.TcpSequenceNumberCompare(seqA, seqB) >= 0;
        }

        [Pure]
        internal static bool TCPSeqGreater(uint seqA, uint seqB)
        {
            return TCPFSM.TcpSequenceNumberCompare(seqA, seqB) >  0;
        }

        //----------------------------------------------------------------------------
        internal sealed class TCPStateClosed : TcpState
        {
            static TCPStateClosed! instance = new TCPStateClosed();
            static TCPStateClosed() {}

            internal static TCPStateClosed! Instance()
            {
                return instance;
            }

            // get state enum for eventing (tracing) and debugging.
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.Closed;
            }

            // enter the Closed state
            override internal void OnStateEnter(TcpSession! tcpSession)
            {
                tcpSession.DestroyRetransmitTimer();
            }

            // leave the state
            override internal void OnStateLeave(TcpSession! tcpSession, TcpState newState)
            {
                assert newState != null;
                base.OnStateLeave(tcpSession, newState);
                switch (newState.StateEnum) {
                    case TcpStateEnum.Listen:
                        break;
                    case TcpStateEnum.SynSent:
                        if (!TCPFSM.SendSYN(tcpSession, TcpFormat.TCP_MSS)) {
                            // This should never happen; our outbound
                            // packet queue should never be empty
                            // while we're setting up a session
                            Debug.Assert(false);
                        }
                        break;
                    case TcpStateEnum.SynRecvd:
                        break;
                    default:
                        Core.Panic("TCP: Ses{0,3} ({1}) state machine error!",
                                   tcpSession.Uid, this.StateName);
                        break;
                }
            }

            override internal NetStatus OnTimeout(TcpSession! tcpSession, Dispatcher.CallbackArgs args)
            {
                base.OnTimeout(tcpSession, args);
                return NetStatus.Code.PROTOCOL_OK;
            }

            override internal NetStatus OnPacketReceive(TcpSession! tcpSession,
                                                        NetPacket!  packet,
                                                        object      context)
            {
                // A Closed session cannot handle any packets.
                // BUGBUG: The parent class should make this the default behavior. // TODO
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }
        }

        //----------------------------------------------------------------------------
        // a passive connection listen state
        internal sealed class TCPStateListen : TcpState
        {
            static TCPStateListen! instance = new TCPStateListen();
            static TCPStateListen() {}

            internal static TCPStateListen! Instance()
            {
                return instance;
            }

            // get state enum for eventing (tracing) and debugging.
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.Listen;
            }

            override internal void OnStateEnter(TcpSession! tcpSession) {
                DebugPrintLine("TCP: Ses{0,3} ({1}) Waiting for connections.",
                               tcpSession.Uid, this.StateName);
            }

            override internal NetStatus OnPacketReceive(TcpSession! tcpSession,
                                                        NetPacket! packet,
                                                        object context)
            {
                assert context != null;
                TcpFormat.TcpHeader tcpHeader = (TcpFormat.TcpHeader)context;

                if (TcpFormat.IsReset(ref tcpHeader)) {
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;  // we ignore it
                }

                if (TcpFormat.IsAck(ref tcpHeader)) {
                    SendReset(tcpSession, false);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                if (TcpFormat.IsSync(ref tcpHeader)) {
                    // we received a syn!
                    // create a new TCP session and initialize it (only if
                    // we have room)  TBC: should use listen param for bound)
                    // new session's new state (OnEnter) will send syn-ack
                    //  (this is the result of the ChangeState call).

                    TcpSession client =
                        (TcpSession!)tcpSession.Protocol.CreateSession();
                    client.passiveSession = tcpSession;  // this is our "owner"
                    client.SetLocalEndPoint(tcpSession.LocalAddress,
                                            tcpSession.LocalPort);
                    client.InitializeServerSession(tcpHeader.seq,
                                                   tcpHeader.window);

                    // we have access to the IP header from the packet overlapped
                    // context (TCPModule put it there)
                    IPFormat.IPHeader ipHeader =
                        packet.OverlapContext as IPFormat.IPHeader;
                    assert ipHeader != null;

                    client.SetRemoteEndPoint(ipHeader.Source,
                                             tcpHeader.sourcePort);

                    // Save ourselves work if we should reject the session right away
                    if (tcpSession.AcceptQueueIsFull()) {
                        TcpSegment reset = CreateResetSegment(client, true);
                        tcpSession.Protocol.OnProtocolSend(reset);
                        return NetStatus.Code.PROTOCOL_DROP_ERROR;
                    }

                    // New session starts at syn-rcv.  It immediately (from
                    //  OnEntry) sends a SYN-Ack and starts the connect timer.
                    client.ChangeState(SYN_RECVD);

                    // WE are left at the SAME state!
                    return NetStatus.Code.PROTOCOL_OK;
                }
                else {
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }
            }
        }

        //----------------------------------------------------------------------------
        internal sealed class TCPStateSynRcv : TcpState
        {
            static TCPStateSynRcv! instance = new TCPStateSynRcv();
            static TCPStateSynRcv() {}

            internal static TCPStateSynRcv! Instance()
            {
                return instance;
            }

            // get state enum for eventing (tracing)
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.SynRecvd;
            }

            override internal void OnStateEnter(TcpSession! tcpSession)
            {
                // send syn-ack
                if (!SendSYNAck(tcpSession)) {
                    // This should never happen; our outbound packet queues
                    // should never be full while we're setting up a session.
                    Debug.Assert(false);
                }

                // Start timer to limit the time to establishing the new session
                tcpSession.StartConnectTimer();
            }

            override internal NetStatus OnPacketReceive(TcpSession! tcpSession,
                                                        NetPacket! packet,
                                                        object context)
            {
                assert context != null;
                // all TCP states get the tcpHeader context
                TcpFormat.TcpHeader tcpHeader = (TcpFormat.TcpHeader)context;
                uint segmentSize = (uint)packet.Available;

                bool packetIsAcceptable =
                    IsSegmentAcceptable(tcpSession, ref tcpHeader, segmentSize);

                if (!packetIsAcceptable) {
                    if (!TcpFormat.IsReset(ref tcpHeader)) {
                        // send an ACK; don't care about whether this works
                        //  or not since we're discarding the packet anyhow.
                        TCPFSM.SendAck(tcpSession);
                    }
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                // we accept the segment
                Debug.Assert(tcpHeader.seq == tcpSession.sessionTCB.RCV.NXT);

                // if we get a reset
                if (TcpFormat.IsReset(ref tcpHeader)) {
                    NetStatus.Code result;
                    switch (tcpSession.oldStateEnum) {
                        case TcpStateEnum.Listen:
                            // if we came from the listen state (passive open)
                            // the reset will return us to the Listen state
                            tcpSession.FlushRetransmissions();
                            ChangeState(tcpSession, LISTEN);
                            result = NetStatus.Code.PROTOCOL_DROP_ERROR;
                            break;
                        case TcpStateEnum.SynSent:
                            // we came from SYN_SENT (active open)
                            // the connection was refused, close it!
                            HandleTerminateSession(tcpSession, null, TcpError.Refused);
                            result = NetStatus.Code.PROTOCOL_DROP_ERROR;
                            break;
                        default:
                            result = NetStatus.Code.PROTOCOL_DROP_ERROR;
                            break;
                    }

                    return result;
                }

                if (TcpFormat.IsSync(ref tcpHeader)) {
                    // reset
                    HandleTerminateSession(tcpSession,
                                           CreateResetSegment(tcpSession, false),
                                           TcpError.ProtocolViolation);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                if (TcpFormat.IsAck(ref tcpHeader)) {
                    if (TCPSeqLEQ(tcpSession.sessionTCB.SND.UNA, tcpHeader.ackSeq) &&
                        TCPSeqGEQ(tcpSession.sessionTCB.SND.NXT, tcpHeader.ackSeq))
                    {
                        // enter established state

                        // we get an Ack for our syn-ack
                        // remove the SYN-ACK from the retransmit Q
                        TCPFSM.HandleTCPAck(tcpSession, ref tcpHeader);
                        AttemptToEnterESTABLISHED(tcpSession, ref tcpHeader);
                        return NetStatus.Code.PROTOCOL_OK;
                    }
                    else {
                        // reset
                        HandleTerminateSession(tcpSession,
                                               CreateResetSegment(tcpSession, false),
                                               TcpError.Reset);
                        return NetStatus.Code.PROTOCOL_DROP_ERROR;
                    }
                }

                if (TcpFormat.IsFIN(ref tcpHeader)) {
                    DebugPrintLine("TCP: Ses{0,3} ({1)} TCPStateSynRcv: Received FIN.",
                                   tcpSession.Uid, this.StateName);

                    // RCV.NXT should reflect the data that we processed out of
                    // this packet, but not the FIN. Advance over the FIN.
                    tcpSession.sessionTCB.RCV.NXT += 1;

                    // ack the FIN. Don't worry if this doesn't actually work;
                    // the remote side will think the ACK got lost and retransmit,
                    // which we will hopefully be able to successfully ACK later.
                    SendAck(tcpSession);
                    ChangeState(tcpSession, CLOSE_WAIT);
                }

                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }
        }

        //----------------------------------------------------------------------------
        internal sealed class TCPStateSynSent : TcpState
        {
            static TCPStateSynSent! instance = new TCPStateSynSent();
            static TCPStateSynSent() {}

            internal static TCPStateSynSent! Instance()
            {
                return instance;
            }

            // get state enum for eventing (tracing) and debugging.
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.SynSent;
            }

            override internal void OnStateEnter(TcpSession! tcpSession)
            {
                DebugPrintLine("TCP: Ses{0,3} ({1}) Sending SYN.",
                               tcpSession.Uid, this.StateName);
            }

            // we sent a syn we wait for syn-ack
            override internal NetStatus OnPacketReceive(TcpSession! tcpSession,
                                                        NetPacket! packet,
                                                        object context)
            {
                assert context != null;
                // all TCP states get the tcpHeader context
                TcpFormat.TcpHeader tcpHeader = (TcpFormat.TcpHeader)context;
                bool ackAcceptable=false;

                if (TcpFormat.IsAck(ref tcpHeader)) {
                    if (TCPSeqLEQ(tcpHeader.ackSeq, tcpSession.sessionTCB.SND.ISS) ||
                        TCPSeqGreater(tcpHeader.ackSeq, tcpSession.sessionTCB.SND.NXT))
                    {
                        if (TcpFormat.IsReset(ref tcpHeader)) {
                            return NetStatus.Code.PROTOCOL_DROP_ERROR;
                        }

                        SendReset(tcpSession, false);
                        return NetStatus.Code.PROTOCOL_DROP_ERROR;
                    }

                    if (TCPSeqLEQ(tcpSession.sessionTCB.SND.UNA, tcpHeader.ackSeq) &&
                        TCPSeqLEQ(tcpHeader.ackSeq, tcpSession.sessionTCB.SND.NXT))
                    {
                        ackAcceptable=true;
                    }
                }

                if (TcpFormat.IsReset(ref tcpHeader)) {
                    if (ackAcceptable) {
                        // connection was reset, drop the segment
                        // and close the connection.
                        HandleTerminateSession(tcpSession, null, TcpError.Reset);
                        return NetStatus.Code.PROTOCOL_DROP_ERROR;
                    }
                    else {
                        return NetStatus.Code.PROTOCOL_DROP_ERROR;
                    }
                }

                // check syn
                // ack is is ok or there is no ack and no RST
                if (TcpFormat.IsSync(ref tcpHeader)) {
                    if (ackAcceptable) {
                        DebugPrintLine("TCP: Ses{0,3} ({1}) SYNSENT, Received SYN-ACK",
                                       tcpSession.Uid, this.StateName);

                        // use the ack parameters to complete the session's data
                        tcpSession.sessionTCB.RCV.NXT = tcpHeader.seq+1;
                        tcpSession.sessionTCB.RCV.IRS = tcpHeader.seq;
                        tcpSession.sessionTCB.SND.UNA = tcpHeader.ackSeq;
                        tcpSession.sessionTCB.SND.WND = tcpHeader.window;
                        tcpSession.sessionTCB.RCV.WND = TcpFormat.TCP_MSS;

                        // now remove the SYN from the retransmit Q
                        // (so we don't retransmit it again)
                        TCPFSM.HandleTCPAck(tcpSession, ref tcpHeader);

                        if (tcpSession.sessionTCB.SND.UNA > tcpSession.sessionTCB.SND.ISS) {
                            // our syn has been acked.
                            TCPFSM.SendAck(tcpSession);

                            // change the state to established!
                            AttemptToEnterESTABLISHED(tcpSession, ref tcpHeader);
                            return NetStatus.Code.PROTOCOL_OK;
                        }
                    }
                    else {
                        // received a new SYN (overlap connection)
                        // (see SYN_RECVD for more details)

                        // Create a new object to track the new session
                        TcpSession client =
                            (TcpSession!) (tcpSession.Protocol.CreateSession());
                        client.passiveSession = tcpSession; // this is our "owner"
                        client.SetLocalEndPoint(tcpSession.LocalAddress,
                                                tcpSession.LocalPort);
                        client.InitializeServerSession(tcpHeader.seq,
                                                       tcpHeader.window);

                        // we have access to the IP header from the packet overlapped
                        // context (TCPModule put it there)
                        IPFormat.IPHeader ipHeader = packet.OverlapContext as IPFormat.IPHeader;
                        assert ipHeader!=null;
                        client.SetRemoteEndPoint(ipHeader.Source,
                                                 tcpHeader.sourcePort);

                        // Save ourselves work if we should reject the session right away
                        if (tcpSession.AcceptQueueIsFull()) {
                            TcpSegment reset = CreateResetSegment(client, true);
                            tcpSession.Protocol.OnProtocolSend(reset);
                            return NetStatus.Code.PROTOCOL_DROP_ERROR;
                        }

                        // New session starts at syn-rcv.  It immediately (from
                        //  OnEntry) sends a SYN-Ack and starts the connect timer.
                        client.ChangeState(SYN_RECVD);

                        return NetStatus.Code.PROTOCOL_OK;
                    }
                }
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }
        } // TCPStateSynSent   

        //----------------------------------------------------------------------------
        // This is the working mode state
        internal sealed class TCPStateEstab : TcpState
        {
            static TCPStateEstab! instance = new TCPStateEstab();
            static TCPStateEstab() {}

            internal static TCPStateEstab! Instance()
            {
                return instance;
            }

            // get state enum for eventing (tracing) and debugging.
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.Established;
            }

            override internal void OnStateEnter(TcpSession! tcpSession)
            {
                // When becoming Established, stop the connect timer
                // if there is one ticking.
                tcpSession.DestroyConnectTimer();

                // Wake up anyone waiting for the connection to complete
                tcpSession.setupCompleteEvent.Set();
            }

            override internal NetStatus OnPacketReceive(TcpSession! tcpSession,
                                                        NetPacket! packet,
                                                        object context)
            {
                assert context != null;
                TcpFormat.TcpHeader tcpHeader = (TcpFormat.TcpHeader)context;
                uint segmentSize = (uint)packet.Available;  // TCPModule already shrinked it for us

                NetStatus res = NetStatus.Code.PROTOCOL_DROP_ERROR;

                bool accept=IsSegmentAcceptable(tcpSession, ref tcpHeader, segmentSize);

                if (!accept) {
                    if (!TcpFormat.IsReset(ref tcpHeader)) {
                        // send an ACK and return
                        TCPFSM.SendAck(tcpSession);
                    }
                    return res;
                }

                if (TcpFormat.IsReset(ref tcpHeader)) {
                    // for simplicity, just close the connection.
                    HandleTerminateSession(tcpSession, null, TcpError.Reset);
                    return res;
                }

                // check syn
                if (TcpFormat.IsSync(ref tcpHeader)) {
                    // send a reset
                    HandleTerminateSession(tcpSession, CreateResetSegment(tcpSession, false), TcpError.Reset);
                    return res;
                }

                res = HandleTCPData(ref tcpHeader, packet, tcpSession);

                // our peer wants to end the relationship...
                if (TcpFormat.IsFIN(ref tcpHeader)) {
                    // RCV.NXT should reflect any data in this packet, but not the FIN.
                    // Advance over the FIN.
                    tcpSession.sessionTCB.RCV.NXT += 1;

                    // ack the FIN
                    SendAck(tcpSession);
                    ChangeState(tcpSession, CLOSE_WAIT);
                }

                return res;
            }
        }
        //----------------------------------------------------------------------------
        // CLOSE_WAIT is entered when we receive (and ACK) a FIN from the
        // remote side. There is no further data to receive, but we can
        // continue sending if we like.
        internal sealed class TCPCloseWait : TcpState
        {
            static TCPCloseWait! instance = new TCPCloseWait();
            static TCPCloseWait() {}

            internal static TCPCloseWait! Instance()
            {
                return instance;
            }

            // get state enum (debug)
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.CloseWait;
            }

            override internal void OnStateEnter(TcpSession! tcpSession)
            {
                base.OnStateEnter(tcpSession);

                // Signal that there is nothing more to read on this
                // connection
                tcpSession.ValidForRead = false;
            }

            override internal NetStatus OnPacketReceive(TcpSession! tcpSession,
                                                        NetPacket! packet,
                                                        object context)
            {
                assert context != null;
                TcpFormat.TcpHeader tcpHeader = (TcpFormat.TcpHeader)context;
                uint segmentSize = (uint)packet.Available;

                if (!IsSegmentAcceptable(tcpSession, ref tcpHeader, segmentSize)) {
                    if (!TcpFormat.IsReset(ref tcpHeader)) {
                        // send an ACK and return
                        TCPFSM.SendAck(tcpSession);
                    }

                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                if (TcpFormat.IsReset(ref tcpHeader) ||
                    TcpFormat.IsSync(ref tcpHeader) ||
                    (!TcpFormat.IsAck(ref tcpHeader)))
                {
                    // Abort
                    HandleTerminateSession(tcpSession, null, TcpError.Reset);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                TCPFSM.HandleTCPAck(tcpSession, ref tcpHeader);
                return NetStatus.Code.PROTOCOL_OK;
            }
        }

        //----------------------------------------------------------------------------
        // LAST_ACK is entered when we close our side of the duplex
        // connection and the remote site had sent us its FIN
        // previously. We send out our own FIN and just hang around
        // to make sure it was received properly before shutting down.
        //
        // CALLER SHOULD ARRANGE TO TRANSMIT THE FIN PACKET BEFORE
        // ENTERING THIS STATE!
        internal sealed class TCPLastAck : TcpState
        {
            static TCPLastAck! instance = new TCPLastAck();
            static TCPLastAck() {}

            internal static TCPLastAck! Instance()
            {
                return instance;
            }

            // get state enum for eventing (tracing) and debugging.
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.LastAck;
            }

            override internal void OnStateEnter(TcpSession! tcpSession)
            {
                base.OnStateEnter(tcpSession);

                // Flag that writing is now disallowed on this session
                tcpSession.ValidForWrite = false;
            }

            override internal NetStatus OnPacketReceive(TcpSession! tcbSession,
                                                        NetPacket! packet,
                                                        object context)
            {
                assert context != null;
                TcpFormat.TcpHeader tcpHeader = (TcpFormat.TcpHeader)context;
                uint segmentSize = (uint)packet.Available;  // TCPModule already shrinked it for us

                // RST is illegal at this point
                if (TcpFormat.IsReset(ref tcpHeader)) {
                    // for simplicity, just close the connection.
                    HandleTerminateSession(tcbSession, null, TcpError.Reset);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                // SYNC causes us to issue a RST and abort
                if (TcpFormat.IsSync(ref tcpHeader)) {
                    // send a reset
                    HandleTerminateSession(tcbSession,
                                           CreateResetSegment(tcbSession, false),
                                           TcpError.Reset);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                if (!IsSegmentAcceptable(tcbSession, ref tcpHeader, segmentSize)) {
                    // Just drop it
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                // Do ACK housekeeping
                if (TCPSeqLess(tcbSession.sessionTCB.SND.UNA, tcpHeader.ackSeq) &&
                    TCPSeqLEQ(tcpHeader.ackSeq, tcbSession.sessionTCB.SND.NXT))
                {
                    // This appears to be ACKing something we sent.
                    tcbSession.sessionTCB.SND.UNA = tcpHeader.ackSeq;

                    // remove the packet(s) from the retransmit queue
                    TCPFSM.HandleTCPAck(tcbSession, ref tcpHeader);
                }

                // Note the weirdness here; because we prepacketize
                // data, we don't want to compare to SND.NXT
                if (TCPSeqGEQ(tcbSession.sessionTCB.SND.UNA, tcbSession.sessionTCB.SND.NextSeq)) {
                    // The remote site has acknowledged everything we sent.
                    // We're done.
                    HandleTerminateSession(tcbSession, null, TcpError.Reset);
                }

                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }
        }

        //----------------------------------------------------------------------------
        // FIN_WAIT1 is entered when we close our side of the duplex
        // connection. We don't send any more data, but we continue to
        // receive data from the remote side.
        //
        // CALLER SHOULD ARRANGE TO SEND THE FIN PACKET BEFORE ENTERING
        // THIS STATE!
        internal sealed class TCPFINWait1 : TcpState
        {
            static TCPFINWait1! instance = new TCPFINWait1();
            static TCPFINWait1() {}

            internal static TCPFINWait1! Instance()
            {
                return instance;
            }

            // get state enum (debug)
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.FinWait1;
            }

            override internal void OnStateEnter(TcpSession! tcpSession)
            {
                base.OnStateEnter(tcpSession);

                // Flag that writing is now disallowed on this session
                tcpSession.ValidForWrite = false;
            }

            // leave the state
            override internal void OnStateLeave(TcpSession! tcpSession, TcpState newState)
            {
                assert newState != null;
                base.OnStateLeave(tcpSession, newState);
            }

            override internal NetStatus OnPacketReceive(TcpSession! tcpSession, NetPacket! packet, object context)
            {
                assert context != null;
                TcpFormat.TcpHeader tcpHeader = (TcpFormat.TcpHeader)context;
                uint segmentSize = (uint)packet.Available;  // TCPModule already shrinked it for us

                // RST is illegal at this point
                if (TcpFormat.IsReset(ref tcpHeader)) {
                    // for simplicity, just close the connection.
                    HandleTerminateSession(tcpSession, null, TcpError.ProtocolViolation);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                // SYNC causes us to issue a RST and abort
                if (TcpFormat.IsSync(ref tcpHeader)) {
                    // send a reset
                    HandleTerminateSession(tcpSession, CreateResetSegment(tcpSession, false), TcpError.ProtocolViolation);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                if (!IsSegmentAcceptable(tcpSession, ref tcpHeader, segmentSize)) {
                    if (!TcpFormat.IsReset(ref tcpHeader)) {
                        // send an ACK and return
                        TCPFSM.SendAck(tcpSession);
                    }

                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                // Chew on the payload...
                NetStatus retval = HandleTCPData(ref tcpHeader, packet, tcpSession);

                if (TCPSeqLEQ(tcpHeader.seq, tcpSession.sessionTCB.RCV.NXT) &&
                    (TcpFormat.IsFIN(ref tcpHeader)))
                {
                    // This is the remote side's FIN, and we have
                    // received all data preceding it, too!
                    // advance RCV.NXT over the FIN sequence
                    tcpSession.sessionTCB.RCV.NXT += 1;

                    // Note the weirdness here; because we
                    // prepacketize data, we don't want to test
                    // against SND.NXT
                    if (TCPSeqLess(tcpSession.sessionTCB.SND.UNA,
                                   tcpSession.sessionTCB.SND.NextSeq)) {
                        // ...but the remote side hasn't received
                        // everything we have said, yet.

                        // ack the FIN
                        SendAck(tcpSession);
                        ChangeState(tcpSession, CLOSING);
                    }
                    else {
                        // The remote side has heard everything we
                        // have to say. We're done.
                        // ACK the FIN and shut down
                        TcpSegment ackSeg = CreateAckSegment(tcpSession);
                        HandleTerminateSession(tcpSession, ackSeg, TcpError.Closed);
                    }
                }
                else {
                    // Note the weirdness here; because we
                    // prepacketize data, we do not want to test
                    // against SND.NXT, but rather SND.NextSeq.
                    if (TCPSeqGEQ(tcpSession.sessionTCB.SND.UNA,
                                  tcpSession.sessionTCB.SND.NextSeq)) {
                        // The remote side has ACKed everything we have
                        // said, but they haven't FINed themselves.
                        ChangeState(tcpSession, FIN_WAIT2);
                    }
                }

                return retval;
            }
        }

        //----------------------------------------------------------------------------
        // FIN_WAIT2 is entered when the other side has received our FIN, but has
        // more data to send. We wait for them to signal FIN as well.
        internal sealed class TCPFINWait2 : TcpState
        {
            static TCPFINWait2! instance = new TCPFINWait2();
            static TCPFINWait2() {}

            internal static TCPFINWait2! Instance()
            {
                return instance;
            }

            // get state enum (debug)
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.FinWait2;
            }

            // leave the state
            override internal void OnStateLeave(TcpSession! tcpSession, TcpState newState)
            {
                base.OnStateLeave(tcpSession, newState);
            }

            override internal NetStatus OnPacketReceive(TcpSession! tcpSession,
                                                        NetPacket! packet,
                                                        object context)
            {
                assert context != null;
                TcpFormat.TcpHeader tcpHeader = (TcpFormat.TcpHeader)context;
                uint segmentSize = (uint)packet.Available;  // TCPModule already shrinked it for us

                // RST is illegal at this point
                if (TcpFormat.IsReset(ref tcpHeader)) {
                    // for simplicity, just close the connection.
                    HandleTerminateSession(tcpSession,
                                           null,
                                           TcpError.ProtocolViolation);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                // SYNC causes us to issue a RST and abort
                if (TcpFormat.IsSync(ref tcpHeader)) {
                    // send a reset
                    HandleTerminateSession(tcpSession,
                                           CreateResetSegment(tcpSession, false),
                                           TcpError.ProtocolViolation);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                if (!IsSegmentAcceptable(tcpSession, ref tcpHeader, segmentSize)) {
                    if (!TcpFormat.IsReset(ref tcpHeader)) {
                        // send an ACK and return
                        TCPFSM.SendAck(tcpSession);
                    }

                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                // Chew on the payload...
                NetStatus retval = HandleTCPData(ref tcpHeader, packet, tcpSession);

                // Only check for FIN if we have previously received
                // all data.
                if (TCPSeqLEQ(tcpHeader.seq, tcpSession.sessionTCB.RCV.NXT) &&
                    (TcpFormat.IsFIN(ref tcpHeader)))
                {
                    // RCV.NXT should reflect the data in this packet, but not
                    // the FIN. Advance over the FIN...
                    tcpSession.sessionTCB.RCV.NXT += 1;

                    // ack the FIN and shut down
                    TcpSegment ackSeg = CreateAckSegment(tcpSession);
                    HandleTerminateSession(tcpSession, ackSeg, TcpError.Closed);
                }

                return retval;
            }
        }

        //----------------------------------------------------------------------------
        // CLOSING is entered when both sides have sent a FIN, but we're not sure
        // the other side has received all our data yet. We hang around processing
        // ACKs until we're sure the other side has heard everything we have to say.
        internal sealed class TCPClosing : TcpState
        {
            static TCPClosing! instance = new TCPClosing();
            static TCPClosing() {}

            internal static TCPClosing! Instance()
            {
                return instance;
            }

            // get state enum (debug)
            override internal TcpStateEnum GetStateEnum()
            {
                return TcpStateEnum.Closing;
            }

            override internal void OnStateEnter(TcpSession! tcpSession)
            {
                base.OnStateEnter(tcpSession);

                // Signal that there's nothing more to read on this session
                tcpSession.ValidForRead = false;
            }

            // leave the state
            override internal void OnStateLeave(TcpSession! tcpSession, TcpState newState)
            {
                assert newState != null;
                base.OnStateLeave(tcpSession, newState);
            }

            override internal NetStatus OnPacketReceive(TcpSession! tcpSession,
                                                        NetPacket! packet,
                                                        object context)
            {
                assert context != null;
                TcpFormat.TcpHeader tcpHeader = (TcpFormat.TcpHeader)context;
                uint segmentSize = (uint)packet.Available;  // TCPModule already shrinked it for us

                // RST is illegal at this point
                if (TcpFormat.IsReset(ref tcpHeader)) {
                    // for simplicity, just close the connection.
                    HandleTerminateSession(tcpSession, null, TcpError.ProtocolViolation);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                // SYNC causes us to issue a RST and abort
                if (TcpFormat.IsSync(ref tcpHeader)) {
                    // send a reset
                    HandleTerminateSession(tcpSession,
                                           CreateResetSegment(tcpSession, false),
                                           TcpError.ProtocolViolation);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                if (!IsSegmentAcceptable(tcpSession, ref tcpHeader, segmentSize)) {
                    // Just drop it
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }

                // Do ACK housekeeping
                if (TCPSeqLess(tcpSession.sessionTCB.SND.UNA, tcpHeader.ackSeq) &&
                    TCPSeqLEQ(tcpHeader.ackSeq, tcpSession.sessionTCB.SND.NXT))
                {
                    // This appears to be ACKing something we sent.
                    tcpSession.sessionTCB.SND.UNA = tcpHeader.ackSeq;

                    // remove the packet(s) from the retransmit queue
                    TCPFSM.HandleTCPAck(tcpSession, ref tcpHeader);
                }

                // Note the weirdness here; because we
                // prepacketize data, we don't want to compare against
                // SND.NXT
                if (TCPSeqGEQ(tcpSession.sessionTCB.SND.UNA, tcpSession.sessionTCB.SND.NextSeq)) {
                    // The remote side has now heard everything we said.
                    HandleTerminateSession(tcpSession, null, TcpError.Closed);
                }

                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }
        }

        //----------------------------------------------------------------------------
        // Create an ACK for data we have received to date
        internal static TcpSegment! CreateAckSegment(TcpSession! tcpSession)
        {
            byte[] ackBuffer = new byte[EthernetFormat.Size+IPFormat.Size+TcpFormat.Size];

            TcpFormat.WriteTcpSegment(
                ackBuffer, tcpSession.LocalPort, tcpSession.RemotePort,
                tcpSession.sessionTCB.RCV.NXT, tcpSession.sessionTCB.SND.NextSeq,
                TcpFormat.TCP_MSS, tcpSession.LocalAddress,
                tcpSession.RemoteAddress, 0,
                true, false, false, false, false);

            return new TcpSegment(ackBuffer, tcpSession,
                                  tcpSession.sessionTCB.SND.NextSeq, true);
        }

        // sends an ack
        internal static bool SendAck(TcpSession! tcpSession)
        {
            TcpSegment ackSeg = CreateAckSegment(tcpSession);

            // put it on this session outgoing queue
            return tcpSession.PutPacket(tcpSession.outQueue, ackSeg, false);
        }

        // Sends a FIN
        internal static bool SendFin(TcpSession! tcpSession, bool canBlock)
        {
            byte[] finBuffer = new byte[EthernetFormat.Size+IPFormat.Size+TcpFormat.Size];

            TcpFormat.WriteTcpSegment(
                finBuffer, tcpSession.LocalPort, tcpSession.RemotePort, tcpSession.sessionTCB.RCV.NXT,
                tcpSession.sessionTCB.SND.NextSeq, TcpFormat.TCP_MSS, tcpSession.LocalAddress, tcpSession.RemoteAddress, 0,
                true, false, false, true, false);

            // ok, we have a ready segment.
            TcpSegment syn = new TcpSegment(finBuffer, tcpSession, tcpSession.sessionTCB.SND.NextSeq, true);

            bool retVal = tcpSession.PutPacket(tcpSession.outQueue, syn, canBlock);

            // Only advance the segment counter if we successfully queued the
            // outbound packet
            if (retVal) {
                tcpSession.sessionTCB.SND.NextSeq++;
            }

            return retVal;
        }

        // sends a syn ack packet
        internal static bool SendSYNAck(TcpSession! tcpSession)
        {
            byte[] synackBuffer = new byte[EthernetFormat.Size+IPFormat.Size+TcpFormat.Size];

            TcpFormat.WriteTcpSegment(synackBuffer, tcpSession.LocalPort, tcpSession.RemotePort,
                                      tcpSession.sessionTCB.RCV.NXT,
                                      tcpSession.sessionTCB.SND.ISS,
                                      (ushort)tcpSession.sessionTCB.SND.WND,
                                      tcpSession.LocalAddress, tcpSession.RemoteAddress,
                                      0, true, true, false, false, false);

            // ok, we have a ready segment.
            // (SYN is regular segment)
            TcpSegment syn = new TcpSegment(synackBuffer, tcpSession, tcpSession.sessionTCB.SND.ISS, true);

            // put it on this session's outgoing queue
            return tcpSession.PutPacket(tcpSession.outQueue, syn, false);
        }

        // sends a syn packet, with MSS options
        internal static bool SendSYN(TcpSession! tcpSession, ushort MSS)
        {
            byte[] synBuffer = new byte[EthernetFormat.Size+IPFormat.Size+TcpFormat.Size+4];

            // setup the session
            tcpSession.sessionTCB.SND.ISS=(uint)DateTime.UtcNow.Ticks;
            tcpSession.sessionTCB.SND.UNA=tcpSession.sessionTCB.SND.ISS;
            tcpSession.sessionTCB.SND.NXT=tcpSession.sessionTCB.SND.ISS+1; // next packet sequence
            tcpSession.sessionTCB.SND.NextSeq = tcpSession.sessionTCB.SND.NXT;
            tcpSession.sessionTCB.SND.WND=TcpFormat.TCP_MSS;

            // we must first write the data...
            byte[] options=new byte[] {2, 4, ((byte)(MSS>>8)), (byte)MSS};
            Array.Copy(options, 0, synBuffer, EthernetFormat.Size+IPFormat.Size+TcpFormat.Size, 4);

            // now create the segment+checksum
            TcpFormat.WriteTcpSegment(
                synBuffer, tcpSession.LocalPort, tcpSession.RemotePort, 0,
                tcpSession.sessionTCB.SND.ISS, MSS, tcpSession.LocalAddress, tcpSession.RemoteAddress, 4,
                false, true, false, false, true);

            // ok, we have a ready segment.
            // (SYN is regular segment)
            TcpSegment syn = new TcpSegment(synBuffer, tcpSession, tcpSession.sessionTCB.SND.ISS, false);

            // put it on this session outgoing queue
            return tcpSession.PutPacket(tcpSession.outQueue, syn, false);
        }

        // send a TCP reset
        internal static bool SendReset(TcpSession! tcpSession, bool isAck)
        {
            // we won't retransmit it (it is like an Ack)
            TcpSegment syn = CreateResetSegment(tcpSession, true);

            // put it on this session outgoing queue
            return tcpSession.PutPacket(tcpSession.outQueue, syn, false);
        }

        // send a TCP reset
        internal static TcpSegment! CreateResetSegment(TcpSession! tcpSession, bool isAck)
        {
            byte[] rstBuffer = new byte[EthernetFormat.Size+IPFormat.Size+TcpFormat.Size];

            // NOTE: use SND.NXT as the sequence number here instead of nextSeq,
            // otherwise the sequence number may be far ahead (if there's lots of queued
            // data) and the receiving host may ignore it as outside its window.
            TcpFormat.WriteTcpSegment(
                rstBuffer, tcpSession.LocalPort, tcpSession.RemotePort, tcpSession.sessionTCB.RCV.NXT,
                tcpSession.sessionTCB.SND.NXT, TcpFormat.TCP_MSS, tcpSession.LocalAddress,
                tcpSession.RemoteAddress, 0, isAck, false, true, false, false);

            // we won't retransmit it
            TcpSegment syn = new TcpSegment(rstBuffer, tcpSession, tcpSession.sessionTCB.SND.NXT, true);
            return syn;
        }

        // Handle received TCP data
        // Returns the appropriate NetStatus.Code
        internal static NetStatus HandleTCPData(ref TcpFormat.TcpHeader tcpHeader,
                                                NetPacket! packet, TcpSession! tcpSession)
        {
            uint segmentSize = (uint)packet.Available;  // TCPModule already shrinked it for us

            // TBC: We assume the segment start with
            // the RCV.NXT !!! (otherwise we can buffer them)
            if (TCPSeqGreater(tcpHeader.seq, tcpSession.sessionTCB.RCV.NXT)) {
                // we missed one or few, send ack again
                TCPFSM.SendAck(tcpSession);
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }

            if (!TcpFormat.IsAck(ref tcpHeader)) {
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }

            // First, deal with the window advertised in this packet.
            tcpSession.sessionTCB.SND.WND = tcpHeader.window;
            tcpSession.HandleWindowUpdate();

            // ack is set and it is relevant (ack something we sent)
            if (TCPSeqLess(tcpSession.sessionTCB.SND.UNA, tcpHeader.ackSeq) &&
                TCPSeqLEQ(tcpHeader.ackSeq, tcpSession.sessionTCB.SND.NXT))
            {
                tcpSession.sessionTCB.SND.UNA = tcpHeader.ackSeq;

                // remove the packet(s) from the retransmit queue
                TCPFSM.HandleTCPAck(tcpSession, ref tcpHeader);
            }
            else if (tcpSession.sessionTCB.SND.UNA > tcpHeader.ackSeq) {
                // a duplicate ack
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }
            else if (TCPSeqGreater(tcpHeader.ackSeq, tcpSession.sessionTCB.SND.NXT)) {
                // ack for future data..
                TCPFSM.SendAck(tcpSession);
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }

            // check URG bit
            if (TcpFormat.IsUrg(ref tcpHeader)) {
                // TBC
            }

            // check PUSH bit
            if (TcpFormat.IsPush(ref tcpHeader)) {
                // TBC
            }

            // at last, process the segment data!!!
            // at the end send an ACK (TBC: change to accumulate acks)
            if (segmentSize > 0) {
                // put the data in the session's inQ
                if (tcpSession.PutPacket(tcpSession.inQueue, packet, false)) {
                    tcpSession.sessionTCB.RCV.NXT+=segmentSize; // we expect the next segment seq
                    tcpSession.sessionTCB.RCV.WND=TcpFormat.TCP_MSS; // TBC: change according to buffer

                    // send our ack if we ack data
                    SendAck(tcpSession);

                    // don't release the packet
                    return NetStatus.Code.PROTOCOL_PROCESSING;
                }
                else {
                    // packet was dropped...
                    // send our ack if we ack data
                    SendAck(tcpSession);
                    return NetStatus.Code.PROTOCOL_DROP_ERROR;
                }
            }
            else {
                // Payload was empty...
                return NetStatus.Code.PROTOCOL_DROP_ERROR;
            }
        }

        // handle a TCP received ack
        // the ack is already checked for validity (by the actual state)
        internal static void HandleTCPAck(TcpSession! tcpSession,
                                          ref TcpFormat.TcpHeader tcpHdr)
        {
            tcpSession.ACKThrough(tcpHdr.ackSeq);
        }

        // check if we can accept the segment
        internal static bool IsSegmentAcceptable(TcpSession! tcpSession,
                                                 ref TcpFormat.TcpHeader tcpHeader,
                                                 uint segmentSize)
        {
            bool accept=false;

            // first check sequence number
            if ((segmentSize == 0) && (tcpSession.sessionTCB.RCV.WND == 0)) {
                accept = (tcpHeader.seq == tcpSession.sessionTCB.RCV.NXT);
            }
            else if ((segmentSize == 0) && (tcpSession.sessionTCB.RCV.WND > 0)) {
                accept=(TCPSeqGEQ(tcpHeader.seq, tcpSession.sessionTCB.RCV.NXT) &&
                        TCPSeqLess(tcpHeader.seq, tcpSession.sessionTCB.RCV.NXT+tcpSession.sessionTCB.RCV.WND));
            }
            else if ((segmentSize > 0) && (tcpSession.sessionTCB.RCV.WND > 0)) {
                accept=(TCPSeqGEQ(tcpHeader.seq, tcpSession.sessionTCB.RCV.NXT) &&
                        TCPSeqLess(tcpHeader.seq, tcpSession.sessionTCB.RCV.NXT+tcpSession.sessionTCB.RCV.WND));

                accept = accept || (TCPSeqLEQ(tcpSession.sessionTCB.RCV.NXT, tcpHeader.seq+segmentSize-1) &&
                                    TCPSeqLess(tcpHeader.seq +segmentSize - 1,
                                               tcpSession.sessionTCB.RCV.NXT + tcpSession.sessionTCB.RCV.WND));
            }

            return accept;
        }

        private static void AttemptToEnterESTABLISHED(TcpSession! tcpSession,
                                                      ref TcpFormat.TcpHeader tcpHeader)
        {
            TcpSession passiveOwner = tcpSession.passiveSession;

            if (passiveOwner != null) {
                bool success = passiveOwner.AddAcceptedSession(tcpSession);

                if (!success) {
                    // Oops; while this connection was being established
                    // we ran out of room in the accept queue. Abort
                    // the connection!
                    HandleTerminateSession(tcpSession,
                                           CreateResetSegment(tcpSession, false),
                                           TcpError.ResourcesExhausted);
                    return;
                }
            }

            tcpSession.ChangeState(ESTABLISHED);
        }

        // this method terminated the given session
        // if nextSegment is not null than it is sent before final
        // removal.
        internal static void HandleTerminateSession(TcpSession! tcpSession,
                                                    TcpSegment nextSegment,
                                                    TcpError connectError)
        {
            tcpSession.StopPersistTimer();

            // 1. first clear the retransmit queue
            // 2. make the session not valid for users!
            // 3. release any user waiting for read/write on the session
            // 4. clear the out/in queues
            // 5. remove the session from TCP if it is no longer needed
            //    (when it considered to be closed)
            tcpSession.FlushRetransmissions();

            // some user may wait on the q to write/read data
            // we will release them by trigger the monitors.
            // they will fail since Valid is false and they are users.
            // only TCP can still use this session.
            lock (tcpSession.outQueue.SyncRoot) {
                // from now on, every user thread will
                // fail to read/write data
                tcpSession.ValidForRead = false;
                tcpSession.ValidForWrite = false;

                tcpSession.DrainQueue(tcpSession.outQueue);
                if (nextSegment != null)
                    tcpSession.outQueue.Add(nextSegment);

                // Don't forget these!
                Monitor.PulseAll(tcpSession.outQueue.SyncRoot);
                Core.Instance().SignalOutboundPackets();
            }

            lock (tcpSession.inQueue.SyncRoot) {
                // Pulse anyone waiting to read data so they can notice
                // they are unlikely to succeed, but don't clear the
                // queue; if there is data on it, we may want to drain
                // it, still.
                Monitor.PulseAll(tcpSession.inQueue.SyncRoot);
            }

            if (nextSegment == null) {
                IProtocol tcpProtocol = tcpSession.Protocol;
                Core.Instance().DeregisterSession(tcpProtocol, tcpSession);
            }

            // change the state to close
            tcpSession.ChangeState(TCPFSM.CLOSED);

            // Signal anyone who was waiting for this session to begin or end
            tcpSession.connectError = connectError;
            tcpSession.setupCompleteEvent.Set();

            // NOTE: If we are transmitting a last-gasp packet,
            // don't signal the session as closed just yet; wait for the packet
            // to actually get transmitted.
            if (nextSegment == null) {
                tcpSession.closedEvent.Set();
            }
        }
    }
}
