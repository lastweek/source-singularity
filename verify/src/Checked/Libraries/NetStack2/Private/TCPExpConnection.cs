////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TcpConnectionExpThread.sg
//  Author: maiken
//  Note:   Provider-side helper for the IP Channel Contract
//

using System;
using System.Net.IP;
using System.Threading;

using Microsoft.SingSharp;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity;

using Microsoft.Singularity.NetStack;

using TcpError = NetStack.Contracts.TcpError;

//add send buffer and receive buffer for app to use.
//append to buff then let TCP send as much as possible.

namespace Microsoft.Singularity.NetStack2.Channels.Private
{
    public class TcpConnectionContract
    {
        private TCP tcpSession;
        private State state = State.Start;

        public enum State
        {
            Start,
            ReadyState,
            //BindResult,
            Bound,
            //ConnectResult,
            //ConfirmAcceptResult,
            //ListenResult,
            Listening,
            Connected,
            //ReadResult,
            //ReadVResult,
            //PollReadResult,
            //PollReadVResult,
            //WriteResult,
            //ReceiveOnly,
            //ROReadResult,
            //ROPollReadResult,
            //SendOnly,
            //SOWriteResult,
            Zombie,
            Closed,
        }

        public bool InState(State s)
        {
            return s == state;
        }

        //
        // ======================= Start state =======================
        //
        public void Connect(IPv4 dstIP, ushort dstPort)
        {
            TcpError tcpError;
            bool success = tcpSession.Connect(dstIP, dstPort, out tcpError);

            if (!success) {
                throw new Exception("Connect");
            }
            state = State.Connected;
        }

        public void BindLocalEndPoint(IPv4 localIP, ushort localPort)
        {
            bool success = tcpSession.Bind(localIP, localPort);

            if (!success) {
                throw new Exception("BindLocalEndPoint");
            }
            state = State.Bound;
        }

        //
        // ======================= Bound state =======================
        //

        public void Listen(int backlog)
        {
            bool success = tcpSession.Listen(backlog);

            if (!success) {
                throw new Exception("Listen");
            }
            state = State.Listening;
        }

        //
        // ======================= Listening state =======================
        //

        public bool IsSessionAvailable()
        {
            return tcpSession.GetNumWaitingListenSessions() > 0;
        }

        //public Accept(TcpConnectionContract/*.Exp*/:PreConnected newEP)
        //[edn] remote channels hack
        public void Accept(TcpConnectionContract/*.Exp*/ newEP)
        {
            TCP newSession = tcpSession.Accept();
            VTable.Assert(newSession != null);
            state = State.Connected;
        }

        //
        // ======================= Connected state =======================
        //

        public Bytes Read()
        {
            if (tcpSession.CurrentState < TcpState.ESTABLISHED) {
                state = State.Closed;
                return null; // connection closed
            }

            Bytes data = tcpSession.Read();

            if (data == null) {
                if (tcpSession.CurrentState != TcpState.ESTABLISHED) {
                    state = State.Closed;
                    return null; // connection closed
                }
                else {
                    // Must be in the ROReadResult state. Here, there is
                    // no ConnectionClosed message.
                    state = State.Zombie;
                    return null; // no more data -> Zombie
                }
            }
            else {
                if (tcpSession.AckNow == true) {
                    tcpSession.SendPacket(TcpFlags.ACK, false);
                }
                return data;
            }
        }

        public Bytes[] ReadV()
        {
            if (tcpSession.CurrentState < TcpState.ESTABLISHED) {
                state = State.Closed;
                return null; // connection closed
            }

            Bytes[] data = tcpSession.ReadV();

            if (data == null) {
                if (tcpSession.CurrentState != TcpState.ESTABLISHED) {
                    state = State.Closed;
                    return null; // connection closed
                }
                else {
                    // Must be in the ROReadResult state. Here, there is
                    // no ConnectionClosed message.
                    state = State.Zombie;
                    return null; // no more data -> Zombie
                }
            }
            else {
                if (tcpSession.AckNow == true) {
                    tcpSession.SendPacket(TcpFlags.ACK, false);
                }
                return data;
            }
        }

        public Bytes PollRead(int timeout)
        {

            if (tcpSession.CurrentState < TcpState.ESTABLISHED) {
                state = State.Closed;
                return null; // connection closed
            }

            Bytes data = tcpSession.PollRead(TimeSpan.FromMilliseconds(timeout));

            if (data == null) {
                if (tcpSession.CurrentState < TcpState.ESTABLISHED) {
                    state = State.Closed;
                    return null; // connection closed
                }
                return null; // no more data
            }
            else {
                if (tcpSession.AckNow == true) {
                    tcpSession.SendPacket(TcpFlags.ACK, false);
                }
                return data;
            }
        }

        public Bytes[] PollReadV(int timeout)
        {

            if (tcpSession.CurrentState < TcpState.ESTABLISHED) {
                state = State.Closed;
                return null; // connection closed
            }

            Bytes[] data = tcpSession.PollReadV(TimeSpan.FromMilliseconds(timeout));

            if (data == null) {
                if (tcpSession.CurrentState < TcpState.ESTABLISHED) {
                    state = State.Closed;
                    return null; // connection closed
                }
                return null; // no more data
            }
            else {
                if (tcpSession.AckNow == true) {
                    tcpSession.SendPacket(TcpFlags.ACK, false);
                }
                return data;
            }
        }


        public void Write(Bytes data)
        {
            if (tcpSession.CurrentState < TcpState.ESTABLISHED) {
                state = State.Closed;
                DebugStub.Print("Connection unexpectedly closed\n");
                throw new Exception("Write: CantSend");
            }

            int bytesToWrite = data.Length;
            int written = tcpSession.Send(data);

            if (written == -1) {
                state = State.Closed;
                // A -1 return value indicates the connection has been closed
                // underneath us while we were trying to write.
                throw new Exception("WriteData: CantSend");
            }
            else if (written != bytesToWrite) {
                // This is unexpected; the current implementation always
                // blocks and writes as much data as is provided.
                throw new Exception("Unexpected partial write in TcpSession.WriteData");
            }
        }


        public bool IsDataAvailable()
        {
            return tcpSession.IsDataAvailable();
        }


        public void DoneSending()
        {
            tcpSession.Close();
            state = State.Closed;
        }


        public void DoneReceiving()
        {
            tcpSession.Close();
            state = State.Closed;
        }


        public void Abort()
        {
            //                        tcpSession.Abort();
        }


        //
        // ======================= Messages from multiple states =======================
        //

        public IPv4 GetLocalAddress()
        {
            return tcpSession.LocalAddress;
        }


        public ushort GetLocalPort()
        {
            return tcpSession.LocalPort;
        }


        public IPv4 GetRemoteAddress()
        {
            return tcpSession.RemoteAddress;
        }


        public ushort GetRemotePort()
        {
            return tcpSession.RemotePort;
        }


        public void Close()
        {
            tcpSession.Close();
            state = State.Closed;
        }


        public long RequestTimeWaiting()
        {
            return tcpSession.TimeWaiting();
        }


        public TcpConnectionContract()
        {
            tcpSession = new TCP();
            state = State.ReadyState;
        }

        private TcpConnectionContract(TCP newSession)
        {
            tcpSession = newSession;
            state = State.ReadyState;
        }
    }
}

