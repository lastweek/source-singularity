///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   UdpSocket.cs
//
//  Note:
//

using System;
using Microsoft.SingSharp;
using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using NetStack.Contracts;
using Microsoft.Singularity.V1.Services;
using Microsoft.Contracts;

namespace System.Net.Sockets
{
    internal class UdpSocket : InternalSocket
    {
        private const int BAD_SOCKET_STATE_ERR = (int)SocketErrors.WSAEOPNOTSUPP;

        private TRef<UdpConnectionContract.Imp:ReadyState> m_Conn;

        private IPEndPoint m_LocalEndPoint;
        private IPEndPoint m_RemoteEndPoint;

        // ================ Private Methods ================

        private void Initialize([Claims]UdpConnectionContract.Imp:ReadyState! conn)
        {
            m_Conn = new TRef<UdpConnectionContract.Imp:ReadyState>(conn);
        }

        private static void ValidateBufferOffsets(byte[] buffer,
                                                  int    offset,
                                                  int    size)
        {
            if (buffer == null) {
                throw new ArgumentNullException("buffer");
            }

            if (offset < 0 || offset > buffer.Length) {
                throw new ArgumentOutOfRangeException("offset");
            }

            if (size < 0 || size > buffer.Length - offset) {
                throw new ArgumentOutOfRangeException("size");
            }
        }

        // ================ Internal Methods ================

        [NotDelayed]
        internal UdpSocket()
        {
            // Connect to the Udp module
            UdpContract.Imp! impConn;
            UdpContract.Exp! expConn;
            UdpContract.NewChannel(out impConn, out expConn);
            DirectoryServiceContract.Imp epNS = DirectoryService.NewClientEndpoint();
            try {
                epNS.SendBind(Bitter.FromString2(UdpContract.ModuleName), expConn);
                switch receive {
                    case epNS.NakBind(ServiceContract.Exp:Start rejectedEP, error) :
                        // failure
                        if (rejectedEP != null) {
                            delete rejectedEP;
                        }
                        throw new SocketException(SocketErrors.WSASYSNOTREADY);
                        break;

                    case epNS.AckBind() :
                        impConn.RecvReady();
                        // success
                        break;
                    case epNS.ChannelClosed():
                        Tracing.Log(Tracing.Debug," NS ep closed");
                        break;
                    case unsatisfiable:
                        DebugService.Break();
                        break;
                }
            }
            finally {
                delete epNS;
            }

            try {
                // Create a new Udp connection
                UdpConnectionContract.Exp! udpExpConn;
                UdpConnectionContract.Imp! udpImpConn;

                UdpConnectionContract.NewChannel(out udpImpConn, out udpExpConn);
                impConn.SendCreateUdpSession(udpExpConn);
                impConn.RecvAck();

                // Move the new connection to the ReadyState
                udpImpConn.RecvReady();
                Initialize(udpImpConn);
            }
            finally {
                delete impConn;
            }
        }

        internal override InternalSocket Accept()
        {
            throw new SocketException(SocketErrors.WSAEOPNOTSUPP);
            return null;
        }

        internal override void Bind(EndPoint localEndPoint)
        {
            if (localEndPoint == null) {
                throw new ArgumentNullException("localEndPoint");
            }

            IPEndPoint ep = localEndPoint as IPEndPoint;

            if (ep == null) {
                // Illegal argument
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            // Make sure we're in the ReadyState
            UdpConnectionContract.Imp conn = m_Conn.Acquire();

            try {
                if (!conn.InState(UdpConnectionContract.ReadyState.Value)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                conn.SendBindLocalEndPoint((uint) ep.Address.m_addr,
                                           unchecked((ushort) ep.Port));
                switch receive {
                    case conn.OK() :
                        // Make a copy of the argument data
                        m_LocalEndPoint = new IPEndPoint(ep.Address, ep.Port);
                        break;
                    case conn.InvalidEndPoint(uint addr, ushort port) :
                        throw new SocketException(SocketErrors.WSAEADDRNOTAVAIL);
                        break;
                }
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override void Close()
        {
            UdpConnectionContract.Imp conn = m_Conn.Acquire();

            try {
                if (!conn.InState(UdpConnectionContract.Closed.Value)) {
                    conn.SendClose();
                }
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override void Connect(EndPoint remoteEndPoint)
        {
            if (remoteEndPoint == null) {
                throw new ArgumentNullException("remoteEP");
            }

            IPEndPoint ep = remoteEndPoint as IPEndPoint;

            if (ep == null) {
                // Illegal argument
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            UdpConnectionContract.Imp conn = m_Conn.Acquire();

            if (!conn.InState(UdpConnectionContract.ReadyState.Value) &&
                ! conn.InState(UdpConnectionContract.LocallyBound.Value))
            {
                // Need to be in the start state to issue a Connect
                throw new SocketException(BAD_SOCKET_STATE_ERR);
            }

            try {
                uint   localIP   = 0;
                ushort localPort = 0;

                if (m_LocalEndPoint != null) {
                    if (m_LocalEndPoint.Address != IPAddress.Any) {
                        localIP = (uint)m_LocalEndPoint.Address.m_addr;
                    }

                    if (m_LocalEndPoint.Port != 0) {
                        localPort = unchecked((ushort)m_LocalEndPoint.Port);
                    }
                }

                if ((localIP != 0) && (localPort != 0)) {
                    conn.SendConnect(localIP, localPort,
                                     (uint)ep.Address.m_addr,
                                     unchecked((ushort)ep.Port));
                }
                else {
                    conn.SendConnectWithAnyLocalEndPoint(
                        (uint)ep.Address.m_addr,
                        unchecked((ushort)ep.Port));
                }

                switch receive {
                    case conn.OK() :
                        // Success
                        m_RemoteEndPoint = ep;
                        break;
                    case conn.InvalidEndPoint(uint addr, ushort port) :
                        // NOTE: could probably stand to retrieve and
                        // return a better error code here
                        throw new SocketException(SocketErrors.SocketError);
                        break;
                }
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override void Dispose()
        {
            UdpConnectionContract.Imp conn = m_Conn.Acquire();
            delete conn;
            // Leak our TRef!
        }

        internal override void Listen(int backlog)
        {
            throw new SocketException(SocketErrors.WSAEOPNOTSUPP);
        }

        private bool PollSelectRead(UdpConnectionContract.Imp! conn,
                                    int                        millis)
        {
            bool result = false;
            conn.SendPollSelectRead(millis);
            conn.RecvPollSelectResult(out result);
            return result;
        }

        private bool PollSelectWrite(UdpConnectionContract.Imp! conn,
                                     int                        millis)
        {
            bool result = false;
            conn.SendPollSelectWrite(millis);
            conn.RecvPollSelectResult(out result);
            return result;
        }

        internal override bool Poll(int microSeconds, SelectMode mode)
        {
            int millis = 0;
            if (microSeconds < 0) {
                millis = Int32.MaxValue;
            }
            else {
                millis = microSeconds / 1000;
            }

            UdpConnectionContract.Imp conn = m_Conn.Acquire();

            try {
                if (conn.InState(UdpConnectionContract.Closed.Value)) {
                    throw new ObjectDisposedException("socket");
                }

                switch (mode) {
                    case SelectMode.SelectRead:
                        return PollSelectRead(conn, millis);
                        break;
                    case SelectMode.SelectWrite:
                        return PollSelectWrite(conn, millis);
                        break;
                    case SelectMode.SelectError:
                        return false;
                        // We don't support any of the requisite operations
                        break;
                    default:
                        throw new NotSupportedException();
                }
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override int ReceiveFrom(byte[]!      buffer,
                                          int          offset,
                                          int          size,
                                          SocketFlags  socketFlags,
                                          ref EndPoint remoteEP)
        {
            ValidateBufferOffsets(buffer, offset, size);
            if (socketFlags != SocketFlags.None) {
                // Invalid flags for this operation
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            UdpConnectionContract.Imp conn = m_Conn.Acquire();

            try {
                if (conn.InState(UdpConnectionContract.Closed.Value)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                conn.SendRead();
                switch receive {
                    case conn.Data(uint addr, ushort port, byte[]! in ExHeap rdata) :
                    {
                        remoteEP = new IPEndPoint(new IPAddress(addr), port);
                        int amount = Math.Min(rdata.Length, size);
                        Bitter.ToByteArray(rdata, 0, amount, buffer, offset);
                        delete rdata;
                        return amount;
                    }
                    break;
                }
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override int Receive(byte[]!     buffer,
                                      int         offset,
                                      int         size,
                                      SocketFlags socketFlags)
        {
            EndPoint dummy = null;
            return ReceiveFrom(buffer, offset, size, socketFlags, ref dummy);
        }

        internal override int Send([Claims] byte[]! in ExHeap data,
                                   SocketFlags socketFlags)
        {
            int byteCount = data.Length;

            if (socketFlags != SocketFlags.None) {
                // Invalid flags for this operation
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            UdpConnectionContract.Imp conn = m_Conn.Acquire();

            try {
                if (!conn.InState(UdpConnectionContract.Connected.Value)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                conn.SendWrite(data); // Give away data

                switch receive {
                    case conn.OK() :
                        // Success
                        return byteCount;
                        break;

                    case conn.DataTooLarge() :
                        // uh oh
                        throw new SocketException(SocketErrors.WSAEMSGSIZE);
                    break;
                }
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override int Send(byte[]!    buffer,
                                   int         offset,
                                   int         size,
                                   SocketFlags socketFlags)
        {
            ValidateBufferOffsets(buffer, offset, size);
            byte[] in ExHeap dataToWrite = Bitter.FromByteArray(buffer, offset, size);
            return Send(dataToWrite, socketFlags);
        }

        internal override int SendTo(byte[]!     buffer,
                                     int         offset,
                                     int         size,
                                     SocketFlags socketFlags,
                                     EndPoint    remoteEP)
        {
            ValidateBufferOffsets(buffer, offset, size);

            if (socketFlags != SocketFlags.None) {
                // Invalid flags for this operation
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            IPEndPoint ep = remoteEP as IPEndPoint;
            if (ep == null) {
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            UdpConnectionContract.Imp conn = m_Conn.Acquire();

            try {
                if (conn.InState(UdpConnectionContract.Closed.Value)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                // Copy the data to write into an ExHeap vector and send it
                byte[] in ExHeap dataToWrite = Bitter.FromByteArray(buffer, offset, size);

                conn.SendWriteTo((uint)ep.Address.m_addr,
                                 unchecked((ushort)ep.Port),
                                 dataToWrite);
                // no longer own dataToWrite!

                switch receive {
                    case conn.OK() :
                        // Success
                        return size;
                        break;

                    case conn.DataTooLarge() :
                        // uh oh
                        throw new SocketException(SocketErrors.WSAEMSGSIZE);
                    break;
                }
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override void Shutdown(SocketShutdown how)
        {
            throw new SocketException(SocketErrors.WSAEOPNOTSUPP);
        }

        internal override int Available { get { return 0; /* XXX */ } }

        internal override EndPoint LocalEndPoint
        {
            get { return m_LocalEndPoint; }
        }

        internal override EndPoint RemoteEndPoint
        {
            get { return m_RemoteEndPoint; }
        }

        internal override bool Blocking
        {
            get {
                return true;
            }
            set {
                if (value != true) {
                    // TODO: non-blocking mode!
                    throw new NotSupportedException();
                }
            }
        }

        internal override bool Connected
        {
            get {
                UdpConnectionContract.Imp conn = m_Conn.Acquire();
                try {
                    return conn.InState(UdpConnectionContract.Connected.Value);
                }
                catch {
                    return false;
                }
                finally {
                    m_Conn.Release(conn);
                }
            }
        }

        internal override AddressFamily AddressFamily
        {
            get { return AddressFamily.InterNetwork; }
        }

        internal override SocketType SocketType
        {
            get { return SocketType.Dgram; }
        }

        internal override ProtocolType ProtocolType
        {
            get { return ProtocolType.Udp; }
        }
    }
}
