///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
//using Microsoft.SingSharp;
//using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using NetStack.Contracts;
using Microsoft.Singularity.V1.Services;
using Microsoft.Contracts;
using UdpConnectionContract = Microsoft.Singularity.NetStack2.Channels.Private.UdpConnectionContract;
using IPv4 = System.Net.IP.IPv4;

namespace System.Net.Sockets
{
    internal class UdpSocket : InternalSocket
    {
        private const int BAD_SOCKET_STATE_ERR = (int)SocketErrors.WSAEOPNOTSUPP;

        private TRef/*<UdpConnectionContract.Imp>*/ m_Conn;

        private IPEndPoint m_LocalEndPoint;
        private IPEndPoint m_RemoteEndPoint;

        // ================ Private Methods ================

        private void Initialize(UdpConnectionContract/*.Imp*/ conn)
        {
            m_Conn = new TRef/*<UdpConnectionContract.Imp>*/(conn);
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
            Initialize(new UdpConnectionContract());
        }

        internal override InternalSocket Accept()
        {
            throw new SocketException(SocketErrors.WSAEOPNOTSUPP);
            //return null;
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
            UdpConnectionContract/*.Imp*/ conn = (UdpConnectionContract)m_Conn.Acquire();

            try {
                if (!conn.InState(UdpConnectionContract.State.ReadyState/*.Value*/)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                conn.BindLocalEndPoint(ep.Address.m_addr,
                                           unchecked((ushort) ep.Port));
                m_LocalEndPoint = new IPEndPoint(ep.Address, ep.Port);
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override void Close()
        {
            UdpConnectionContract/*.Imp*/ conn = (UdpConnectionContract)m_Conn.Acquire();

            try {
                if (!conn.InState(UdpConnectionContract.State.Closed/*.Value*/)) {
                    conn.Close();
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

            UdpConnectionContract/*.Imp*/ conn = (UdpConnectionContract)m_Conn.Acquire();

            if (!conn.InState(UdpConnectionContract.State.ReadyState/*.Value*/) &&
                ! conn.InState(UdpConnectionContract.State.LocallyBound/*.Value*/))
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
                    conn.Connect(new IPv4(localIP), localPort,
                                     new IPv4((uint)ep.Address.m_addr),
                                     unchecked((ushort)ep.Port));
                }
                else {
                    conn.ConnectWithAnyLocalEndPoint(
                        new IPv4((uint)ep.Address.m_addr),
                        unchecked((ushort)ep.Port));
                }

                m_RemoteEndPoint = ep;
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override void Dispose()
        {
            UdpConnectionContract/*.Imp*/ conn = (UdpConnectionContract)m_Conn.Acquire();
            //delete conn;
            // Leak our TRef!
        }

        internal override void Listen(int backlog)
        {
            throw new SocketException(SocketErrors.WSAEOPNOTSUPP);
        }

        private bool PollSelectRead(UdpConnectionContract/*.Imp*/ conn,
                                    int                        millis)
        {
            return conn.PollSelectRead(millis);
        }

        private bool PollSelectWrite(UdpConnectionContract/*.Imp*/ conn,
                                     int                        millis)
        {
            return conn.PollSelectWrite(millis);
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

            UdpConnectionContract/*.Imp*/ conn = (UdpConnectionContract)m_Conn.Acquire();

            try {
                if (conn.InState(UdpConnectionContract.State.Closed/*.Value*/)) {
                    throw new ObjectDisposedException("socket");
                }

                switch (mode) {
                    case SelectMode.SelectRead:
                        return PollSelectRead(conn, millis);
                        //break;
                    case SelectMode.SelectWrite:
                        return PollSelectWrite(conn, millis);
                        //break;
                    case SelectMode.SelectError:
                        return false;
                        // We don't support any of the requisite operations
                        //break;
                    default:
                        throw new NotSupportedException();
                }
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override int ReceiveFrom(byte[]      buffer,
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

            UdpConnectionContract/*.Imp*/ conn = (UdpConnectionContract)m_Conn.Acquire();

            try {
                if (conn.InState(UdpConnectionContract.State.Closed/*.Value*/)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                Bytes rdata = conn.Read();
                uint addr = 0;
                ushort port = 0;
                        remoteEP = new IPEndPoint(new IPAddress(addr), port);
                        int amount = Math.Min(rdata.Length, size);
                        Bitter.ToByteArray(rdata, 0, amount, buffer, offset);
                        return amount;
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override int Receive(byte[]     buffer,
                                      int         offset,
                                      int         size,
                                      SocketFlags socketFlags)
        {
            EndPoint dummy = null;
            return ReceiveFrom(buffer, offset, size, socketFlags, ref dummy);
        }

        internal override int Send(Bytes data,
                                   SocketFlags socketFlags)
        {
            int byteCount = data.Length;

            if (socketFlags != SocketFlags.None) {
                // Invalid flags for this operation
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            UdpConnectionContract/*.Imp*/ conn = (UdpConnectionContract)m_Conn.Acquire();

            try {
                if (!conn.InState(UdpConnectionContract.State.Connected/*.Value*/)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                conn.Write(data); // Give away data

                        return byteCount;
            }
            finally {
                m_Conn.Release(conn);
            }
        }

        internal override int Send(byte[]    buffer,
                                   int         offset,
                                   int         size,
                                   SocketFlags socketFlags)
        {
            ValidateBufferOffsets(buffer, offset, size);
            Bytes dataToWrite = Bitter.FromByteArray(buffer, offset, size);
            return Send(dataToWrite, socketFlags);
        }

        internal override int SendTo(byte[]     buffer,
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

            UdpConnectionContract/*.Imp*/ conn = (UdpConnectionContract)m_Conn.Acquire();

            try {
                if (conn.InState(UdpConnectionContract.State.Closed/*.Value*/)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                // Copy the data to write into an ExHeap vector and send it
                Bytes dataToWrite = Bitter.FromByteArray(buffer, offset, size);

                conn.WriteTo((uint)ep.Address.m_addr,
                                 unchecked((ushort)ep.Port),
                                 dataToWrite);
                // no longer own dataToWrite!

                        return size;
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
                UdpConnectionContract/*.Imp*/ conn = (UdpConnectionContract)m_Conn.Acquire();
                try {
                    return conn.InState(UdpConnectionContract.State.Connected/*.Value*/);
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
