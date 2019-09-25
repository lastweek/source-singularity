////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    This is a port of the System.Net.Sockets.Socket class to Singularity.
//    Currently, it only supports TCP sockets.
//

using Microsoft.SingSharp;
using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using NetStack.Contracts;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Contracts;

namespace System.Net.Sockets
{
    internal class TcpSocket : InternalSocket
    {
        // This can be NULL if the channel has been discarded.
        private TRef<TcpConnectionContract.Imp:ReadyState> m_Conn;

        private IPEndPoint m_LocalEndPoint; // Strictly a cache; may be null
        private IPEndPoint m_RemoteEndPoint; // Strictly a cache; may be null

        // Data arrives from the netstack in discrete packets; in order to
        // adapt this to the socket interface, we keep a buffer of data
        // that has been read from the NetStack but not passed off to
        // the user.
        private TrackedBytesBuffer m_DataBuffer;

        // NOTE: not sure what error to specify when an operation
        // is not allowed by the current socket state; this is the value
        // I use. Change it if it's inappropriate
        private const int BAD_SOCKET_STATE_ERR = (int)SocketErrors.WSAEOPNOTSUPP;

        // ================== Private Methods ==================

        // Returns true if the channel is in one of the three connected states
        // (connected, ReceiveOnly, SendOnly)
        private bool IsConnected(TcpConnectionContract.Imp! conn)
        {
            return (conn.InState(TcpConnectionContract.Connected.Value) ||
                    conn.InState(TcpConnectionContract.ReceiveOnly.Value) ||
                    conn.InState(TcpConnectionContract.SendOnly.Value));
        }
#if !SPL 
        // Returns true if the channel allows writing
        private bool CanWrite(TcpConnectionContract.Imp! conn) {
            if (conn.InState(TcpConnectionContract.Connected.Value)) {
                return true;  
            }
            else  if(conn.InState(TcpConnectionContract.SendOnly.Value)) {
                return true; 
            }
            if (conn.InState(TcpConnectionContract.ReceiveOnly.Value)) {
//                DebugStub.Break();
                return false; 
            }
            if (conn.InState(TcpConnectionContract.ReadyState.Value)) {
                DebugStub.Break();
                return false; 
            }
            if (conn.InState(TcpConnectionContract.Listening.Value)) {
                DebugStub.Break();
                return false; 
            }
           return false; 
        }
#else
        // Returns true if the channel allows writing
        private bool CanWrite(TcpConnectionContract.Imp! conn)
        {
            return (conn.InState(TcpConnectionContract.Connected.Value) ||
                    conn.InState(TcpConnectionContract.SendOnly.Value));
        }
#endif 
        // Returns true if the channel allows reading
        private bool CanRead(TcpConnectionContract.Imp! conn)
        {
            return (conn.InState(TcpConnectionContract.Connected.Value) ||
                    conn.InState(TcpConnectionContract.ReceiveOnly.Value));
        }

        // Returns the channel or throws a BAD_SOCKET_STATE_ERR error
        private TcpConnectionContract.Imp! GetChannelOrThrow()
        {
            if (m_Conn == null) {
                throw new SocketException(BAD_SOCKET_STATE_ERR);
            }
            else {
                return m_Conn.Acquire();
            }
        }

        // Release the previously-acquired channel
        private void ReleaseChannel([Claims]TcpConnectionContract.Imp! conn)
        {
            m_Conn.Release(conn);
        }

        //
        // Returns false if we are in an inappropriate state to retrieve the
        // local endpoint
        //
        private bool GetLocalEndPoint(out uint localIP, out ushort localPort)
        {
            localIP = 0;
            localPort = 0;

            TcpConnectionContract.Imp! conn = GetChannelOrThrow();

            try {
                // We need to be connected or listening to retrieve the local
                // endpoint
                if ((!conn.InState(TcpConnectionContract.Listening.Value)) &&
                    (!IsConnected(conn)))
                {
                    return false;
                }

                conn.SendGetLocalAddress();
                conn.RecvIPAddress(out localIP);
                conn.SendGetLocalPort();
                conn.RecvPort(out localPort);
                return true;
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        //
        // Returns false if we are in an inappropriate state to retrieve the
        // remote endpoint
        //
        private bool GetRemoteEndPoint(out uint localIP, out ushort localPort)
        {
            localIP = 0;
            localPort = 0;

            TcpConnectionContract.Imp! conn = GetChannelOrThrow();

            try {
                // Need to be connected for the remote endpoint to be defined
                if (!IsConnected(conn)) {
                    return false;
                }

                conn.SendGetRemoteAddress();
                conn.RecvIPAddress(out localIP);
                conn.SendGetRemotePort();
                conn.RecvPort(out localPort);
                return true;
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        // Reads as much as possible without blocking, tack it onto dataBuffer.
        // We will block for a MAXIMUM of the time specified by "microSeconds".
        // Returns true if future read operations are permissible, false if
        // the data stream has ended
        private bool DrainDataNonBlock(TcpConnectionContract.Imp! conn,
                                       TrackedBytesBuffer! dataBuffer,
                                       int microSeconds)
        {
            bool keepTrying = true;
            int timeToSleep = microSeconds;

            while (keepTrying) {
                keepTrying = false; // defensive
                conn.SendPollRead(timeToSleep);

                switch receive {
                    case conn.Data(byte[]! in ExHeap readData) :
                        // Tack this onto the data buffer. Data is consumed by AddToTail()
                        dataBuffer.AddToTail(readData);

                        // Keep trying, but don't sleep. We do this strictly to
                        // drain off any additional data, since currently the
                        // netStack hands data to us in packet-sized chunks,
                        // which means it may have additional data ready if you
                        // ask it again.
                        keepTrying = true;
                        timeToSleep = 0;
                        break;

                    case conn.NoData() :
                        // done
                        return true;
                        break;

                    case conn.NoMoreData() :
                        return false;
                        break;

                    case conn.ConnectionClosed() :
                        return false;
                        break;
                }
            }

            // Should never get here
            return true;
        }

        // Makes a round-trip to the NetStack to pull in as much data as
        // possible, only blocking as long as is specified by the
        // microSeconds argument (this can be zero). Reports the new
        // amount of data in our internal buffer.
        private int GetAvailableBytes(int microSeconds)
        {
            TcpConnectionContract.Imp conn = GetChannelOrThrow();

            try {
                if (CanRead(conn)) {
                    // Drain as much data from the netstack as possible
                    DrainDataNonBlock(conn, m_DataBuffer, microSeconds);
                }

                return m_DataBuffer.Count;
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        // Performs a single blocking read to the netstack, and adds data
        // to dataBuffer.
        // Returns true if future read operations are permissible; false
        // if the data stream has ended.
        private bool BlockingRead(TcpConnectionContract.Imp! conn, TrackedBytesBuffer! dataBuffer)
        {
            conn.SendRead();

            switch receive {
                case conn.Data(byte[]! in ExHeap readData) :
                    // Tack this onto the data buffer. Data is consumed by AddToTail.
                    dataBuffer.AddToTail(readData);
                    return true;
                    break;

                case conn.NoMoreData() :
                    return false;
                    break;

                case conn.ConnectionClosed() :
                    return false;
                    break;
            }
        }

        private void Initialize([Claims] TcpConnectionContract.Imp:ReadyState! conn)
        {
            // Stash the endpoint into our field
            m_Conn = new TRef<TcpConnectionContract.Imp:ReadyState>(conn);

            // Create an empty data buffer...
            m_DataBuffer = new TrackedBytesBuffer();
        }

        [NotDelayed]
        private TcpSocket([Claims] TcpConnectionContract.Imp:ReadyState! conn)
        {
            Initialize(conn);
        }

        // ================== Internal Methods ==================

        [NotDelayed]
        internal TcpSocket()
        {
            // Connect to the Tcp module
            TcpContract.Imp! impConn;
            TcpContract.Exp! expConn;
            TcpContract.NewChannel(out impConn, out expConn);
            DirectoryServiceContract.Imp! epNS = DirectoryService.NewClientEndpoint();

            try {
                epNS.SendBind(Bitter.FromString2(TcpContract.ModuleName), expConn);

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
                }
            }
            finally {
                delete epNS;
            }

            try {
                // Create a new Tcp connection
                TcpConnectionContract.Exp! tcpExpConn;
                TcpConnectionContract.Imp! tcpImpConn;

                TcpConnectionContract.NewChannel(out tcpImpConn, out tcpExpConn);
                impConn.SendCreateTcpSession(tcpExpConn);
                impConn.RecvAck();

                // Confirm that the channel is wired up
                tcpImpConn.RecvReady();

                Initialize(tcpImpConn);
            }
            finally {
                delete impConn;
            }
        }

        internal override void Dispose()
        {
            if (m_Conn != null) {
                TcpConnectionContract.Imp conn = m_Conn.Acquire();
                delete conn;
                m_Conn = null;
            }
        }

        internal override InternalSocket Accept()
        {
            // We need to be in the listening state
            TcpConnectionContract.Imp conn = GetChannelOrThrow();

            try {
                if (!conn.InState(TcpConnectionContract.Listening.Value)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                TcpConnectionContract.Exp! newExpConn;
                TcpConnectionContract.Imp! newImpConn;
                // Make sure to create the new channel in the connected
                // state!
                TcpConnectionContract.NewChannel(out newImpConn, out newExpConn,
                                                 TcpConnectionContract.PreConnected.Value);

                conn.SendAccept(newExpConn);
                conn.RecvOK(); // BLOCKS

                // Receive the confirmation message that the new channel
                // is established
                newImpConn.RecvReady();

                return new TcpSocket(newImpConn);
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        internal override void Bind(EndPoint localEP)
        {
            if (localEP == null) {
                throw new ArgumentNullException("localEP");
            }

            IPEndPoint ep = localEP as IPEndPoint;

            if (ep == null) {
                // Illegal argument
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            // Make sure we're in the ReadyState state
            TcpConnectionContract.Imp conn = GetChannelOrThrow();

            try {
                if (!conn.InState(TcpConnectionContract.ReadyState.Value)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                conn.SendBindLocalEndPoint((uint) ep.Address.m_addr,
                                           (ushort) ep.Port);
                switch receive {
                    case conn.OK() :
                        // success!
                        break;
                    case conn.InvalidEndPoint() :
                        throw new SocketException(SocketErrors.WSAEADDRNOTAVAIL);
                        break;
                }
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        internal override void Close()
        {
            // NOTE: we should add support for the SO_DONTLINGER and SO_LINGER
            // socket options, and then call either Close() or Abort() on our underlying
            // channel. We will also need to add support for sleeping-close to the
            // NetStack to support nonzero SO_LINGER values.
            TcpConnectionContract.Imp conn = GetChannelOrThrow();

            // Need to be listening, connected or zombied to close
            if ((!conn.InState(TcpConnectionContract.ReadyState.Value)) &&
                (!conn.InState(TcpConnectionContract.Listening.Value)) &&
                (!IsConnected(conn)) &&
                (!conn.InState(TcpConnectionContract.Zombie.Value)))
            {
                ReleaseChannel(conn);
                throw new SocketException(BAD_SOCKET_STATE_ERR);
            }
            else {
                conn.SendClose();
                ReleaseChannel(conn);
                Dispose(); // This discards the channel
            }
        }

        internal override void Connect(EndPoint remoteEP)
        {
            if (remoteEP == null) {
                throw new ArgumentNullException("remoteEP");
            }

            IPEndPoint ep = remoteEP as IPEndPoint;

            if (ep == null) {
                // Illegal argument
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            TcpConnectionContract.Imp conn = GetChannelOrThrow();

            if ((!conn.InState(TcpConnectionContract.ReadyState.Value)) &&
                (!conn.InState(TcpConnectionContract.Bound.Value)))
            {
                // Need to be in the ReadyState or Bound state to issue
                // a Connect
                throw new SocketException(BAD_SOCKET_STATE_ERR);
            }

            try {
                conn.SendConnect((uint)ep.Address.m_addr,
                                 unchecked((ushort)ep.Port));

                switch receive {
                    case conn.CouldNotConnect(TcpError error) :
                        string message = TcpException.GetMessageForTcpError(error);
                        throw new TcpException(error, String.Format("A TCP connection could not be established to endpoint {0}.  {1}",
                            remoteEP.ToString(), message));

                    case conn.OK() :
                        // Success
                        break;
                }
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        //
        //public object GetSocketOption(SocketOptionLevel optionLevel, SocketOptionName optionName)
        //{
        //  // TODO
        //  throw new NotSupportedException();
        //}
//
        //public void GetSocketOption(SocketOptionLevel optionLevel, SocketOptionName optionName, byte[] optionValue)
        //{
        //  // TODO
        //  throw new NotSupportedException();
        //}
//
        //public byte[] GetSocketOption(SocketOptionLevel optionLevel, SocketOptionName optionName, int optionLength)
        //{
        //  // TODO
        //  throw new NotSupportedException();
        //}
        //

        internal override void Listen(int backlog)
        {
            // We have to be in the Bound state to Listen
            TcpConnectionContract.Imp conn = GetChannelOrThrow();

            if (!conn.InState(TcpConnectionContract.Bound.Value)) {
                throw new SocketException(BAD_SOCKET_STATE_ERR);
            }

            try {
                conn.SendListen(backlog);

                switch receive {
                    case conn.CouldNotListen() :
                        throw new SocketException(SocketErrors.SocketError);
                        break;

                    case conn.OK() :
                        // Success
                        break;
                }
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        internal override bool Poll(int microSeconds, SelectMode mode)
        {
            switch (mode) {
                //
                // For SelectRead, return true iff:
                //    Listen has been called and a connection is pending, OR
                //    Data is available for reading, OR
                //    The connection has been closed, reset, or terminated
                //
                case SelectMode.SelectRead :
                    {
                        TcpConnectionContract.Imp conn = GetChannelOrThrow();
                        bool isClosed, sessionsWaiting = false;

                        try {
                            // First check if our channel is in the Closed state
                            isClosed = conn.InState(TcpConnectionContract.Closed.Value);

                            // Now check if there are sessions available for Accept()
                            if (conn.InState(TcpConnectionContract.Listening.Value)) {
                                conn.SendIsSessionAvailable();
                                conn.RecvSessionIsAvailable(out sessionsWaiting);
                            }
                        }
                        finally {
                            ReleaseChannel(conn);
                        }

                        int dataAvailable = 0;

                        try {
                            dataAvailable = GetAvailableBytes(microSeconds);
                        }
                        catch (Exception) {
                            // Swallow any exceptions here
                        }

                        return ((dataAvailable > 0) || isClosed || sessionsWaiting);
                    }
                    break;

                //
                // For SelectWrite, return true iff:
                //    An asynchronous Connect has succeeded, OR
                //    Data can be sent
                //
                case SelectMode.SelectWrite :
                    {
                        bool isConnected = false;

                        try {
                            isConnected = Connected;
                        }
                        catch (Exception) {
                            // swallow everything
                        }

                        // We don't currently support async operations,
                        // so just indicate true if we are connected (meaning
                        // we can send data)
                        return isConnected;
                    }
                    break;

                //
                // For SelectError, return true iff:
                //    An asynchronous Connect has failed
                //    OutOfBandInline is not set, and out-of-band data is available.
                //
                case SelectMode.SelectError :
                    // We don't support any of the requisite operations
                    return false;
                    break;
            }

            // never get here
            Debug.Assert(false);
            return false;
        }

        internal override int Receive(byte[]!     buffer,
                                      int         offset,
                                      int         size,
                                      SocketFlags socketFlags)
        {
            if ((socketFlags != SocketFlags.None) &&
                (socketFlags != SocketFlags.Peek))
            {
                // Invalid flags for this operation
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            if (buffer == null) {
                throw new ArgumentNullException("buffer");
            }

            if (offset < 0 || offset > buffer.Length) {
                throw new ArgumentOutOfRangeException("offset");
            }
            if (size < 0 || size > buffer.Length - offset) {
                throw new ArgumentOutOfRangeException("size");
            }

            bool fPeek = ((int)socketFlags & (int)SocketFlags.Peek) != 0;

            // If we can satisfy the read request from our internal buffer, just
            // do that and we're done.
            if (size <= m_DataBuffer.Count) {
                int copied = m_DataBuffer.CopyFromHead(buffer, offset, size, fPeek);
                Debug.Assert(copied == size);
                return size;
            }

            TcpConnectionContract.Imp conn = GetChannelOrThrow();

            try {
                int dataCount = m_DataBuffer.Count;

                if (!CanRead(conn)) {
                    // The channel doesn't support reading anymore.

                    if (dataCount > 0) {
                        // There's some residual data in our buffer.
                        m_DataBuffer.CopyFromHead(buffer, offset, dataCount, fPeek);
                    }

                    return dataCount;
                }

                // We're in the connected state, but we don't have as much
                // data as the reader would like already available. Take
                // this opportunity to drain off as much as possible from
                // the Netstack below us.
                bool canReadAgain = DrainDataNonBlock(conn, m_DataBuffer, 0);
                dataCount = m_DataBuffer.Count;

                if (!canReadAgain) {
                    // The connection went away!
                    if (dataCount == 0) {
                        // At the beginning of this call, the socket was
                        // readable, but now it's not. So the data
                        // stream has just ended. Signal this to the caller
                        // with a zero-size completion.
                        // If the caller tries to Receive() again, they'll
                        // get an exception.
                        return 0;
                    }
                    // else return some data below
                }

                if (dataCount > 0) {
                    // Return as much as possible, even if the data stream
                    // has ended
                    int countToReturn = (size > dataCount) ? dataCount : size;
                    m_DataBuffer.CopyFromHead(buffer, offset, countToReturn, fPeek);
                    return countToReturn;
                }
                else {
                    // There's no data at all, but we can still read. Block.
                    canReadAgain = BlockingRead(conn, m_DataBuffer);
                    dataCount = m_DataBuffer.Count;

                    if (!canReadAgain) {
                        if (dataCount == 0)
                        // See comment above
                        { return 0; }
                        // else return some data below
                    }

                    // We did a blocking read and were told that future reads
                    // are permissible. It wouldn't make sense to not have
                    // received some data at this point.
                    Debug.Assert(dataCount > 0);

                    // Return as much as possible.
                    int countToReturn = (size > dataCount) ? dataCount : size;
                    m_DataBuffer.CopyFromHead(buffer, offset, countToReturn, fPeek);
                    return countToReturn;
                }
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        internal override int ReceiveFrom(byte[]!     buffer,
                                          int         offset,
                                          int         size,
                                          SocketFlags socketFlags,
                                          ref EndPoint remoteEP)
        {
            int recvBytes = Receive(buffer, offset, size, socketFlags);
            remoteEP = RemoteEndPoint;
            return recvBytes;
        }

        //
        //public static void Select(IList checkRead, IList checkWrite, IList checkError, int microSeconds)
        //{
        //  // TODO
        //  throw new NotSupportedException();
        //}
        //

        internal override int Send([Claims] byte[]! in ExHeap data,
                                   SocketFlags socketFlags)
        {
            int byteCount = data.Length;

            if (byteCount == 0) {
                // This shoudn't really happen, obviously
                delete data;
                return 0;
            }

            if (socketFlags != SocketFlags.None) {
                // Invalid flags for this operation
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            TcpConnectionContract.Imp conn = GetChannelOrThrow();

            try {
                if (!CanWrite(conn)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                conn.SendWrite(data); // Give away data

                switch receive {
                    case conn.OK() :
                        // Success
                        return byteCount;
                        break;

                    case conn.CantSend() :
                        // uh oh
                        throw new SocketException(SocketErrors.WSAENOTCONN);
                    break;
                }
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        internal override int Send(byte[]!     buffer,
                                   int         offset,
                                   int         size,
                                   SocketFlags socketFlags)
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

            // Copy the data into the shared heap
            byte[]! in ExHeap dataToWrite = Bitter.FromByteArray(buffer, offset, size);
            return Send(dataToWrite, socketFlags);
        }

        internal override int SendTo(byte[]!     buffer,
                                     int         offset,
                                     int         size,
                                     SocketFlags socketFlags,
                                     EndPoint    remoteEP)
        {
            return Send(buffer, offset, size, socketFlags);
        }

        //
        //public void SetSocketOption(SocketOptionLevel optionLevel, SocketOptionName optionName, int optionValue)
        //{
        //  // TODO
        //  throw new NotSupportedException();
        //}
//
        //public void SetSocketOption(SocketOptionLevel optionLevel, SocketOptionName optionName, byte[] optionValue)
        //{
        //  // TODO
        //  throw new NotSupportedException();
        //}
//
        //public void SetSocketOption(SocketOptionLevel optionLevel, SocketOptionName optionName, bool optionValue)
        //{
        //  SetSocketOption(optionLevel, optionName, (optionValue?1:0));
        //}
        //

        internal override void Shutdown(SocketShutdown how)
        {
            TcpConnectionContract.Imp conn = GetChannelOrThrow();

            try {
                if ((how == SocketShutdown.Both) ||
                    (how == SocketShutdown.Receive))
                {
                    if (!CanRead(conn)) {
                        // Can't shut down reading if it's not currently allowed
                        throw new SocketException(BAD_SOCKET_STATE_ERR);
                    }

                    conn.SendDoneReceiving();
                }

                if ((how == SocketShutdown.Both) ||
                    (how == SocketShutdown.Send))
                {
                    if (!CanWrite(conn)) {
                        // Can't shut down writing if it's not currently allowed
                        throw new SocketException(BAD_SOCKET_STATE_ERR);
                    }

                    conn.SendDoneSending();
                }
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        // ================== Properties ==================

        //
        // NOTE: Many of these are hard-coded for now since we only support
        // IPv4 Tcp streams.
        //

        internal override int Available {
            get {
                return GetAvailableBytes(0); // Don't sleep at all
            }
         }

        internal override EndPoint LocalEndPoint {
            get {
                if (m_LocalEndPoint == null) {
                    uint ipAddr;
                    ushort port;

                    if (!GetLocalEndPoint(out ipAddr, out port)) {
                        return null;
                    }

                    m_LocalEndPoint = new IPEndPoint(ipAddr, port);
                }

                return m_LocalEndPoint;
            }
        }

        internal override EndPoint RemoteEndPoint {
            get {
                if (m_RemoteEndPoint == null) {
                    uint ipAddr;
                    ushort port;

                    if (!GetRemoteEndPoint(out ipAddr, out port)) {
                        return null;
                    }

                    m_RemoteEndPoint = new IPEndPoint(ipAddr, port);
                }

                return m_RemoteEndPoint;
            }
        }

        internal override bool Blocking {
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
                TcpConnectionContract.Imp conn = GetChannelOrThrow();
                bool connected = IsConnected(conn);
                ReleaseChannel(conn);
                return connected;
            }
        }

        internal override AddressFamily AddressFamily {
            get {
                return AddressFamily.InterNetwork;
            }
        }

        internal override SocketType SocketType {
            get {
                return SocketType.Stream;
            }
        }

        internal override ProtocolType ProtocolType {
            get {
                return ProtocolType.Tcp;
            }
        }
    }
}
