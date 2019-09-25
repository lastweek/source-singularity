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

//using Microsoft.SingSharp;
//using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using NetStack.Contracts;
using System.Collections;
//using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Contracts;
using TcpConnectionContract = Microsoft.Singularity.NetStack2.Channels.Private.TcpConnectionContract;
using IPv4 = System.Net.IP.IPv4;

namespace System.Net.Sockets
{
    internal class TcpSocket : InternalSocket
    {
        // This can be NULL if the channel has been discarded.
        private TRef/*<TcpConnectionContract.Imp>*/ m_Conn;

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
        private bool IsConnected(TcpConnectionContract/*.Imp*/ conn)
        {
            return (conn.InState(TcpConnectionContract.State.Connected/*.Value*/) //||
                    //conn.InState(TcpConnectionContract.ReceiveOnly/*.Value*/) ||
                    //conn.InState(TcpConnectionContract.SendOnly/*.Value*/)
                    );
        }
#if !SPL 
        // Returns true if the channel allows writing
        private bool CanWrite(TcpConnectionContract/*.Imp*/ conn) {
            if (conn.InState(TcpConnectionContract.State.Connected/*.Value*/)) {
                return true;  
            }
//            else  if(conn.InState(TcpConnectionContract.SendOnly/*.Value*/)) {
//                return true; 
//            }
//            if (conn.InState(TcpConnectionContract.ReceiveOnly/*.Value*/)) {
//                DebugStub.Break();
//                return false; 
//            }
            if (conn.InState(TcpConnectionContract.State.ReadyState/*.Value*/)) {
                DebugStub.Break();
                return false; 
            }
            if (conn.InState(TcpConnectionContract.State.Listening/*.Value*/)) {
                DebugStub.Break();
                return false; 
            }
           return false; 
        }
#else
        // Returns true if the channel allows writing
        private bool CanWrite(TcpConnectionContract/*.Imp*/ conn)
        {
            return (conn.InState(TcpConnectionContract.State.Connected/*.Value*/));// ||
                    //conn.InState(TcpConnectionContract.SendOnly/*.Value*/));
        }
#endif 
        // Returns true if the channel allows reading
        private bool CanRead(TcpConnectionContract/*.Imp*/ conn)
        {
            return (conn.InState(TcpConnectionContract.State.Connected/*.Value*/));// ||
                    //conn.InState(TcpConnectionContract.ReceiveOnly/*.Value*/));
        }

        // Returns the channel or throws a BAD_SOCKET_STATE_ERR error
        private TcpConnectionContract/*.Imp*/ GetChannelOrThrow()
        {
            if (m_Conn == null) {
                throw new SocketException(BAD_SOCKET_STATE_ERR);
            }
            else {
                return (TcpConnectionContract)m_Conn.Acquire();
            }
        }

        // Release the previously-acquired channel
        private void ReleaseChannel(TcpConnectionContract/*.Imp*/ conn)
        {
            m_Conn.Release(conn);
        }

        //
        // Returns false if we are in an inappropriate state to retrieve the
        // local endpoint
        //
        private bool GetLocalEndPoint(out IPv4 localIP, out ushort localPort)
        {
            localIP = new IPv4(0);
            localPort = 0;

            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

            try {
                // We need to be connected or listening to retrieve the local
                // endpoint
                if ((!conn.InState(TcpConnectionContract.State.Listening/*.Value*/)) &&
                    (!IsConnected(conn)))
                {
                    return false;
                }

                localIP = conn.GetLocalAddress();
                localPort = conn.GetLocalPort();
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
        private bool GetRemoteEndPoint(out IPv4 localIP, out ushort localPort)
        {
            localIP = new IPv4(0);
            localPort = 0;

            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

            try {
                // Need to be connected for the remote endpoint to be defined
                if (!IsConnected(conn)) {
                    return false;
                }

                localIP = conn.GetRemoteAddress();
                localPort = conn.GetRemotePort();
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
        private bool DrainDataNonBlock(TcpConnectionContract/*.Imp*/ conn,
                                       TrackedBytesBuffer dataBuffer,
                                       int microSeconds)
        {
            bool keepTrying = true;
            int timeToSleep = microSeconds;

            while (keepTrying) {
                keepTrying = false; // defensive
                Bytes readData = conn.PollRead(timeToSleep);

                    //case conn.Data(byte[] readData) :
                    if (readData != null && readData.Length > 0) {
                        // Tack this onto the data buffer. Data is consumed by AddToTail()
                        dataBuffer.AddToTail(readData);

                        // Keep trying, but don't sleep. We do this strictly to
                        // drain off any additional data, since currently the
                        // netStack hands data to us in packet-sized chunks,
                        // which means it may have additional data ready if you
                        // ask it again.
                        keepTrying = true;
                        timeToSleep = 0;
                        continue;
                    }

                    //case conn.NoData() :
                    if (readData != null && readData.Length == 0) {
                        // done
                        return true;
                    }

                    //case conn.NoMoreData() :
                    //case conn.ConnectionClosed() :
                    if (readData == null) {
                        return false;
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
            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

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
        private bool BlockingRead(TcpConnectionContract/*.Imp*/ conn, TrackedBytesBuffer dataBuffer)
        {
            Bytes readData = conn.Read();

                //case conn.Data(byte[] readData) :
                if (readData != null) {
                    // Tack this onto the data buffer. Data is consumed by AddToTail.
                    dataBuffer.AddToTail(readData);
                    return true;
                }

                //case conn.NoMoreData() :
                //case conn.ConnectionClosed() :
                    return false;
        }

        private void Initialize(TcpConnectionContract/*.Imp*/ conn)
        {
            // Stash the endpoint into our field
            m_Conn = new TRef/*<TcpConnectionContract.Imp>*/(conn);

            // Create an empty data buffer...
            m_DataBuffer = new TrackedBytesBuffer();
        }

        [NotDelayed]
        private TcpSocket(TcpConnectionContract/*.Imp*/ conn)
        {
            Initialize(conn);
        }

        // ================== Internal Methods ==================

        [NotDelayed]
        internal TcpSocket()
        {
            // Connect to the Tcp module
            //TcpContract/*.Imp*/ impConn = new TcpContract();

                        //impConn.RecvReady();

                // Create a new Tcp connection
                TcpConnectionContract/*.Exp*/ tcpExpConn = new TcpConnectionContract();
                //impConn.SendCreateTcpSession(tcpExpConn);
                Initialize(tcpExpConn);
        }

        internal override void Dispose()
        {
            if (m_Conn != null) {
                TcpConnectionContract/*.Imp*/ conn = (TcpConnectionContract)(m_Conn.Acquire());
                //delete conn;
                m_Conn = null;
            }
        }

        internal override InternalSocket Accept()
        {
            // We need to be in the listening state
            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

            try {
                if (!conn.InState(TcpConnectionContract.State.Listening/*.Value*/)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                TcpConnectionContract newExpConn = new TcpConnectionContract();
                conn.Accept(newExpConn);
                return new TcpSocket(newExpConn);
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
            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

            try {
                if (!conn.InState(TcpConnectionContract.State.ReadyState/*.Value*/)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                conn.BindLocalEndPoint(ep.Address.m_addr,
                                           (ushort) ep.Port);
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
            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

            // Need to be listening, connected or zombied to close
            if ((!conn.InState(TcpConnectionContract.State.ReadyState/*.Value*/)) &&
                (!conn.InState(TcpConnectionContract.State.Listening/*.Value*/)) &&
                (!IsConnected(conn)) &&
                (!conn.InState(TcpConnectionContract.State.Zombie/*.Value*/)))
            {
                ReleaseChannel(conn);
                throw new SocketException(BAD_SOCKET_STATE_ERR);
            }
            else {
                conn.Close();
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

            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

            if ((!conn.InState(TcpConnectionContract.State.ReadyState/*.Value*/)) &&
                (!conn.InState(TcpConnectionContract.State.Bound/*.Value*/)))
            {
                // Need to be in the ReadyState or Bound state to issue
                // a Connect
                throw new SocketException(BAD_SOCKET_STATE_ERR);
            }

            try {
                conn.Connect(ep.Address.m_addr,
                                 unchecked((ushort)ep.Port));
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
            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

            if (!conn.InState(TcpConnectionContract.State.Bound/*.Value*/)) {
                throw new SocketException(BAD_SOCKET_STATE_ERR);
            }

            try {
                conn.Listen(backlog);
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
                        TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();
                        bool isClosed, sessionsWaiting = false;

                        try {
                            // First check if our channel is in the Closed state
                            isClosed = conn.InState(TcpConnectionContract.State.Closed/*.Value*/);

                            // Now check if there are sessions available for Accept()
                            if (conn.InState(TcpConnectionContract.State.Listening/*.Value*/)) {
                                sessionsWaiting = conn.IsSessionAvailable();
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

                //
                // For SelectError, return true iff:
                //    An asynchronous Connect has failed
                //    OutOfBandInline is not set, and out-of-band data is available.
                //
                case SelectMode.SelectError :
                    // We don't support any of the requisite operations
                    return false;
            }

            // never get here
            Debug.Assert(false);
            return false;
        }

        internal override int Receive(byte[]     buffer,
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

            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

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

        internal override int ReceiveFrom(byte[]     buffer,
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

        internal override int Send(Bytes data,
                                   SocketFlags socketFlags)
        {
            int byteCount = data.Length;

            if (byteCount == 0) {
                // This shoudn't really happen, obviously
                //delete data;
                return 0;
            }

            if (socketFlags != SocketFlags.None) {
                // Invalid flags for this operation
                throw new SocketException(SocketErrors.WSAEINVAL);
            }

            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

            try {
                if (!CanWrite(conn)) {
                    throw new SocketException(BAD_SOCKET_STATE_ERR);
                }

                conn.Write(data); // Give away data
                return byteCount;
            }
            finally {
                ReleaseChannel(conn);
            }
        }

        internal override int Send(byte[]     buffer,
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
            Bytes dataToWrite = Bitter.FromByteArray(buffer, offset, size);
            return Send(dataToWrite, socketFlags);
        }

        internal override int SendTo(byte[]     buffer,
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
            TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();

            try {
                if ((how == SocketShutdown.Both) ||
                    (how == SocketShutdown.Receive))
                {
                    if (!CanRead(conn)) {
                        // Can't shut down reading if it's not currently allowed
                        throw new SocketException(BAD_SOCKET_STATE_ERR);
                    }

                    conn.DoneReceiving();
                }

                if ((how == SocketShutdown.Both) ||
                    (how == SocketShutdown.Send))
                {
                    if (!CanWrite(conn)) {
                        // Can't shut down writing if it's not currently allowed
                        throw new SocketException(BAD_SOCKET_STATE_ERR);
                    }

                    conn.DoneSending();
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
                    IPv4 ipAddr;
                    ushort port;

                    if (!GetLocalEndPoint(out ipAddr, out port)) {
                        return null;
                    }

                    m_LocalEndPoint = new IPEndPoint((uint)ipAddr, port);
                }

                return m_LocalEndPoint;
            }
        }

        internal override EndPoint RemoteEndPoint {
            get {
                if (m_RemoteEndPoint == null) {
                    IPv4 ipAddr;
                    ushort port;

                    if (!GetRemoteEndPoint(out ipAddr, out port)) {
                        return null;
                    }

                    m_RemoteEndPoint = new IPEndPoint((uint)ipAddr, port);
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
                TcpConnectionContract/*.Imp*/ conn = GetChannelOrThrow();
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
