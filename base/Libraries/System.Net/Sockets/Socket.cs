///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Socket.cs
//
//  Note:
//

using Microsoft.SingSharp;
using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using NetStack.Contracts;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;

namespace System.Net.Sockets
{
    public class Socket : IDisposable
    {
        InternalSocket internalSocket;
        bool disposed = false;

        // ================== Private Methods ==================

        private Socket(InternalSocket internalSocket)
        {
            this.internalSocket = internalSocket;
        }

        // ================== Public Methods ==================

        public Socket(AddressFamily addressFamily,
                      SocketType    socketType,
                      ProtocolType  protocolType)
        {
            // We only support TCP streams

            if (addressFamily != AddressFamily.InterNetwork) {
                throw new SocketException(SocketErrors.WSAEAFNOSUPPORT);
            }

            if (socketType == SocketType.Stream &&
                protocolType == ProtocolType.Tcp)
            {
                internalSocket = new TcpSocket();
                return;
            }

            if (socketType == SocketType.Dgram &&
                protocolType == ProtocolType.Udp)
            {
                internalSocket = new UdpSocket();
                return;
            }
            throw new SocketException(SocketErrors.WSAEPROTONOSUPPORT);
        }

        public void Dispose()
        {
            if (!disposed) {
                internalSocket.Dispose();
                disposed = true;
            }
        }

        public Socket Accept()
        {
            InternalSocket s = internalSocket.Accept();
            if (s != null)
                return new Socket(s);
            return null;
        }

        public void Bind(EndPoint localEP)
        {
            internalSocket.Bind(localEP);
        }

        public void Close()
        {
            internalSocket.Close();
        }

        public void Connect(EndPoint remoteEP)
        {
            internalSocket.Connect(remoteEP);
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

        public void Listen(int backlog)
        {
            internalSocket.Listen(backlog);
        }

        public bool Poll(int microSeconds, SelectMode mode)
        {
            return internalSocket.Poll(microSeconds, mode);
        }

        public int Receive(byte[] buffer, int size, SocketFlags socketFlags)
        {
            return Receive(buffer, 0, size, socketFlags);
        }

        public int Receive(byte[] buffer, SocketFlags socketFlags)
        {
            return Receive(buffer, 0, buffer!=null ? buffer.Length : 0, socketFlags);
        }

        public int Receive(byte[] buffer)
        {
            return Receive(buffer, 0, buffer!=null ? buffer.Length : 0, SocketFlags.None);
        }

        public int Receive(byte[] buffer, int offset, int size, SocketFlags socketFlags)
        {
            if (buffer == null) {
                throw new ArgumentNullException("buffer");
            }
            return internalSocket.Receive(buffer, offset, size, socketFlags);
        }

        //
        //public static void Select(IList checkRead, IList checkWrite, IList checkError, int microSeconds)
        //{
        //  // TODO
        //  throw new NotSupportedException();
        //}
        //

        public int Send(byte[] buffer, int size, SocketFlags socketFlags)
        {
            return Send(buffer, 0, size, socketFlags);
        }

        public int Send(byte[] buffer, SocketFlags socketFlags)
        {
            return Send(buffer, 0, buffer!=null ? buffer.Length : 0, socketFlags);
        }

        public int Send(byte[] buffer)
        {
            return Send(buffer, 0, buffer!=null ? buffer.Length : 0, SocketFlags.None);
        }

        public int Send(byte[] buffer, int offset, int size, SocketFlags socketFlags)
        {
            if (buffer == null) {
                throw new ArgumentException("buffer");
            }
            return internalSocket.Send(buffer, offset, size, socketFlags);
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

        public void Shutdown(SocketShutdown how)
        {
            internalSocket.Shutdown(how);
        }

        // ================== Properties ==================

        public static bool SupportsIPv4
        {
            get { return true; }
        }

        public static bool SupportsIPv6
        {
            get { return false; }
        }

        public int Available
        {
            get { return internalSocket.Available; }
        }

        public EndPoint LocalEndPoint
        {
            get { return internalSocket.LocalEndPoint; }
        }

        public EndPoint RemoteEndPoint
        {
            get { return internalSocket.RemoteEndPoint; }
        }

        public bool Blocking
        {
            get { return internalSocket.Blocking; }
        }

        public bool Connected
        {
            get { return internalSocket.Connected; }
        }

        public AddressFamily AddressFamily
        {
            get { return internalSocket.AddressFamily; }
        }

        public SocketType SocketType
        {
            get { return internalSocket.SocketType; }
        }

        public ProtocolType ProtocolType
        {
            get { return internalSocket.ProtocolType; }
        }

        // ================== Singularity-Specific ==================
        public int Send([Claims] byte[]! in ExHeap buffer, SocketFlags socketFlags)
        {
            return internalSocket.Send(buffer, socketFlags);
        }
    }
}
