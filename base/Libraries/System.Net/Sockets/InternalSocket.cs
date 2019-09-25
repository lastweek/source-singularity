///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   InternalSocket.cs
//
//  Note:
//

using System;
using Microsoft.SingSharp;
using Microsoft.SingSharp.Runtime;
using Microsoft.Singularity.Channels;

namespace System.Net.Sockets
{
    public abstract class InternalSocket
    {
        abstract internal InternalSocket Accept();
        abstract internal void   Bind(EndPoint localEndPoint);
        abstract internal void   Close();
        abstract internal void   Connect(EndPoint remoteEndPoint);
        abstract internal void   Dispose();
        abstract internal void   Listen(int backlog);
        abstract internal bool   Poll(int microSeconds, SelectMode mode);
        abstract internal int    Receive(byte[]! buffer, int offset, int size, SocketFlags socketFlags);
        abstract internal int    ReceiveFrom(byte[]! buffer, int offset, int size, SocketFlags socketFlags, ref EndPoint remoteEP);

        abstract internal int    Send(byte[]! buffer, int offset, int size, SocketFlags socketFlags);
        abstract internal int    SendTo(byte[]! buffer, int offset, int size, SocketFlags socketFlags, EndPoint remoteEP);
        abstract internal void   Shutdown(SocketShutdown how);

        abstract internal int           Available       { get; }
        abstract internal EndPoint      LocalEndPoint   { get; }
        abstract internal EndPoint      RemoteEndPoint  { get; }
        abstract internal bool          Blocking        { get; set; }
        abstract internal bool          Connected       { get; }
        abstract internal AddressFamily AddressFamily   { get; }
        abstract internal SocketType    SocketType      { get; }
        abstract internal ProtocolType  ProtocolType    { get; }

        // Singularity-specific
        abstract internal int Send([Claims] byte[]! in ExHeap data, SocketFlags flags);
    }
}
