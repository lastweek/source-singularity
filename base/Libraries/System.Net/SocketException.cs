////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   SocketException.cs
//

namespace System.Net.Sockets
{
    using System;
    using NetStack.Contracts;

    public class SocketException : Exception {
        SocketErrors _socketError;

        public SocketException(int socketError)
            : this((SocketErrors)socketError)
        {
        }

        public SocketException(SocketErrors socketError)
            : this(socketError, String.Format("SocketError: {0}", socketError.ToString()))
        {
        }

        internal SocketException(SocketErrors socketError, string message)
            : base(message)
        {
            _socketError = socketError;
        }

        public SocketErrors ErrorCode {
            get { return _socketError; }
        }
    }

    public class TcpException : SocketException
    {
        public TcpException(TcpError error, string message)
            : base(GetSocketErrorForTcpError(error), message)
        {
            _tcpError = error;
        }

        public TcpException(TcpError error)
            : this(error, GetMessageForTcpError(error))
        {
        }

        readonly TcpError _tcpError;

        public TcpError TcpError
        {
            get { return _tcpError; }
        }

        public static SocketErrors GetSocketErrorForTcpError(TcpError error)
        {
            switch (error) {
                    // These are defined in Contracts\NetStack.Contracts\TcpConnectionContract.sg.
                case TcpError.Unknown:              return SocketErrors.SocketError; 
                case TcpError.AlreadyConnected:     return SocketErrors.WSAEISCONN;
                case TcpError.Refused:              return SocketErrors.WSAECONNREFUSED;
                case TcpError.Reset:                return SocketErrors.WSAECONNRESET;
                case TcpError.Timeout:              return SocketErrors.WSAETIMEDOUT;
                case TcpError.ProtocolViolation:    return SocketErrors.WSAECONNRESET;
                case TcpError.ResourcesExhausted:   return SocketErrors.SocketError;
                case TcpError.Closed:               return SocketErrors.WSAEDISCON;

                default:
                    return SocketErrors.SocketError;
             }
        }

        public static string GetMessageForTcpError(TcpError error)
        {
            switch (error) {
                    // These are defined in Contracts\NetStack.Contracts\TcpConnectionContract.sg.
                case TcpError.Unknown:              return "Unknown error";
                case TcpError.AlreadyConnected:     return "The connection is already in use.";
                case TcpError.Refused:              return "The remote host actively refused the connection.";
                case TcpError.Reset:                return "The connection was reset by the peer.";
                case TcpError.Timeout:              return "No response was received.";
                case TcpError.ProtocolViolation:    return "An invalid packet was received from the peer.";
                case TcpError.ResourcesExhausted:   return "Insufficient resources.";
                case TcpError.Closed:               return "The TCP connection has been closed.";

                default:
                    return String.Format("Unknown TcpError code ({0}).", ((int)error).ToString());
            }
        }
    }


} // namespace System.Net
