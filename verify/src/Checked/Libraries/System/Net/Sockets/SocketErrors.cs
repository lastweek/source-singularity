////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

//------------------------------------------------------------------------------
// <copyright file="SocketErrors.cs" company="Microsoft">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//------------------------------------------------------------------------------

namespace System.Net.Sockets
{
    using System;

    /// <devdoc>
    ///    <para>
    ///       Defines socket error constants.
    ///    </para>
    /// </devdoc>
    public enum SocketErrors : int {
        /// <devdoc>
        ///    <para>
        ///       The operation completed successfully.
        ///    </para>
        /// </devdoc>
        Success                = 0,
        /// <devdoc>
        ///    <para>
        ///       The socket is invalid.
        ///    </para>
        /// </devdoc>
        InvalidSocket          = (-1),
        /// <devdoc>
        ///    <para>
        ///       The socket has an error.
        ///    </para>
        /// </devdoc>
        SocketError            = (-1),
        /// <devdoc>
        ///    <para>
        ///       Overlapped operations will complete later.
        ///    </para>
        /// </devdoc>
        WSA_IO_PENDING             = 997, // Winsock 2 Defines this value just to be ERROR_IO_PENDING or 997
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        ERROR_OPERATION_ABORTED    = 995,


        //
        // All Windows Sockets error constants are biased by WSABASEERR from
        // the "normal"
        // 
        /// <devdoc>
        ///    <para>
        ///       The base value of all socket error constants. All other socket errors are
        ///       offset from this value.
        ///    </para>
        /// </devdoc>
        WSABASEERR             = 10000,


        //
        // Windows Sockets definitions of regular Microsoft C error constants
        // 
        /// <devdoc>
        ///    <para>
        ///       A blocking socket call was canceled.
        ///    </para>
        /// </devdoc>
        WSAEINTR               = (WSABASEERR+4),
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        WSAEBADF               = (WSABASEERR+9),
        /// <devdoc>
        ///    <para>
        ///       Permission denied.
        ///    </para>
        /// </devdoc>
        WSAEACCES              = (WSABASEERR+13),
        /// <devdoc>
        ///    <para>
        ///       Bad address.
        ///    </para>
        /// </devdoc>
        WSAEFAULT              = (WSABASEERR+14),
        /// <devdoc>
        ///    <para>
        ///       Invalid argument.
        ///    </para>
        /// </devdoc>
        WSAEINVAL              = (WSABASEERR+22),
        /// <devdoc>
        ///    <para>
        ///       Too many open
        ///       files.
        ///    </para>
        /// </devdoc>
        WSAEMFILE              = (WSABASEERR+24),


        //
        // Windows Sockets definitions of regular Berkeley error constants
        // 
        /// <devdoc>
        ///    <para>
        ///       Resource temporarily unavailable.
        ///    </para>
        /// </devdoc>
        WSAEWOULDBLOCK         = (WSABASEERR+35),
        /// <devdoc>
        ///    <para>
        ///       Operation now in progress.
        ///    </para>
        /// </devdoc>
        WSAEINPROGRESS         = (WSABASEERR+36),
        /// <devdoc>
        ///    <para>
        ///       Operation already in progress.
        ///    </para>
        /// </devdoc>
        WSAEALREADY            = (WSABASEERR+37),
        /// <devdoc>
        ///    <para>
        ///       Socket operation on nonsocket.
        ///    </para>
        /// </devdoc>
        WSAENOTSOCK            = (WSABASEERR+38),
        /// <devdoc>
        ///    <para>
        ///       Destination address required.
        ///    </para>
        /// </devdoc>
        WSAEDESTADDRREQ        = (WSABASEERR+39),
        /// <devdoc>
        ///    <para>
        ///       Message too long.
        ///    </para>
        /// </devdoc>
        WSAEMSGSIZE            = (WSABASEERR+40),
        /// <devdoc>
        ///    <para>
        ///       Protocol wrong type for socket.
        ///    </para>
        /// </devdoc>
        WSAEPROTOTYPE          = (WSABASEERR+41),
        /// <devdoc>
        ///    <para>
        ///       Bad protocol option.
        ///    </para>
        /// </devdoc>
        WSAENOPROTOOPT         = (WSABASEERR+42),
        /// <devdoc>
        ///    <para>
        ///       Protocol not supported.
        ///    </para>
        /// </devdoc>
        WSAEPROTONOSUPPORT     = (WSABASEERR+43),
        /// <devdoc>
        ///    <para>
        ///       Socket type not supported.
        ///    </para>
        /// </devdoc>
        WSAESOCKTNOSUPPORT     = (WSABASEERR+44),
        /// <devdoc>
        ///    <para>
        ///       Operation not supported.
        ///    </para>
        /// </devdoc>
        WSAEOPNOTSUPP          = (WSABASEERR+45),
        /// <devdoc>
        ///    <para>
        ///       Protocol family not supported.
        ///    </para>
        /// </devdoc>
        WSAEPFNOSUPPORT        = (WSABASEERR+46),
        /// <devdoc>
        ///    <para>
        ///       Address family not supported by protocol family.
        ///    </para>
        /// </devdoc>
        WSAEAFNOSUPPORT        = (WSABASEERR+47),
        /// <devdoc>
        ///    Address already in use.
        /// </devdoc>
        WSAEADDRINUSE          = (WSABASEERR+48),
        /// <devdoc>
        ///    <para>
        ///       Cannot assign requested address.
        ///    </para>
        /// </devdoc>
        WSAEADDRNOTAVAIL       = (WSABASEERR+49),
        /// <devdoc>
        ///    <para>
        ///       Network is down.
        ///    </para>
        /// </devdoc>
        WSAENETDOWN            = (WSABASEERR+50),
        /// <devdoc>
        ///    <para>
        ///       Network is unreachable.
        ///    </para>
        /// </devdoc>
        WSAENETUNREACH         = (WSABASEERR+51),
        /// <devdoc>
        ///    <para>
        ///       Network dropped connection on reset.
        ///    </para>
        /// </devdoc>
        WSAENETRESET           = (WSABASEERR+52),
        /// <devdoc>
        ///    <para>
        ///       Software caused connection to abort.
        ///    </para>
        /// </devdoc>
        WSAECONNABORTED        = (WSABASEERR+53),
        /// <devdoc>
        ///    <para>
        ///       Connection reset by peer.
        ///    </para>
        /// </devdoc>
        WSAECONNRESET          = (WSABASEERR+54),
        /// <devdoc>
        ///    No buffer space available.
        /// </devdoc>
        WSAENOBUFS             = (WSABASEERR+55),
        /// <devdoc>
        ///    <para>
        ///       Socket is already connected.
        ///    </para>
        /// </devdoc>
        WSAEISCONN             = (WSABASEERR+56),
        /// <devdoc>
        ///    <para>
        ///       Socket is not connected.
        ///    </para>
        /// </devdoc>
        WSAENOTCONN            = (WSABASEERR+57),
        /// <devdoc>
        ///    <para>
        ///       Cannot send after socket shutdown.
        ///    </para>
        /// </devdoc>
        WSAESHUTDOWN           = (WSABASEERR+58),
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        WSAETOOMANYREFS        = (WSABASEERR+59),
        /// <devdoc>
        ///    <para>
        ///       Connection timed out.
        ///    </para>
        /// </devdoc>
        WSAETIMEDOUT           = (WSABASEERR+60),
        /// <devdoc>
        ///    <para>
        ///       Connection refused.
        ///    </para>
        /// </devdoc>
        WSAECONNREFUSED        = (WSABASEERR+61),
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        WSAELOOP               = (WSABASEERR+62),
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        WSAENAMETOOLONG        = (WSABASEERR+63),
        /// <devdoc>
        ///    <para>
        ///       Host is down.
        ///    </para>
        /// </devdoc>
        WSAEHOSTDOWN           = (WSABASEERR+64),
        /// <devdoc>
        ///    <para>
        ///       No route to host.
        ///    </para>
        /// </devdoc>
        WSAEHOSTUNREACH        = (WSABASEERR+65),
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        WSAENOTEMPTY           = (WSABASEERR+66),
        /// <devdoc>
        ///    <para>
        ///       Too many processes.
        ///    </para>
        /// </devdoc>
        WSAEPROCLIM            = (WSABASEERR+67),
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        WSAEUSERS              = (WSABASEERR+68),
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        WSAEDQUOT              = (WSABASEERR+69),
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        WSAESTALE              = (WSABASEERR+70),
        /// <devdoc>
        ///    <para>
        ///       [To be supplied.]
        ///    </para>
        /// </devdoc>
        WSAEREMOTE             = (WSABASEERR+71),
        /// <devdoc>
        ///    <para>
        ///       Graceful shutdown in progress.
        ///    </para>
        /// </devdoc>
        WSAEDISCON             = (WSABASEERR+101),


        //
        // Extended Windows Sockets error constant definitions
        // 
        /// <devdoc>
        ///    <para>
        ///       Network subsystem is unavailable.
        ///    </para>
        /// </devdoc>
        WSASYSNOTREADY         = (WSABASEERR+91),
        /// <devdoc>
        ///    <para>
        ///       Winsock.dll out of range.
        ///    </para>
        /// </devdoc>
        WSAVERNOTSUPPORTED     = (WSABASEERR+92),
        /// <devdoc>
        ///    <para>
        ///       Successful startup not yet performed.
        ///    </para>
        /// </devdoc>
        WSANOTINITIALISED      = (WSABASEERR+93),

        //
        // Error return codes from gethostbyname() and gethostbyaddr()
        //              = (when using the resolver). Note that these errors are
        // retrieved via WSAGetLastError() and must therefore follow
        // the rules for avoiding clashes with error numbers from
        // specific implementations or language run-time systems.
        // For this reason the codes are based at WSABASEERR+1001.
        // Note also that [WSA]NO_ADDRESS is defined only for
        // compatibility purposes.
        // 

        /// <devdoc>
        ///    <para>
        ///       Host not found (Authoritative Answer: Host not found).
        ///    </para>
        /// </devdoc>
        WSAHOST_NOT_FOUND      = (WSABASEERR+1001),
        /// <devdoc>
        ///    <para>
        ///       Nonauthoritative host not found (Non-Authoritative: Host not found, or SERVERFAIL).
        ///    </para>
        /// </devdoc>
        WSATRY_AGAIN           = (WSABASEERR+1002),
        /// <devdoc>
        ///    <para>
        ///       This is a nonrecoverable error (Non recoverable errors, FORMERR, REFUSED, NOTIMP).
        ///    </para>
        /// </devdoc>
        WSANO_RECOVERY         = (WSABASEERR+1003),
        /// <devdoc>
        ///    <para>
        ///       Valid name, no data record of requested type.
        ///    </para>
        /// </devdoc>
        WSANO_DATA             = (WSABASEERR+1004),
        /// <devdoc>
        ///    <para>
        ///       No address, look for MX record.
        ///    </para>
        /// </devdoc>
        WSANO_ADDRESS          = WSANO_DATA,
    }


}
