////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

//------------------------------------------------------------------------------
// <copyright file="SocketFlags.cs" company="Microsoft">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//------------------------------------------------------------------------------

namespace System.Net.Sockets
{
    using System;

    /// <devdoc>
    ///    <para>
    ///       Provides constant values for socket messages.
    ///    </para>
    /// </devdoc>
    //UEUE

    [Flags]
    public enum SocketFlags {

        /// <devdoc>
        ///    <para>
        ///       Use no flags for this call.
        ///    </para>
        /// </devdoc>
        None                = 0x0000,

        /// <devdoc>
        ///    <para>
        ///       Process out-of-band data.
        ///    </para>
        /// </devdoc>
        OutOfBand           = 0x0001,

        /// <devdoc>
        ///    <para>
        ///       Peek at incoming message.
        ///    </para>
        /// </devdoc>
        Peek                = 0x0002,

        /// <devdoc>
        ///    <para>
        ///       Send without using routing tables.
        ///    </para>
        /// </devdoc>
        DontRoute           = 0x0004,

        // see: http://as400bks.rochester.ibm.com/pubs/html/as400/v4r5/ic2978/info/apis/recvms.htm
        MaxIOVectorLength   = 0x0010,

        /// <devdoc>
        ///    <para>
        ///       Partial send or recv for message.
        ///    </para>
        /// </devdoc>

        Truncated           = 0x0100,
        ControlDataTruncated = 0x0200,
        Broadcast           = 0x0400,
        MultiCast           = 0x0800,


        Partial             = 0x8000,

    }; // enum SocketFlags

} // namespace System.Net.Sockets
