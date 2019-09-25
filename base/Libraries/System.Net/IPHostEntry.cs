///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: IPHostEntry.
//

namespace System.Net
{

// Host information
    /// <devdoc>
    ///    <para>Provides a container class for Internet host address information..</para>
    /// </devdoc>
    public class IPHostEntry {
        string hostName;
        string[] aliases;
        IPAddress[] addressList;

        /// <devdoc>
        ///    <para>
        ///       Contains the DNS
        ///       name of the host.
        ///    </para>
        /// </devdoc>
        /// <devdoc>
        /// </devdoc>
        public string HostName {
            get {
                return hostName;
            }
            set {
                hostName = value;
            }
        }

        /// <devdoc>
        ///    <para>
        ///       Provides an
        ///       array of strings containing other DNS names that resolve to the IP addresses
        ///       in <paramref name='AddressList'/>.
        ///    </para>
        /// </devdoc>
        /// <devdoc>
        /// </devdoc>
        public string[] Aliases {
            get {
                return aliases;
            }
            set {
                aliases = value;
            }
        }

        /// <devdoc>
        ///    <para>
        ///       Provides an
        ///       array of <paramref name='IPAddress'/> objects.
        ///    </para>
        /// </devdoc>
        /// <devdoc>
        /// </devdoc>
        public IPAddress[] AddressList {
            get {
                return addressList;
            }
            set {
                addressList = value;
            }
        }
    } // class IPHostEntry
} // namespace System.Net
