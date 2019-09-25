///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: IPv6HostEntry.cs
//

namespace System.Net.IP
{
    public class IPv6HostEntry
    {
        private string [] aliases;
        private IPv6 []   addresses;

        public string [] Aliases
        {
            get { return aliases; }
            set { aliases = value; }
        }

        public IPv6 [] AddressList
        {
            get { return addresses; }
            set { addresses = value; }
        }
    }
} // namespace System.Net.IP
