///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DNSExpConnection.gs
//  Author: maiken
//  Note:   Provider-side helper for the DNS Channel Contract
//

using System;
using System.Collections;
using System.Net.IP;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.SingSharp;
using Microsoft.Singularity.Channels;

using Microsoft.Singularity.NetStack;

using Dns = Microsoft.Singularity.NetStack2.Protocols.Dns;

namespace Microsoft.Singularity.NetStack2.Channels.Private
{
    public class DNSContract
    {
        public void AddNameServer(IPv4 address)
        {
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            hostConfiguration.AddNameServer(address);
        }

        public void RemoveNameServer(IPv4 address)
        {
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            hostConfiguration.DeleteNameServer(address);
        }

        public void RotateNameServers()
        {
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            hostConfiguration.RotateNameServers();
        }

        public IPv4 GetCurrentNameServer()
        {
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            return hostConfiguration.GetCurrentNameServer();
        }

        public IPv4[] GetNameServers()
        {
            ArrayList serverList = new ArrayList();
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            return hostConfiguration.NameServers();
        }

        public void Resolve(String repName, out IPv4[] addrsAsUint, out String[] aliases)
        {
            IPv4HostEntry hostEntry;
            BasicDnsClient client = new BasicDnsClient();
            string name = repName;
            BasicDnsClient.StatusCode result = client.Resolve(name,
                                                              out hostEntry);

            if (result != BasicDnsClient.StatusCode.Success) {
                throw new Exception("Resolve: NotFound");
            }
            else {
                VTable.Assert(hostEntry != null);

                // Convert the alias strings
                aliases = new String[hostEntry.Aliases.Length];
                for (int i = 0; i < hostEntry.Aliases.Length; ++i) {
                    aliases[i] = hostEntry.Aliases[i];
                }

                // Convert the IP addresses
                IPv4[] addrs = hostEntry.AddressList;
                addrsAsUint = new IPv4[addrs.Length];

                for (int i = 0; i < addrs.Length; ++i) {
                    addrsAsUint[i] = addrs[i];
                }
            }
        }

        public bool IsValidName(String name)
        {
            return name != null && Dns.Format.IsSafeDnsName(name);
        }
    }
}
