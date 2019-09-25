///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DNSImpConnection.gs
//  Author: maiken
//  Note:   Client-side helper for the IP Channel Contract
//

using System;
using System.Threading;
using System.Net.IP;
//using Microsoft.Singularity.Drivers.Net;
//using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.NetStack2;
//using Microsoft.Singularity.NetStack.Runtime;

using DNSContract = Microsoft.Singularity.NetStack2.Channels.Private.DNSContract;

namespace Microsoft.Singularity.NetStack2
{
    public class DNSImpConnection
    {
        // Converts the results of GerNameServers to IPv4 structures
        public static IPv4[] GetNameServers(DNSContract/*.Imp*/ ep)
        {
            IPv4[] addrList = ep.GetNameServers();

                IPv4[] retval;
                if (addrList == null) {
                    retval = new IPv4[0];
                }
                else {
                    retval = addrList;
                }

                return retval;
        }

        // Converts the retrieved address(es) to IPv4 structures.
        // Returns true iff the named host was found successfully.
        public static bool Resolve(DNSContract/*.Imp*/ ep, string name,
                                   out string[] aliases, out IPv4[] addrs)
        {
            aliases = null;
            addrs = null;

            IPv4[] addrList;
            String[] aliasesResult;
            ep.Resolve(name, out addrList, out aliasesResult);

                        if (aliasesResult != null) {
                            aliases = aliasesResult;
                        }
                        else {
                            aliases = new string[0];
                        }
                        if (addrList != null) {
                            addrs = addrList;
                        }
                        else {
                            addrs = new IPv4[0];
                        }
                        return true; // success;
        }
    }
}
