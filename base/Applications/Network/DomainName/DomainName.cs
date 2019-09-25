////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program.
//
using System;
using System.Diagnostics;
using System.Net.IP;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using NetStack.Contracts;
using NetStack.Channels.Public;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications.Network
{
    [ConsoleCategory(HelpMessage="Change network routing information", DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<IPContract.Imp:Start> ipRef;

        [StringParameter( "n", Default=null,  HelpMessage="new domain name")]
        internal string name;

        reflective internal Parameters();

        internal int AppMain() {
            DomainName.AppMain(this);
            return 0;
        }
    }

    /// <summary>
    /// Class for configuring Domain Name.
    /// </summary>
    public class DomainName
    {
        internal static int AppMain(Parameters! config)
        {
            IPContract.Imp ipConn = ((!)config.ipRef).Acquire();
            if (ipConn == null) {
                Console.WriteLine("Could not initialize IP endpoint.");
                return 1;
            }
            ipConn.RecvReady();

            try {
                if (config.name == null) {
                    char[]! in ExHeap repDomain;
                    ipConn.SendGetDomainName();
                    ipConn.RecvDomainName(out repDomain);
                    Console.WriteLine(Bitter.ToString2(repDomain));
                    delete repDomain;
                }
                else {
                    ipConn.SendSetDomainName(Bitter.FromString2(config.name));

                    switch receive {
                        case ipConn.Err():
                            Console.WriteLine("Error setting domain name");
                            return 1; // failure

                        case ipConn.OK():
                            Console.WriteLine("Set domain name successfully");
                            break;

                        case ipConn.ChannelClosed():
                            Console.WriteLine("Error setting domain name (channel closed)");
                            return 1; // failure
                    }
                }
            }
            finally {
                delete ipConn;
            }

            return 0; // success
        }
    } // end class DomainName
}
