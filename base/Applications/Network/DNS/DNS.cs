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

using Microsoft.SingSharp;
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
    [ConsoleCategory(HelpMessage="Add network routing information", DefaultAction=true)]
    internal class AddConfig
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<DNSContract.Imp:Start> dnsRef;

        [StringArrayParameter( "Servers",  HelpMessage="Servers to add")]
        internal string[] servers;

        reflective internal AddConfig();

        internal int AppMain()
        {
            DebugStub.Break();
            DNS.Add(this);
            return 0;
        }
    }

    [ConsoleCategory(Action="show", HelpMessage="Show DNS information")]
    internal class ShowConfig
    {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<DNSContract.Imp:Start> dnsRef;

        reflective internal ShowConfig();

        internal int AppMain()
        {
            return DNS.Show(this);
        }
    }

    [ConsoleCategory(Action="delete", HelpMessage="Delete DNS information")]
    internal class DeleteConfig
    {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<DNSContract.Imp:Start> dnsRef;

        [StringArrayParameter( "Servers", Mandatory=true, Position=0,  HelpMessage="Servers to delete")]
        internal string[] servers;

        reflective internal DeleteConfig();

        internal int AppMain()
        {
            DNS.Delete(this);
            return 0;
        }
    }

    [ConsoleCategory(Action="rotate", HelpMessage="Rotate name servers")]
    internal class RotateConfig
    {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<DNSContract.Imp:Start> dnsRef;

        reflective internal RotateConfig();

        internal int AppMain()
        {
            DNS.Rotate(this);
            return 0;
        }
    }


    [ConsoleCategory(Action="query", HelpMessage="Query DNS information")]
    internal class QueryConfig
    {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<DNSContract.Imp:Start> dnsRef;

        [Endpoint]
        public readonly TRef<IPContract.Imp:Start> ipRef;

        [StringParameter( "host", Mandatory=true, Position=0, HelpMessage="host to be queried")]
        internal string name;

        reflective internal QueryConfig();

        internal int AppMain()
        {
            DNS.Query(this);
            return 0;
        }
    }

    public class DNS
    {
        internal static int Add(AddConfig! config)
        {
            DebugStub.Break();

            if (config.servers == null) {
                Console.WriteLine("no servers given");
                return -1;
            }

            DNSContract.Imp dnsConn = ((!)config.dnsRef).Acquire();
            if (dnsConn == null) {
                Console.WriteLine("Could not initialize DNS endpoint.");
                delete dnsConn;
                return 1;
            }
            dnsConn.RecvReady();

            for (int i = 0; i < config.servers.Length; i++) {
                IPv4 resolver;
                Console.WriteLine("Resolving {0}", config.servers[i]);

                if (IPv4.Parse(config.servers[i], out resolver) == false) {
                    Console.WriteLine("Invalid IP address: {0}", config.servers[i]);
                }

                dnsConn.SendAddNameServer((uint)resolver);
                dnsConn.RecvAck();
            }
            delete dnsConn;
            return 0;
        }

        internal static int Delete(DeleteConfig! config)
        {
             if (config.servers == null) {
                Console.WriteLine("no servers given");
                return -1;
            }

            DNSContract.Imp dnsConn = ((!)config.dnsRef).Acquire();
            if (dnsConn == null) {
                Console.WriteLine("Could not initialize DNS endpoint.");
                return 1;
            }
            dnsConn.RecvReady();

            for (int i = 0; i < config.servers.Length; i++) {
                IPv4 resolver;
                if (IPv4.Parse(config.servers[i], out resolver) == false) {
                    Console.WriteLine("Invalid IP address: {0}", config.servers[i]);
                }

                dnsConn.SendRemoveNameServer((uint)resolver);
                dnsConn.RecvAck();
            }
            delete dnsConn;
            return 0;
        }

        private static bool QueryInternal(string! name)
        {
            // NOTE: use the System.NET APIs here, just to exercise our
            // port of them. We could also accomplish this by using a
            // DNS channel.
            try {
                System.Net.IPHostEntry hostInfo = System.Net.Dns.GetHostByName(name);
                if (hostInfo == null) return false;

                IPAddress[] addresses = hostInfo.AddressList;
                if (addresses == null) return false;
                String[] aliases = hostInfo.Aliases;
                if (aliases == null) return false;

                Console.Write("Host names:   ");

                int end = aliases.Length - 1;
                for (int i = 0; i <= end; i++) {
                    Console.Write("{0}{1}", aliases[i], (i == end) ? "" : ", ");
                }
                Console.Write("\n");

                end = addresses.Length - 1;

                Console.Write("IP addresses: ");
                for (int i = 0; i <= end; i++) {
                    Console.Write("{0}{1}", addresses[i], (i == end) ? "" : ", ");
                }
                Console.Write("\n");

                return true;
            }
            catch (System.Net.Sockets.SocketException) {
                return false;
            }
        }

        internal static int Query(QueryConfig! config)
            requires config.name != null;
        {
            bool isValid;
            string name = config.name;

            DNSContract.Imp dnsConn = ((!)config.dnsRef).Acquire();
            if (dnsConn == null) {
                Console.WriteLine("Could not initialize DNS endpoint.");
                return 1;
            }
            dnsConn.RecvReady();

            dnsConn.SendIsValidName(Bitter.FromString(name));
            dnsConn.RecvIsValid(out isValid);

            if (!isValid) {
                Console.Write("Invalid name: {0}", name);
                delete dnsConn;
                return -1;
            }

            if (QueryInternal(name)) {
                delete dnsConn;
                return -1;
            }

            IPContract.Imp ipConn = ((!)config.ipRef).Acquire();
            if (ipConn == null) {
                Console.WriteLine("Could not initialize IP endpoint.");
                delete dnsConn;
                return -1;
            }

            try {
                // Ad-hoc search list
                char[]! in ExHeap repDomain;
                ipConn.SendGetDomainName();
                ipConn.RecvDomainName(out repDomain);
                string domain = Bitter.ToString(repDomain);
                delete repDomain;

                if (domain == null) {
                    Console.WriteLine("Couldn't resolve \"" + name + "\"");
                    delete dnsConn;
                    delete ipConn;
                    return -1;
                }

                name = String.Concat(name, ".");
                int index = 0;
                do {
                    string guess = String.Concat(name, domain.Substring(index));
                    dnsConn.SendIsValidName(Bitter.FromString(guess));
                    dnsConn.RecvIsValid(out isValid);

                    if (isValid && QueryInternal(guess)) {
                        delete dnsConn;
                        delete ipConn;
                        return -1;
                    }

                    index = domain.IndexOf('.', index) + 1;
                } while (index > 0 && index < domain.Length);

                Console.WriteLine("No IP address found");
            }
            finally {
            }
            delete ipConn;
            delete dnsConn;
            return 0;
        }

        internal static int Rotate(RotateConfig! config)
        {
            DNSContract.Imp dnsConn = ((!)config.dnsRef).Acquire();
            if (dnsConn == null) {
                Console.WriteLine("Could not initialize DNS endpoint.");
                return 1;
            }
            dnsConn.RecvReady();

            dnsConn.SendRotateNameServers();
            dnsConn.RecvAck();
            delete dnsConn;
            return 0;
        }


        internal  static int Show(ShowConfig! config)
        {
            DNSContract.Imp dnsConn = ((!)config.dnsRef).Acquire();
            if (dnsConn == null) {
                Console.WriteLine("Could not initialize DNS endpoint.");
                return 1;
            }
            dnsConn.RecvReady();

            Utils.DNSShow(dnsConn);
            delete dnsConn;
            return 0;
        }
    } // end class DNS
}
