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
using Microsoft.SingSharp;
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

    [ConsoleCategory(Action="show", HelpMessage="Show network routing information")]
    internal class ShowConfig {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<RoutingContract.Imp:Start> routingRef;

        reflective internal ShowConfig();

        internal int AppMain() {
            return Route.Show(this);
        }
    }

    [ConsoleCategory(HelpMessage="Add network routing information",DefaultAction=true)]
    internal class AddConfig {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<RoutingContract.Imp:Start> routingRef;

        [Endpoint]
        public readonly TRef<IPContract.Imp:Start> ipRef;

        [StringParameter( "destination", Mandatory=true, Position=0, HelpMessage="destination to be added")]
        internal string destination;

        [StringParameter( "g", Mandatory=true, Position=1,  HelpMessage="Gateway")]
        internal string gateway;
        
        [StringParameter( "i", Default=null, HelpMessage="ifAddress")]
        internal string ifAddress;

        reflective internal AddConfig();

        internal int AppMain() {
             Route.Add(this);
             return 0; 
        }
    }

    [ConsoleCategory(Action="delete", HelpMessage="Remove network routing information")]
    internal class DeleteConfig {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<RoutingContract.Imp:Start> routingRef;

        [StringParameter( "address", Mandatory=true, Position=0, HelpMessage="Address to be removed")]
        internal string address;

        [StringParameter( "destination", Mandatory=true, Position=0, HelpMessage="destination to be removed")]
        internal string destination;
      
        reflective internal DeleteConfig();

        internal int AppMain() {
            return Route.Delete(this);
        }
    }

    /// <summary>
    /// Class for routing related configuration.
    /// </summary>
    public class Route
    {
        internal static int Show(ShowConfig! config)
        {
            RouteEntry[] in ExHeap routes;

            RoutingContract.Imp routeConn = ((!)config.routingRef).Acquire();
            if (routeConn == null) {
                Console.WriteLine("Could not initialize routing endpoint.");
                return 1;
            }
            routeConn.RecvReady();

            routeConn.SendGetRoutingTable();
            routeConn.RecvRoutingTable(out routes);

            if (routes == null)
                throw new Exception("routes is null");

            for (int i = 0; i < routes.Length; i++) {
                Console.WriteLine("Network           : " + ChannelUtils.NetworkToString(routes[i].network));
                Console.WriteLine("Gateway           : " + ChannelUtils.AddressToString(routes[i].gateway));
                Console.WriteLine("Interface address : " + ChannelUtils.AddressToString(routes[i].ifaddr));
                Console.WriteLine("Metric            : " + routes[i].metric);
                Console.WriteLine(String.Format("Tag               : {0:x8}\n", routes[i].tag));
            }

            delete routes;
            delete routeConn; 
            return 0; 
        }

        internal static int Add(AddConfig! config)
        {
            IPv4 gateway;
  
            RoutingContract.Imp routeConn = ((!)config.routingRef).Acquire();
            if (routeConn == null) {
                Console.WriteLine("Could not initialize routing endpoint.");
                return 1;
            }
            routeConn.RecvReady();

            if (IPv4.Parse(config.gateway, out gateway) == false) {
                Console.WriteLine("Could not parse gateway address.");
                delete routeConn;
                return -1;
            }

            try {
                // NOTE: for some reason the compiler doesn't
                // realize that ifaddr will definitely be assigned if
                // we survive the if/switch-receive sequence. Work
                // around that by initializing.
                IPv4 ifaddr = new IPv4(0);

                if (config.ifAddress == null) {
                    routeConn.SendFindHostRoute((uint)gateway);

                    switch receive {
                        case routeConn.Route(RouteEntry r) :
                            ifaddr = new IPv4(r.ifaddr);
                            break;

                        case routeConn.NoRouteFound() :
                            Console.WriteLine("No route to gateway.");
                            delete routeConn;
                            return -1;
                            break;

                        case routeConn.ChannelClosed() :
                            Console.WriteLine("routeConn channel closed.");
                            throw new Exception("routeConn channel closed.");
                    }
                }
                else if (IPv4.Parse(config.ifAddress, out ifaddr) == false) {
                    Console.WriteLine("Could not parse interface address.");
                    delete routeConn; 
                    return -1;
                }

                IPContract.Imp ipConn = ((!)config.ipRef).Acquire(); 
                if (ipConn == null) {
                    Console.WriteLine("Could not initialize IP endpoint.");
                    delete routeConn; 
                    return -1;
                }

                try {
                    bool isLocal;
                    ipConn.SendIsLocalAddress((uint)ifaddr);
                    ipConn.RecvIsLocal(out isLocal);

                    if (!isLocal) {
                        Console.WriteLine("Proposed interface address is not bound to an interface.");
                        delete routeConn; 
                        return -1;
                    }
                }
                finally {
                    delete ipConn;
                    ipConn = null;
                }

                IPv4Network destination;
                if (IPv4Network.Parse(config.destination, out destination) == false) {
                    Console.WriteLine("Could not parse destination address.");
                    delete routeConn;
                    return  -1;
                }

                NetStack.Contracts.Network nwrk = new NetStack.Contracts.Network();
                nwrk.network = (uint)destination.Network;
                nwrk.netmask = (uint)destination.NetMask;
                routeConn.SendAddRoute(nwrk, (uint)gateway, (uint)ifaddr);

                switch receive {
                    case routeConn.Err() :
                        Console.WriteLine("Route could not be added -- it may already exist.");
                        break;

                    case routeConn.OK() :
                        Console.WriteLine("Route added successfully");
                        break;

                    case routeConn.ChannelClosed() :
                        throw new Exception("routeConn channel closed");
                }
            }
            catch (Exception e) {
                Console.WriteLine("Exception: {0}", e);
            }
            delete routeConn; 
            return 0;
        }

        internal static int Delete(DeleteConfig! config)
        {
            RoutingContract.Imp routeConn = ((!)config.routingRef).Acquire();
            if (routeConn == null) {
                Console.WriteLine("Could not initialize routing endpoint.");
                return 1;
            }
            routeConn.RecvReady();

            IPv4Network destination;
            if (IPv4Network.Parse(config.destination, out destination) == false) {
                Console.WriteLine("Could not parse destination address.");
            }

            Network destNet = ChannelUtils.NetworkToChannelNetwork(destination);
            routeConn.SendFindSpecificNetRoute(destNet);

            switch receive {
                case routeConn.NoRouteFound() :
                    Console.WriteLine("No route for destination.");
                    delete routeConn; 
                    return -1;

                case routeConn.Route(RouteEntry r) :
                    // Do nothing; success.
                    break;

                case routeConn.ChannelClosed() :
                    Console.WriteLine("routeConn channel closed.");
                    throw new Exception("routeConn channel closed.");
            }

            routeConn.SendDeleteRoute(destNet);

            switch receive {
                case routeConn.NoRouteFound() :
                    Console.WriteLine("Unexpected error attempting to delete the route");
                    break;

                case routeConn.OK() :
                    Console.WriteLine("Route successfully deleted");
                    break;

                case routeConn.ChannelClosed() :
                    Console.WriteLine("routeConn channel closed");
                    throw new Exception("routeConn channel closed");
            }
            delete routeConn; 
            return 0;
        }
    } // end class Route
}
