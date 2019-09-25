///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   RoutingExpManager.gs
//  Author: maiken
//  Note:   Provider-side helper for the Routing Channel Contract
//

using System;
using System.Threading;
using Drivers.Net;
using Microsoft.SingSharp;
using Microsoft.Singularity;
//using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;

using System.Collections;
using System.Net.IP;
using Microsoft.Singularity.NetStack;
//using Microsoft.Singularity.NetStack.Channels.Public;

namespace Microsoft.Singularity.NetStack2.Channels.Private
{
    public class RoutingExpManager
    {
        public RoutingExpManager()
        {
        }

/*
        RouteEntry[] GetRoutingTable()
        {
            HostConfiguration h = IP.GetHostConfiguration();
            RouteEntry[] retval =
                new RouteEntry[h.RoutingTable.Count];
            int i = 0;

            foreach (NetStack2.RouteEntry r in h.RoutingTable) {
                retval[i] = ConvertRouteEntry(r);
                i++;
            }

            return retval;
        }
*/

        void AddRoute(IPv4Network dest, uint gateway, uint ifaddr)
        {
            HostConfiguration h = IP.GetHostConfiguration();
            IPv4Network destination = dest;

            if (h.RoutingTable.AddRoute(
                    new NetStack2.RouteEntry(destination,
                                             new IPv4(gateway),
                                             new IPv4(ifaddr))))
            {
                return;
            }
            else {
                throw new Exception("AddRoute");
            }
        }

        NetStack2.RouteEntry FindHostRoute(uint dest)
        {
            HostConfiguration h = IP.GetHostConfiguration();
            NetStack2.RouteEntry re =
                h.RoutingTable.Lookup(new IPv4(dest));

            if (re != null) {
                return re;
            }
            else {
                throw new Exception("FindHostRoute");
            }
        }

        NetStack2.RouteEntry FindNetRoute(IPv4Network dest)
        {
            HostConfiguration h = IP.GetHostConfiguration();
            IPv4Network nwrk = dest;
            NetStack2.RouteEntry re =
                h.RoutingTable.Lookup(nwrk);

            if (re != null) {
                return re;
            }
            else {
                throw new Exception("FindNetRoute");
            }
        }

        NetStack2.RouteEntry FindSpecificHostRoute(uint dest)
        {
            HostConfiguration h = IP.GetHostConfiguration();
            NetStack2.RouteEntry re =
                h.RoutingTable.LookupSpecific(new IPv4(dest));

            if (re != null) {
                return re;
            }
            else {
                throw new Exception("FindSpecificHostRoute");
            }
        }

        NetStack2.RouteEntry FindSpecificNetRoute(IPv4Network dest)
        {
            HostConfiguration h = IP.GetHostConfiguration();
            IPv4Network nwrk = dest;
            NetStack2.RouteEntry re =
                h.RoutingTable.LookupSpecific(nwrk);

            if (re != null) {
                return re;
            }
            else {
                throw new Exception("FindSpecificNetRoute");
            }
        }

        void DeleteRoute(IPv4Network dest)
        {
            HostConfiguration h = IP.GetHostConfiguration();
            IPv4Network destNet = dest;
            NetStack2.RouteEntry re =
                h.RoutingTable.LookupSpecific(destNet);

            if (re == null) {
                throw new Exception("DeleteRoute");
            }
            else {
                h.RoutingTable.DeleteRoute(re);
            }
        }
    }
}
