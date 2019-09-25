// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Net.IP;
using Drivers.Net;

namespace NetStack.Runtime
{
    public class RouteEntry : IComparable
    {
        public const uint InterfaceRouteTag = 0x80000000;

        public const uint InterfaceMetric         = 0;
        public const uint DirectlyConnectedMetric = 1;
        public const uint DefaultRouteMetric      = 20;

        private IPv4Network network;
        private IPv4        gateway;
        private IPv4        ifaddr;
        private uint        metric;
        private uint        tag;

        public RouteEntry(IPv4Network network,
                          IPv4        gateway,
                          IPv4        ifaddr,
                          uint        metric,
                          uint        tag)
        {
            this.network = network;
            this.gateway = gateway;
            this.ifaddr  = ifaddr;
            this.metric  = metric;
            this.tag     = tag;
        }

        public RouteEntry(IPv4Network network,
                          IPv4        gateway,
                          IPv4        ifaddr)
            : this (network, gateway, ifaddr, DefaultRouteMetric, 0)
        {
        }

        public RouteEntry(IPv4 host,
                          IPv4 gateway,
                          IPv4 ifaddr,
                          uint metric,
                          uint tag)
        {
            this.network = new IPv4Network(host, IPv4.BitCount);
            this.gateway = gateway;
            this.ifaddr  = ifaddr;
            this.metric  = metric;
            this.tag     = tag;
        }

        public RouteEntry(IPv4 host,
                          IPv4 gateway,
                          IPv4 ifaddr)
            : this (host, gateway, ifaddr, DefaultRouteMetric, 0)
        {
        }

        public IPv4Network Network   { get { return network; } }
        public IPv4 Gateway          { get { return gateway; } }
        public IPv4 InterfaceAddress { get { return ifaddr; } }
        public uint Metric           { get { return metric; } }
        public uint Tag              { get { return tag; } }

        public override string! ToString()
        {
            if (network.MaskLength == IPv4.BitCount) {
                return String.Format("Host    {0,-17} Gateway {1,-14} " +
                                     "Interface {2,-14} Metric {3,-3} " +
                                     "Tag {4:x8}",
                                     network.LowerBound, gateway,
                                     ifaddr, metric, tag);
            }
            else {
                return String.Format("Network {0,-17} Gateway {1,-14} " +
                                     "Interface {2,-14} Metric {3,-3} " +
                                     "Tag {4:x8}",
                                     network, gateway, ifaddr, metric, tag);
            }
        }

        public int CompareTo(object o)
        {
            RouteEntry other = o as RouteEntry;
            if (other == null)
                throw new ArgumentException();

            //
            // Metric - Cheapest route wins
            //
            if (this.metric < other.metric) {
                return -1;
            }
            else if (this.metric > other.metric) {
                return +1;
            }

            //
            // Specificity - Most specific wins
            //
            if (network.IsLessSpecificThan(other.network)) {
                return +1;
            }
            else if (network.IsMoreSpecificThan(other.network)) {
                return -1;
            }

            //
            // Numeric value of network - lowest value wins
            //
            IPv4 ourAddress   = network.LowerBound;
            IPv4 otherAddress = other.network.LowerBound;

            if (ourAddress < otherAddress) {
                return -1;
            }
            if (ourAddress == otherAddress) {
                return 0;
            }
            return +1;
        }
    } // RouteEntry

    /// <summary>
    /// A placeholder implementation of a routing table.
    /// RoutingTables are great areas for optimization and
    /// there's a ton of ways to perform fast lookups.  The
    /// current implementation uses a linear search to find the
    /// best route and should be replaced if there are going to
    /// be have more than a handful of routes.
    ///
    /// Also note the current implementation allows routes to be
    /// added without being fully resolvable.  Finding the interface
    /// for a route may take multiple lookups.
    ///
    /// </summary>
    public class RoutingTable
    {
        private SortedList! routes;      // synchronized

        public RoutingTable()
        {
            routes = SortedList.Synchronized(new SortedList());
            base();
        }

        public int Count
        {
            get { return routes.Count; }
        }

        public bool AddRoute(RouteEntry! e)
        {
            try {
                routes.Add(e, e);
                return true;
            }
            catch (ArgumentException) {
                return false;
            }
        }

        public bool DeleteRoute(RouteEntry e)
        {
            lock (routes.SyncRoot) {
                int oldCount = routes.Count;
                routes.Remove(e);
                return oldCount > routes.Count;
            }
        }

        /// <summary>
        /// Get route for destination address.
        /// </summary>
        public RouteEntry Lookup(IPv4 destination)
        {
            foreach (RouteEntry! e in routes.Values) {
                if (e.Network.Contains(destination)) {
                    return e;
                }
            }
            return null;
        }

        /// <summary>
        /// Get route for destination network.
        /// </summary>
        public RouteEntry Lookup(IPv4Network destination)
        {
            foreach (RouteEntry! e in routes.Values) {
                if (e.Network.Contains(destination)) {
                    return e;
                }
            }
            return null;
        }

        /// <summary>
        /// Get Enumerator for <c>RouteEntry</c> instances in Routing table.
        /// </summary>
        public IEnumerator GetEnumerator()
        {
            return routes.Values.GetEnumerator();
        }

        /// <summary>
        /// Get route for specific destination.
        /// </summary>
        /// <returns>Specific route if it is present,
        /// <c>null</c> otherwise.  </returns>
        public RouteEntry LookupSpecific(IPv4 destination)
        {
            return LookupSpecific(new IPv4Network(destination, IPv4.BitCount));
        }

        /// <summary>
        /// Get route for specific destination network.
        /// </summary>
        /// <returns>Specific route if it is present,
        /// <c>null</c> otherwise.  </returns>
        public RouteEntry LookupSpecific(IPv4Network destination)
        {
            foreach (RouteEntry! e in routes.Values) {
                if (e.Network == destination) {
                    return e;
                }
            }
            return null;
        }

        /// <summary>
        /// Delete all routes that have specified interface address.
        /// </summary>
        public void DeleteInterfaceRoutes(IPv4 interfaceAddress)
        {
            ArrayList deadRoutes = new ArrayList();

            lock (routes) {
                foreach (RouteEntry! e in routes.Values) {
                    if (e.InterfaceAddress == interfaceAddress) {
                        deadRoutes.Add(e);
                    }
                }
            }

            foreach (RouteEntry e in deadRoutes) {
                deadRoutes.Remove(e);
            }
        }
    }
}
