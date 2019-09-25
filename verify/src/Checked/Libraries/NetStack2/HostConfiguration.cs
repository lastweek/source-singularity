///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:
//
//  Note:
//

using System;
using System.Collections;
using System.Net.IP;

using Microsoft.Contracts;
using Microsoft.Singularity;

//using Microsoft.Singularity.NetStack.Common;
using Microsoft.Singularity.NetStack.Protocols;
//using Microsoft.Singularity.NetStack.NetDrivers;
using MonitorLock = System.Threading.MonitorLock;

namespace Microsoft.Singularity.NetStack2
{
    // define the InterfaceList
    public class InterfaceList : ArrayList {}

    /**
     * The local host IP configuration
     */
    public class HostConfiguration
    {
        private string                 hostname;
        private string                 domainname;
        private bool                   isRouter;
        private RoutingTable          routingTable;
        private IList                 nameServers;
        private MonitorLock           nameServersLock = new MonitorLock();
        private IPAdapterBindingTable bindings;
        private ArrayList             dhcpClients;
        private MonitorLock           dhcpClientsLock = new MonitorLock();
        private ArrayList             adapters;  //list of registered adapters

        [NotDelayed]
        public HostConfiguration()
        {
            RoutingTable routingTableOnStack = new RoutingTable();

            isRouter     = false;
            routingTable = routingTableOnStack;
            nameServers  = new ArrayList();
            bindings     = new IPAdapterBindingTable(routingTableOnStack);
            dhcpClients  = new ArrayList();
            adapters     = new ArrayList();

            SetHostName("singularity");
            SetDomainName("microsoft.com");
#if false
            IAdapter loopbackAdapter = new LoopbackAdapter();

            Core.Instance().RegisterAdapter(loopbackAdapter, "loopback", LoopbackAdapter.RingSize);

            this.bindings.Add(loopbackAdapter,
                              new InterfaceIPConfiguration(
                                  IPv4.Loopback,
                                  new IPv4(0xff000000),
                                  IPv4.Loopback,
                                  1));
#endif
            routingTable.AddRoute(
                new RouteEntry(IPv4Network.Loopback,
                               IPv4.Loopback,
                               IPv4.Loopback,
                               RouteEntry.InterfaceMetric,
                               RouteEntry.InterfaceRouteTag)
                );
        }

        //dups?
        //XXX fix the dupes!
        public bool RegisterAdapter(IAdapter adapter)
        {
            if (adapters.Contains(adapter)) {
                    DebugStub.Print("Duplicate adapters???\n");
                    DebugStub.Break();
                    return false;
            }
            adapters.Add(adapter);
            return true;
        }

        public bool DeRegisterAdapter(IAdapter adapter)
        {
            if (!adapters.Contains(adapter)) {
                    return false;
            }
            adapters.Remove(adapter);
            return true;
        }
        //XXX this seems really unsafe!
        public IAdapter FindAdapterByName(string name)
        {
            foreach (IAdapter adapter in adapters) {
                VTable.Assert(adapter != null);
                if (adapter.NicName == name) {
                    return adapter;
                }
            }
            return null;
        }

        /// <summary>
        /// Get collection of AdapterInfo instances associated
        /// with adapters.
        /// </summary>
        public ICollection GetAdapterInfoCollection()
        {
            return adapters;
        }



        public string GetHostName()
        {
            return hostname;
        }

        public bool SetHostName(string name)
        {
            int dot = name.IndexOf('.');
            if (dot >= 0) {
                string hostpart = name.Substring(0, dot);
                string domainpart = name.Substring(dot + 1);
                if ((ValidDnsName(hostpart, false) == false) ||
                    (ValidDnsName(domainpart, true) == false))
                    return false;
                hostname   = hostpart;
                domainname = domainpart;
                return true;
            }

            if (ValidDnsName(name, false) == false)
                return false;
            hostname = name;
            return true;
        }

        public string GetDomainName()
        {
            return domainname;
        }

        public bool SetDomainName(string name)
        {
            if (ValidDnsName(name, true) == false) {
                return false;
            }
            domainname = name;
            return true;
        }

        private static bool ValidDnsName(string name, bool dotsAllowed)
        {
            if (name.Length <= 2)
                return false;

            // Dashes are okay as long as not first or last character
            int last = name.Length - 1;
            if (name[0] == '-' || name[last] == '-')
                return false;

            for (int i = 0; i <= last; i++) {
                // Letters, digits, and dashes are okay
                if (Char.IsLetterOrDigit(name[i]) == true || name[i] == '-')
                    continue;
                // Dots are okay in domain-names
                if (name[i] == '.' && dotsAllowed == true)
                    continue;
                return false;
            }
            return true;
        }

        public bool IsRouter
        {
            get { return isRouter; }
        }

        public RoutingTable RoutingTable
        {
            get { return routingTable; }
        }

        public IPAdapterBindingTable Bindings
        {
            get { return bindings; }
        }

        public void AddNameServer(IPv4 address)
        {
            using (nameServersLock.Lock()) {
                nameServers.Add(address);
            }
        }

        public bool DeleteNameServer(IPv4 address)
        {
            using (nameServersLock.Lock()) {
                int index = this.nameServers.IndexOf(address);
                if (index < 0)
                    return false;
                nameServers.RemoveAt(index);
                return true;
            }
        }

        /// <summary>
        /// Get enumerable interface of IPv4 collection
        /// containing name servers.
        /// </summary>
        public IPv4[] NameServers()
        {
            using (nameServersLock.Lock()) {
                IPv4[] servers = new IPv4[nameServers.Count];
                for (int i = 0; i < servers.Length; i++) {
                    servers[i] = (IPv4)(nameServers[i]);
                }
                return servers;
            }
        }

        /// <summary>
        /// Get the current name server.
        /// </summary>
        public IPv4 GetCurrentNameServer()
        {
            using (nameServersLock.Lock()) {
                if (nameServers.Count > 0) {
                    return (IPv4) nameServers[0];
                }
                return IPv4.Zero;
            }
        }

        /// <summary>
        /// Rotate name servers.
        /// </summary>
        public void RotateNameServers()
        {
            using (nameServersLock.Lock()) {
                if (nameServers.Count < 2)
                    return;
                IPv4 retiree = (IPv4) nameServers[0];
                nameServers.RemoveAt(0);
                nameServers.Add(retiree);
            }
        }

        public bool IsLocalAddress(IPv4 ipAddress)
        {
            return bindings.IsLocalAddress(ipAddress);
        }

        public bool StartDhcp(IAdapter adapter)
        {
            using (dhcpClientsLock.Lock()) {
                foreach (DhcpClient client in dhcpClients) {
                    if (client.Adapter == adapter)
                        return false;
                }
                DhcpClient dc = new DhcpClient(adapter);
                dc.Start();
                dhcpClients.Add(dc);
            }
            return true;
        }

        public bool StopDhcp(IAdapter adapter)
        {
            using (dhcpClientsLock.Lock()) {
                for (int i = 0; i < dhcpClients.Count; i++) {
                    DhcpClient client = (DhcpClient) dhcpClients[i];
                    if (client.Adapter == adapter) {
                        client.Stop();
                        dhcpClients.RemoveAt(i);
                        return true;
                    }
                }
            }
            return false;
        }

        public bool IsRunningDhcp(IAdapter adapter)
        {
            using (dhcpClientsLock.Lock()) {
                foreach (DhcpClient client in dhcpClients) {
                    if (client.Adapter == adapter)
                        return true;
                }
            }
            return false;
        }
    }

    // an interface ip address
    public class InterfaceIPConfiguration
    {
        IPv4 address;
        IPv4 netmask;
        IPv4 gateway;
        int  ttl;

        public InterfaceIPConfiguration(IPv4 address,
                                        IPv4 netmask,
                                        IPv4 gateway,
                                        int  ttl)
        {
            this.address = address;
            this.netmask = netmask;
            this.gateway = gateway;
            this.ttl     = ttl;
        }

        public InterfaceIPConfiguration(IPv4 address,
                                        IPv4 netmask,
                                        IPv4 gateway)
            : this(address, netmask, gateway, IpHeader.DefaultTTL)
        {
        }

        public IPv4 Address
        {
            get { return address; }
        }

        public IPv4 NetMask
        {
            get { return netmask; }
        }

        public IPv4 Gateway
        {
            get { return gateway; }
        }

        public int TTL
        {
            get { return ttl; }
            set { ttl = value; }
        }
    }

    // this is the local ip table entry
    // binds an IP to a specific adapter
    public class IPBinding
    {
        private IAdapter adapter;
        private InterfaceIPConfiguration ipConfig;

        public IPBinding(IAdapter ad, InterfaceIPConfiguration ipc)
        {
            adapter  = ad;
            ipConfig = ipc;
        }

        public IAdapter Adapter
        {
            get { return adapter; }
        }

        public InterfaceIPConfiguration IPConfiguration
        {
            get { return ipConfig; }
        }
    }

    public class IPAdapterBindingTable
    {
        Hashtable    ipBindings;   // <IPv4,IPBinding>
        RoutingTable routingTable;

        public IPAdapterBindingTable(RoutingTable routingTable)
        {
            this.ipBindings   = new Hashtable();
            this.routingTable = routingTable;
        }

        private void AddInterfaceRoutes(InterfaceIPConfiguration ipConfig)
        {
            //
            // Add subnet route
            //
            IPv4Network subnet = new IPv4Network(ipConfig.Address,
                                                 ipConfig.NetMask);
            routingTable.AddRoute(
                new RouteEntry(subnet,
                               ipConfig.Address,
                               ipConfig.Address,
                               RouteEntry.DirectlyConnectedMetric,
                               RouteEntry.InterfaceRouteTag)
                );

            //
            // Add route to gateway
            //
            routingTable.AddRoute(
                new RouteEntry(ipConfig.Gateway,
                               ipConfig.Address,
                               ipConfig.Address,
                               RouteEntry.DirectlyConnectedMetric,
                               RouteEntry.InterfaceRouteTag)
                );

            //
            // Add default route if none exists
            //
            if (routingTable.Lookup(IPv4Network.Default) == null) {
                routingTable.AddRoute(
                    new RouteEntry(IPv4Network.Default,
                                   ipConfig.Gateway,
                                   ipConfig.Address,
                                   RouteEntry.DefaultRouteMetric,
                                   RouteEntry.InterfaceRouteTag)
                    );
            }
        }

        private void DeleteInterfaceRoutes(InterfaceIPConfiguration ipConfig)
        {
            routingTable.DeleteInterfaceRoutes(ipConfig.Address);
        }

        public bool Add(IAdapter adapter, InterfaceIPConfiguration ipConfig)
        {
            if (ipBindings[ipConfig.Address] != null) {
                return false;
            }
            ipBindings[ipConfig.Address] = new IPBinding(adapter, ipConfig);
            AddInterfaceRoutes(ipConfig);
            return true;
        }

        /// <summary>
        /// Delete all IP address bindings associated with adapter.
        /// </summary>
        public void Flush(IAdapter adapter)
        {
            Stack flushItems = new Stack();
            foreach (IPBinding ipb in ipBindings.Values) {
                if (ipb.Adapter == adapter) {
                    flushItems.Push(ipb.IPConfiguration);
                }
            }

            while (flushItems.Count != 0) {
                Flush((InterfaceIPConfiguration) flushItems.Pop());
            }
        }

        /// <summary>
        /// Delete specific IP address binding from adapter.
        /// </summary>
        internal void Flush(IAdapter adapter, IPv4 address)
        {
            IPBinding ipb = (IPBinding) ipBindings[address];
            if (ipb != null && ipb.Adapter == adapter) {
                Flush(ipb.IPConfiguration);
            }
        }

        private void Flush(InterfaceIPConfiguration ipConfig)
        {
            DeleteInterfaceRoutes(ipConfig);
            ipBindings.Remove(ipConfig.Address);
        }

        public IAdapter GetAdapter(IPv4 address)
        {
            IPBinding ipb = (IPBinding) ipBindings[address];
            if (ipb == null) {
                return null;
            }
            return ipb.Adapter;
        }

        // is the given ip defined?
        public bool IsLocalAddress(IPv4 ipAddress)
        {
            return ipBindings[ipAddress] != null;
        }

        public ArrayList GetAdapterIPConfigurations(IAdapter adapter)
        {
            ArrayList results = new ArrayList();
            foreach (IPBinding ipb in ipBindings.Values) {
                if (ipb.Adapter == adapter)
                    results.Add(ipb.IPConfiguration);
            }
            return results;
        }
    }
}
