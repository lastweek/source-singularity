///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Netstack / Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DhcpClientSession.cs
//
//  Note:   DHCP Client Session.
//

//#define DEBUG_DHCP_CLIENT

using NetStack.Common;
using System;
using System.Collections;
using System.Diagnostics;
using System.Threading;

using System.Net.IP;
using Drivers.Net;
using NetStack.NetDrivers;

#if SINGULARITY
using Microsoft.Singularity;
#else
using System.Net;
#endif

namespace NetStack.Runtime
{
    using Protocols;

    /// <summary>
    /// A DhcpClient acts as a DHCP Client on a particular interface.
    ///
    /// The implementation is based on RFC2131.
    /// </summary>
    public class DhcpClient
    {
        private IAdapter        adapter;
        private UdpSession      udpSession;
        private Thread          workerThread;
        private bool            workerDone;
        private DhcpClientState @state;
        private SortedList      activeDhcpOptions;

        private DateTime    renewalTimeout;
        private DateTime    rebindTimeout;
        private DateTime    stateTimeout;
        private DateTime    transactionStart;
        private uint        transactionID;

        public static byte [] StandardRequestParameters = new byte [] {
                DhcpSubnetMask.OptionCode,
                DhcpRouter.OptionCode,
                DhcpHostName.OptionCode,
                DhcpTimeOffset.OptionCode,
                DhcpDomainNameServer.OptionCode,
                DhcpDomainName.OptionCode,
                DhcpInterfaceMtu.OptionCode,
                DhcpRouterDiscovery.OptionCode,
                DhcpStaticRoutes.OptionCode,
                DhcpRenewalTime.OptionCode,
                DhcpRebindingTime.OptionCode,
                DhcpIPAddressLeaseTime.OptionCode,
                DhcpVendorSpecific.OptionCode
            };

        private static readonly TimeSpan PollInterval = TimeSpan.FromMilliseconds(1000);

        [ Conditional("DEBUG_DHCP_CLIENT") ]
        internal static void DebugPrint(string format, params object [] args)
        {
            Core.Log("DhcpClient: ");
            Core.Log(format, args);
        }

        public DhcpClient(IAdapter adapter)
        {
            this.adapter = adapter;
            transactionID = (uint)(new Random()).Next();
        }

        ~DhcpClient()
        {
            if (workerThread != null) {
                Stop();
            }
        }

        public IAdapter Adapter
        {
            get { return adapter; }
        }

        public EthernetAddress MacAddress
        {
            get { return adapter.HardwareAddress; }
        }

        public DateTime TransactionStart
        {
            get { return transactionStart; }
        }

        public ushort TransactionSeconds
        {
            get {
                TimeSpan delta = DateTime.Now - transactionStart;
                return (ushort)delta.Seconds;
            }
        }

        public uint TransactionID
        {
            get { return transactionID; }
        }

        public bool Start()
        {
            lock (this) {
                if (udpSession != null) {
                    return false;
                }

                Core core = Core.Instance();
                UdpModule udpModule =
                    core.GetProtocolByName("UDP") as UdpModule;
                if (udpModule == null) {
                    DebugPrint("DhcpClient.Start() failed -- " +
                               "UdpModule not found.\n");
                    return false;
                }

                udpSession = udpModule.CreateBoundSession(
                                 IPv4.Any, DhcpFormat.ClientPort,
                                 IPv4.Any, DhcpFormat.ServerPort
                                 );
                udpSession.BoundMux = core.GetMuxForAdapter(adapter);
                ResetAdapterIPInfo();

                workerDone = false;
                workerThread = new Thread(new ThreadStart(WorkerMain));
#if !SINGULARITY
                workerThread.Name = String.Format("DhcpClient/{0}",
                                                  adapter.HardwareAddress);
#endif
                workerThread.Start();
                return true;
            }
        }

        public void Stop()
        {
            lock (this) {
                workerDone = true;
                workerThread.Join();

                udpSession.Close();
                udpSession = null;
                workerThread = null;

                CancelTimeouts();
                @state = null;
            }
            DebugPrint("DhcpClient.Stop()\n");
        }

        private bool SetTimeout(ref DateTime timeout, DateTime when)
        {
            timeout = when;
            return timeout >= DateTime.Now;
        }

        internal void SetRenewalTimeout(DateTime when)
        {
            if (SetTimeout(ref renewalTimeout, when) == false)
                DebugPrint("Set renewal timeout in the past!\n");
        }

        internal void CancelRenewalTimeout()
        {
            renewalTimeout = DateTime.MaxValue;
        }

        internal void SetRebindTimeout(DateTime when)
        {
            if (SetTimeout(ref rebindTimeout, when) == false)
                DebugPrint("Set rebind timeout in the past!\n");
        }

        internal void CancelRebindTimeout()
        {
            rebindTimeout = DateTime.MaxValue;
        }

        internal void SetStateTimeout(DateTime when)
        {
            if (SetTimeout(ref stateTimeout, when) == false)
                DebugPrint("Set state timeout in the past!\n");
        }

        internal void CancelStateTimeout()
        {
            stateTimeout = DateTime.MaxValue;
        }

        internal void CancelTimeouts()
        {
            CancelRenewalTimeout();
            CancelRebindTimeout();
            CancelStateTimeout();
        }

        internal void ChangeState(DhcpClientState newState)
        {
            assert newState != null;
            @state = newState;
            newState.EnterEvent();
            DebugPrint("ChangeState -> {0}\n", newState.Name);
        }

        internal bool InstallDhcpOptions(SortedList! dhcpOptions)
        {
            if (activeDhcpOptions != null)
                UninstallDhcpOptions();

            IPModule ip = (IPModule) Core.Instance().GetProtocolByName("IP");
            if (ip == null) {
                DebugPrint("Failed to get IP Module\n");
                return false;
            }

            //
            // Add interface address binding
            //
            DhcpIPv4Option address =
                dhcpOptions[DhcpRequestedIPAddress.OptionCode]
                as DhcpIPv4Option;

            DhcpIPv4Option netmask =
                dhcpOptions[DhcpSubnetMask.OptionCode] as DhcpIPv4Option;

            DhcpMultiIPv4Option routers =
                dhcpOptions[DhcpRouter.OptionCode] as DhcpMultiIPv4Option;

            if (address == null || netmask == null || routers == null ||
                routers.Values.Length == 0)
            {
                return false;
            }

            ip.HostConfiguration.Bindings.Add(
                adapter, new InterfaceIPConfiguration(address.Value,
                                                      netmask.Value,
                                                      routers.Values[0])
                );

            //
            // Register Domain name
            //
            DhcpStringOption domain =
                dhcpOptions[DhcpDomainName.OptionCode] as DhcpStringOption;

            //            string domainName = ip.HostConfiguration.GetDomainName();
            // never used
            if (domain != null) {
                ip.HostConfiguration.SetDomainName(domain.Value);
            }

            //
            // Add DNS servers
            //
            DhcpMultiIPv4Option dnsServers =
                dhcpOptions[DhcpDomainNameServer.OptionCode]
                as DhcpMultiIPv4Option;
            if (dnsServers != null) {
                foreach (IPv4 server in dnsServers.Values) {
                    ip.HostConfiguration.AddNameServer(server);
                }
            }

            //
            // Install static routes
            //
            DhcpMultiIPv4Option staticRoutes =
                dhcpOptions[DhcpStaticRoutes.OptionCode]
                as DhcpMultiIPv4Option;
            if (staticRoutes != null) {
                int routeCount = staticRoutes.Values.Length & ~1; // pairs
                for (int i = 0; i < routeCount; i += 2) {
                    IPv4 destination = staticRoutes.Values[i];
                    IPv4 gateway     = staticRoutes.Values[i + 1];
                    IPv4 ifAddress   = address.Value;
                    ip.HostConfiguration.RoutingTable.AddRoute(
                        new RouteEntry(destination, gateway, ifAddress,
                                       RouteEntry.DefaultRouteMetric, 0)
                        );
                }
            }

            activeDhcpOptions = dhcpOptions;
            return true;
        }

        internal void UninstallDhcpOptions()
        {
            // Back-out options
            IPModule ip = (IPModule!) Core.Instance().GetProtocolByName("IP");

            DhcpIPv4Option address = (DhcpIPv4Option!)
                activeDhcpOptions[DhcpRequestedIPAddress.OptionCode];

            IPv4 ifAddress = address.Value;

            //
            // Remove routes associated with interface address
            //
            ip.HostConfiguration.RoutingTable.DeleteInterfaceRoutes(ifAddress);

            //
            // Remove name server
            //
            DhcpMultiIPv4Option dnsServers =
                activeDhcpOptions[DhcpDomainNameServer.OptionCode]
                as DhcpMultiIPv4Option;
            if (dnsServers != null) {
                foreach (IPv4 server in dnsServers.Values) {
                    ip.HostConfiguration.AddNameServer(server);
                }
            }

            //
            // Leave domain name in place
            //

            // If we wanted to remove it...
            DhcpStringOption domain =
                activeDhcpOptions[DhcpDomainName.OptionCode]
                as DhcpStringOption;

            string domainName = ip.HostConfiguration.GetDomainName();
            if (domain != null && domainName == domain.Value) {
                ip.HostConfiguration.SetDomainName("");
            }

            //
            // Remove interface address bindings
            //
            ip.HostConfiguration.Bindings.Flush(adapter, ifAddress);

            activeDhcpOptions = null;
        }

        internal void StartNewTransaction()
        {
            transactionID++;
            transactionStart = DateTime.Now;
        }

        private void WorkerMain()
        {
            DebugPrint("Worker starting\n");

            Random r = new Random();
            transactionID = (uint)r.Next();

            DateTime startTime = DateTime.Now;

            // Enter "Init" state of FSM
            ChangeState(new DhcpClientStateInitialize(this));

            while (workerDone == false) {
                // Check for timeouts
                DateTime now = DateTime.Now;
                if (now >= renewalTimeout) {
                    CancelRenewalTimeout();
                    @state.RenewalTimeoutEvent();
                }
                if (now >= rebindTimeout) {
                    CancelRebindTimeout();
                    @state.RebindTimeoutEvent();
                }
                if (now >= stateTimeout) {
                    CancelStateTimeout();
                    @state.StateTimeoutEvent();
                }

                // Poll for data
                try {
                    byte [] data = udpSession.PollCopyData(PollInterval);
                    if (data != null) {
                        SimpleBuffer sb = new SimpleBuffer(data);
                        DhcpFormat dhcp = DhcpFormat.Parse(sb);

                        // Check transaction id is ours
                        if (dhcp.TransactionID != transactionID) {
                            continue;
                        }

                        // Check client address is ours
                        if (dhcp.GetHardwareAddress() != MacAddress) {
                            continue;
                        }

                        @state.ReceiveEvent(dhcp);
                    }
                }
                catch (InvalidDhcpFormatException idfe) {
                    DebugPrint(idfe.Message);
                }

                // XXX Temporary until process can run in background
                // from shell.  ie we'd like to run and renew lease
                // but shell blocks on running process and cleans up
                // after it for the time being.
                if (activeDhcpOptions != null) {
                    DebugPrint("Got options -- done\n");
                    break;
                }

                if (DateTime.Now - startTime > TimeSpan.FromSeconds(5)) {
                    DebugPrint("Timed out\n");
                    break;
                }
            }
        }

        internal void ResetAdapterIPInfo()
        {
        }

        internal bool Send(EthernetAddress dstAddr, DhcpFormat! dhcp)
        {
            int packetSize = dhcp.Size + UdpFormat.Size +
                IPFormat.Size + EthernetFormat.Size;

            byte [] packet = new byte [packetSize];

            // Write out DHCP packet
            int dhcpSize = dhcp.Size;
            int dhcpOffset = packet.Length - dhcpSize;
            dhcp.Write(packet, dhcpOffset);

            // Create UDP Header
            UdpFormat.UdpHeader udpHeader = new UdpFormat.UdpHeader();
            udpHeader.srcPort = DhcpFormat.ClientPort;
            udpHeader.dstPort = DhcpFormat.ServerPort;
            udpHeader.length  = (ushort)(UdpFormat.Size + dhcpSize);

            // Create IP Header
            IPFormat.IPHeader ipHeader = new NetStack.Protocols.IPFormat.IPHeader();
            ipHeader.SetDefaults(IPFormat.Protocol.UDP);
            IPFormat.SetDontFragBit(ipHeader);

            ipHeader.Source      = IPv4.Any;
            ipHeader.Destination = IPv4.Broadcast;
            ipHeader.totalLength = (ushort)(IPFormat.Size + UdpFormat.Size + dhcpSize);

            // Write out IP and Header
            int udpOffset = packet.Length - dhcp.Size - UdpFormat.Size;
            int ipOffset = udpOffset - IPFormat.Size;
            UdpFormat.WriteUdpPacket(packet, ipOffset,
                                     ipHeader, ref udpHeader,
                                     packet, dhcpOffset, dhcpSize);

            // Add Ethernet Header
            EthernetFormat.Write(packet, 0, adapter.HardwareAddress,
                                 dstAddr, EthernetFormat.PROTOCOL_IP);

            NetPacket np = new NetPacket(packet);
            return udpSession.WritePacket(np);
        }
    }
}
