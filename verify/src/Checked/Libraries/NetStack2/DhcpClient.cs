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

using System;
using System.Collections;
using System.Diagnostics;
using System.Threading;

using System.Net.IP;
using Drivers.Net;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.SingSharp;

namespace Microsoft.Singularity.NetStack2
{
    /// <summary>
    /// A DhcpClient acts as a DHCP Client on a particular interface.
    ///
    /// The implementation is based on RFC2131.
    /// </summary>
    public class DhcpClient: IThreadStart
    {
        private IAdapter        adapter;
        private UDP             udp;
        private Thread          workerThread;
        private bool            workerDone;
        private ManualResetEvent workerDoneEvent;
        private DhcpClientState @state;
        private SortedList      activeDhcpOptions;

        private DateTime    renewalTimeout;
        private DateTime    rebindTimeout;
        private DateTime    stateTimeout;
        private DateTime    transactionStart;
        private uint        transactionID;
        private MonitorLock thisLock = new MonitorLock();

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
            DebugStub.Print("DhcpClient: {0}",
                            DebugStub.ArgList(
                                string.Format(format, args))
                            );

        }

        [Conditional("DEBUG_DHCP_CLIENT")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print("DhcpClient: {0}",
                            DebugStub.ArgList(format));
        }


        public DhcpClient(IAdapter adapter)
        {
            this.adapter = adapter;
            transactionID = (uint) INucleusCalls.Rdtsc();
            //TODO: transactionID = (uint)(new Random()).Next();
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
                return (ushort)(delta.Ticks >> 23); //TODO (but using .Seconds is dubious anyway): (ushort)delta.Seconds;
            }
        }

        public uint TransactionID
        {
            get { return transactionID; }
        }

        public bool Start()
        {
            using (thisLock.Lock()) {
                if (udp != null) {
                    return false;
                }
                udp = new UDP();
                udp.Bind(IPv4.Any, DhcpFormat.ClientPort);
                udp.Connect(IPv4.Broadcast, DhcpFormat.ServerPort);

                ResetAdapterIPInfo();

                workerDone = false;
                workerThread = new Thread(this);
                workerThread.Start();
                return true;
            }
        }

        public void Run()
        {
            System.DebugStub.Print("DhcpClient@" + Kernel.CurrentThread + ". ");
            workerDoneEvent = new ManualResetEvent();
            WorkerMain();
            workerDoneEvent.Set();
        }

        public void Stop()
        {
            using (thisLock.Lock()) {
                workerDone = true;
                workerDoneEvent.WaitOne();

                udp.Close();
                udp = null;
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
            VTable.Assert(newState != null);
            @state = newState;
            newState.EnterEvent();
            DebugPrint("ChangeState -> {0}\n", newState.Name);
        }

        internal bool InstallDhcpOptions(SortedList dhcpOptions)
        {
            if (activeDhcpOptions != null)
                UninstallDhcpOptions();

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

            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            hostConfiguration.Bindings.Add(
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
                hostConfiguration.SetDomainName(domain.Value);
            }

            //
            // Add DNS servers
            //
            DhcpMultiIPv4Option dnsServers =
                dhcpOptions[DhcpDomainNameServer.OptionCode]
                as DhcpMultiIPv4Option;
            if (dnsServers != null) {
                foreach (IPv4 server in dnsServers.Values) {
                    hostConfiguration.AddNameServer(server);
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
                    hostConfiguration.RoutingTable.AddRoute(
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

            DhcpIPv4Option address = (DhcpIPv4Option)
                activeDhcpOptions[DhcpRequestedIPAddress.OptionCode];

            IPv4 ifAddress = address.Value;

            //
            // Remove routes associated with interface address
            //
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            hostConfiguration.RoutingTable.DeleteInterfaceRoutes(ifAddress);

            //
            // Remove name server
            //
            DhcpMultiIPv4Option dnsServers =
                activeDhcpOptions[DhcpDomainNameServer.OptionCode]
                as DhcpMultiIPv4Option;
            if (dnsServers != null) {
                foreach (IPv4 server in dnsServers.Values) {
                    hostConfiguration.AddNameServer(server);
                }
            }

            //
            // Leave domain name in place
            //

            // If we wanted to remove it...
            DhcpStringOption domain =
                activeDhcpOptions[DhcpDomainName.OptionCode]
                as DhcpStringOption;

            string domainName = hostConfiguration.GetDomainName();
            if (domain != null && domainName == domain.Value) {
                hostConfiguration.SetDomainName("");
            }

            //
            // Remove interface address bindings
            //
            hostConfiguration.Bindings.Flush(adapter, ifAddress);

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

            //TODO: Random r = new Random();
            //TODO: transactionID = (uint)r.Next();
            transactionID = (uint) INucleusCalls.Rdtsc();
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
                    Bytes data = udp.PollReadData(PollInterval);
                    if (data != null) {
                        DhcpFormat dhcp = DhcpFormat.Parse(data);
                        //delete data;
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

        internal bool Send(EthernetAddress dstAddr, DhcpFormat dhcp)
        {
            int packetSize = dhcp.Size;
            int headerSize = EthernetHeader.Size + UDPHeader.Size + IpHeader.Size;
            Bytes packet = new Bytes(new byte [packetSize]);
            Bytes header = new Bytes(new byte [headerSize]);
            // Write out DHCP packet
            dhcp.Write(packet, 0);
            //the correct ports/addresses should already be bound up in instance of the UDP object
            udp.WriteCompleteUDPHeader(header, packet, dhcp.Size);
            // Add Ethernet Header
            EthernetHeader.Write(header,  adapter.HardwareAddress,
                                 dstAddr, EthernetHeader.PROTOCOL_IP);
            adapter.PopulateTxRing(header, packet);
            return true;
        }
    }
}
