///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: TestDhcpClient.cs
//

using NetStack.Common;
using System;
using System.Threading;
using System.Collections;

using System.Net.IP;
using Drivers.Net;
using NetStack.Protocols;
using NetStack.NetDrivers;

namespace NetStack.Runtime.TestDhcpClient
{
    public class FakeDhcpServer : IDebugAdapterClient
    {
#region Constants
        public enum ServerState : byte
        {
            Running  = 1,
            Failed   = 2,
            Finished = 3
        };

        private const int NonDhcpHeaderSize =
            EthernetFormat.Size + IPFormat.Size + UdpFormat.Size;

        private readonly EthernetAddress ServerMac =
            EthernetAddress.Parse("00:50:f2:fe:dc:0d");

        private readonly IPv4 ServerAddress = IPv4.Parse("10.0.0.99");
        private readonly IPv4 HostAddress   = IPv4.Parse("10.0.0.100");
        private readonly IPv4 NetMask       = IPv4.NetMask(19);
        private readonly IPv4 [] Routers    = {
            IPv4.Parse("10.0.0.1")
        };
        private readonly IPv4 [] DnsServers = {
            IPv4.Parse("10.0.0.10"),
            IPv4.Parse("10.0.1.10")
            };
        private const uint RenewalTime   = 20;
        private const uint RebindingTime = 40;

        private readonly String DomainName = "microsoft.com";

        //
        // <Expect,Action> pairings.
        //
        // NB If action is not a DHCP Response, no response should be sent.
        //
        private DhcpFormat.MessageType [,] expectActions =
        {
            // Expect Discover and do nothing with it.
            { DhcpFormat.MessageType.Discover,
              DhcpFormat.MessageType.Discover },

            // Expect Discover and make an offer
            { DhcpFormat.MessageType.Discover,
              DhcpFormat.MessageType.Offer },

            // Expect request then cruelly reject it
            { DhcpFormat.MessageType.Request,
              DhcpFormat.MessageType.Nak },

            // Expect Discover and make another offer
            { DhcpFormat.MessageType.Discover,
              DhcpFormat.MessageType.Offer },

            // Expect request and fickly accept
            { DhcpFormat.MessageType.Request,
              DhcpFormat.MessageType.Ack },

            // Live happily ever after
        };
#endregion Constants

#region InstanceState
        private DebugAdapter adapter;
        private ServerState state;
        private IPv4 assignedAddress = IPv4.Zero;
        private int expectIndex = 0;
#endregion InstanceState

        public ServerState State
        {
            get { return state; }
        }

        private void SetState(ServerState newState)
        {
            state = newState;
        }

        public void RegisterAdapter(DebugAdapter adapter)
        {
            this.adapter = adapter;
        }

        /// <summary>
        /// Check Ethernet, IP, and UDP headers match those expected.
        /// </summary>
        private bool ValidHeaders(NetPacket packet)
        {
            if (packet.Length < NonDhcpHeaderSize) {
                Console.WriteLine("Packet too short");
                return false;
            }

            //
            // Check EthernetHeader
            //
            EthernetAddress originMac;
            EthernetAddress targetMac;
            EthernetFormat.Protocol protocol;

            EthernetFormat.Read(packet,
                                out originMac, out targetMac, out protocol);
            if (originMac != adapter.HardwareAddress) {
                Console.WriteLine("Bad origin mac: {0}", originMac);
                return false;
            }
            else if (targetMac != EthernetAddress.Broadcast &&
                     targetMac != ServerMac)
            {
                Console.WriteLine("Bad target mac: {0}", targetMac);
                return false;
            }
            else if (protocol != EthernetFormat.Protocol.IP) {
                Console.WriteLine("Bad encapsulated protocol: {0}", protocol);
                return false;
            }

            //
            // Check IP Header
            //
            IPFormat.IPHeader ipHeader;
            if (IPFormat.ReadIPHeader(packet, out ipHeader) == false) {
                Console.WriteLine("Failed to read IP Header");
                return false;
            }
            else if (ipHeader.Protocol != IPFormat.Protocol.UDP) {
                Console.WriteLine("Bad encapsulated IP protocol: {0}",
                                  ipHeader.Protocol);
                return false;
            }
            else if (ipHeader.Source != IPv4.Zero &&
                     ipHeader.Source != assignedAddress)
            {
                Console.WriteLine("Bad IP source address: {0}",
                                  ipHeader.Source);
                return false;
            }
            else if (ipHeader.Destination != IPv4.AllOnes &&
                     ipHeader.Destination != ServerAddress)
            {
                Console.WriteLine("Bad IP destination address: {0}",
                                  ipHeader.Destination);
                return false;
            }

            Console.WriteLine("{0} {1}",
                              ipHeader.Source, ipHeader.Destination);

            //
            // Check UDP Header
            //
            UdpFormat.UdpHeader udpHeader;
            if (UdpFormat.ReadUdpHeader(packet, out udpHeader) == false) {
                Console.WriteLine("Failed to read UDP Header");
                return false;
            }
            else if (udpHeader.srcPort != 68) {
                Console.WriteLine("Bad UDP source port: {0}",
                                  udpHeader.srcPort);
                return false;
            }
            else if (udpHeader.dstPort != 67) {
                Console.WriteLine("Bad UDP destination port: {0}",
                                  udpHeader.dstPort);
                return false;
            }

            return true;
        }

        public void Receive(NetPacket packet)
        {
            packet.Reset();

            Console.WriteLine("Received {0} bytes", packet.Length);
            if (ValidHeaders(packet) == false) {
                SetState(ServerState.Failed);
                return;
            }

            try {
                DhcpFormat dhcp = DhcpFormat.Parse(packet);
                SortedList options = dhcp.GetOptions();

                DhcpByteOption message = options[DhcpMessageType.OptionCode]
                    as DhcpByteOption;
                if (message == null) {
                    Console.WriteLine("MessageType option not found");
                    SetState(ServerState.Failed);
                    return;
                }

                DhcpFormat.MessageType messageType =
                    (DhcpFormat.MessageType) message.Value;

                if (DhcpFormat.IsRequestMessage(messageType) == false) {
                    Console.WriteLine("Inappropriate message type: {0}",
                                      message.Value);
                    SetState(ServerState.Failed);
                    return;
                }

                DhcpFormat.MessageType expected = expectActions[expectIndex,0];
                DhcpFormat.MessageType action = expectActions[expectIndex,1];
                expectIndex++;

                if (messageType != expected) {
                    Console.WriteLine("Unexpected message type: {0} != {1}",
                                      messageType, expected);
                    SetState(ServerState.Failed);
                    return;
                }

                if (DhcpFormat.IsResponseMessage(action)) {
                    Respond(dhcp, action);
                }

                if (expectIndex == expectActions.Length / expectActions.Rank) {
                    SetState(ServerState.Finished);
                }
            }
            catch (Exception e) {
                Console.WriteLine("Bad Dhcp packet: {0}", e);
                SetState(ServerState.Failed);
            }
        }

        private void FillOptions(DhcpFormat request, DhcpFormat response)
        {
            SortedList requestOptions = request.GetOptions();

            response.AddOption(DhcpServerID.Create(ServerAddress));
            response.AddOption(DhcpRenewalTime.Create(RenewalTime));
            response.AddOption(DhcpRebindingTime.Create(RebindingTime));

            foreach (IDhcpOption option in requestOptions.Values) {
                byte optionCode = option.OptionCode;
                Console.WriteLine("({0}) {1}",
                                  optionCode,
                                  DhcpOptionParser.GetOptionName(optionCode));
            }

            DhcpMultiByteOption parameters =
                requestOptions[DhcpParameterRequest.OptionCode]
                as DhcpMultiByteOption;

            if (parameters == null)
                return;

            foreach (byte parameter in parameters.Values) {
                switch (parameter) {
                    case DhcpSubnetMask.OptionCode:
                        response.AddOption(DhcpSubnetMask.Create(NetMask));
                        break;
                    case DhcpDomainName.OptionCode:
                        response.AddOption(
                            DhcpDomainName.Create(DomainName.ToCharArray())
                            );
                        break;
                    case DhcpRouter.OptionCode:
                        response.AddOption(DhcpRouter.Create(Routers));
                        break;
                    case DhcpDomainNameServer.OptionCode:
                        response.AddOption(
                            DhcpDomainNameServer.Create(DnsServers)
                            );
                        break;
                }
            }
        }

        private void Respond(DhcpFormat request, DhcpFormat.MessageType m)
        {
            DhcpFormat response    = new DhcpFormat(m);

            response.TransactionID = request.TransactionID;

            EthernetAddress hwAddress = request.GetHardwareAddress();
            response.SetHardwareAddress(hwAddress);

            switch (m) {
                case DhcpFormat.MessageType.Offer:
                    response.NextServerIPAddress = ServerAddress;
                    response.AddOption(
                        DhcpIPAddressLeaseTime.Create(RebindingTime)
                        );
                    goto case DhcpFormat.MessageType.Ack;
                case DhcpFormat.MessageType.Ack:
                    response.YourIPAddress = HostAddress;
                    assignedAddress = HostAddress;
                    FillOptions(request, response);
                    break;
                case DhcpFormat.MessageType.Nak:
                    // Nothing to do
                    break;
                default:
                    return;
            }
            SendResponsePacket(response);
        }

        private void SendResponsePacket(DhcpFormat dhcp)
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
            udpHeader.srcPort = DhcpFormat.ServerPort;
            udpHeader.dstPort = DhcpFormat.ClientPort;
            udpHeader.length  = (ushort)(UdpFormat.Size + dhcpSize);

            // Create IP Header
            IPFormat.IPHeader ipHeader = new NetStack.Protocols.IPFormat.IPHeader();
            ipHeader.SetDefaults(IPFormat.Protocol.UDP);
            IPFormat.SetDontFragBit(ipHeader);

            ipHeader.Source      = ServerAddress;
            ipHeader.Destination = IPv4.Broadcast;
            ipHeader.totalLength = (ushort)(IPFormat.Size + UdpFormat.Size + dhcpSize);

            // Write out IP and Header
            int udpOffset = packet.Length - dhcp.Size - UdpFormat.Size;
            int ipOffset = udpOffset - IPFormat.Size;
            UdpFormat.WriteUdpPacket(packet, ipOffset,
                                     ref ipHeader, ref udpHeader,
                                     packet, dhcpOffset, dhcpSize);

            // Add Ethernet Header
            EthernetFormat.Write(packet, 0, ServerMac,
                                 EthernetAddress.Broadcast,
                                 EthernetFormat.Protocol.IP);

            NetPacket np = new NetPacket(packet);
            if (adapter.ReceivePacket(np) == false) {
                Console.WriteLine("Failed to send packet");
                SetState(ServerState.Failed);
            }
        }
    }

    public class Test
    {
        static int Main()
        {
            StaticConfiguration.Initialize();
            StaticConfiguration.Start();

            FakeDhcpServer fakeDhcpServer = new FakeDhcpServer();
            DebugAdapter adapter = new DebugAdapter(fakeDhcpServer);
            Console.WriteLine("Created Debug Adapter {0}",
                              adapter.HardwareAddress);
            Core.Instance().RegisterAdapter(adapter, 64);

            DhcpClient dc = new DhcpClient(adapter);
            dc.Start();

            while (fakeDhcpServer.State == FakeDhcpServer.ServerState.Running) {
                Thread.Sleep(TimeSpan.FromSeconds(1));
            }
            dc.Stop();

            Console.WriteLine("Removing Adapter.");
            Core.Instance().DeregisterAdapter(adapter);

            StaticConfiguration.Stop();

            if (fakeDhcpServer.State == FakeDhcpServer.ServerState.Failed) {
                return 1;
            }
            return 0;
        }
    }
}
