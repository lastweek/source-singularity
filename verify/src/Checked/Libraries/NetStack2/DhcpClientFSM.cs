///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Netstack / Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DhcpClientFSM.cs
//
//  Description:   DHCP Client Finite State machine.
//
//  Note: This file does not yet implement the RENEWING or
//        REBINDING states.

using Microsoft.Singularity;
using System;
using System.Diagnostics;
using System.Collections;

using System.Net.IP;
using Drivers.Net;

namespace Microsoft.Singularity.NetStack2
{
    using Protocols;

    class DhcpClientState
    {
        protected DhcpClient client;
        protected string     stateName;

        internal DhcpClientState(DhcpClient client, string stateName)
        {
            this.client    = client;
            this.stateName = stateName;
        }

        internal string Name
        {
            get { return stateName; }
        }

        /// <summary>
        /// State should perform processing as DhcpClient recognizes it
        /// as the currently active event.
        /// </summary>
        internal virtual void EnterEvent()
        {
            //DebugStub.WriteLine("Entering State {0}\n", DebugStub.ArgList(stateName));
        }

        /// <summary>
        /// State should process that has arrived.
        /// </summary>
        internal virtual void ReceiveEvent(DhcpFormat df)
        {
            //DebugStub.WriteLine("FSM Ignored DHCP packet: {0}\n", DebugStub.ArgList(stateName));
        }

        /// <summary>
        /// Renewal timer expiry event.
        /// </summary>
        internal virtual void RenewalTimeoutEvent()
        {
            //DebugStub.WriteLine("FSM Renewal Timeout: {0}\n", DebugStub.ArgList(stateName));
        }

        /// <summary>
        /// Rebind timer expiry event.
        /// </summary>
        internal virtual void RebindTimeoutEvent()
        {
            //DebugStub.WriteLine("FSM Rebind Timeout: {0}\n", DebugStub.ArgList(stateName));
        }

        /// <summary>
        /// General purpose timer expiry event.
        /// </summary>
        internal virtual void StateTimeoutEvent()
        {
            //DebugStub.WriteLine("FSM State Specific Timeout: {0}\n",
            //                    DebugStub.ArgList(stateName));
        }
    };

    internal class DhcpClientStateInitialize : DhcpClientState
    {
        internal DhcpClientStateInitialize(DhcpClient client)
            : base(client, "Initialize")
        {
        }

        internal override void EnterEvent()
        {
            client.StartNewTransaction();

            DhcpFormat dhcp =
                new DhcpFormat(DhcpFormat.MessageType.Discover);

            dhcp.TransactionID = client.TransactionID;
            dhcp.SetHardwareAddress(client.MacAddress);

#if ADVERTISE_CLIENT_ID
            // Add Client Identifier for self
            //
            // [2006-02-03 ohodson] This is disabled because the Windows
            // DHCP server allocates us a different address with the
            // client id present if we networked booted.  Thus having the
            // identifier breaks static DHCP entries which we use
            // for test machines.
            EthernetAddress macAddress = client.MacAddress;
            dhcp.AddOption(DhcpClientID.Create(macAddress.GetAddressBytes()));
#endif

            // Add parameters we'd like to know about
            dhcp.AddOption(DhcpParameterRequest.Create(
                               DhcpClient.StandardRequestParameters
                               )
                           );
            // dhcp.AddOption(DhcpAutoConfigure.Create(0));
            client.Send(EthernetAddress.Broadcast, dhcp);
            client.ChangeState(new DhcpClientStateSelecting(client));
        }
    }

    internal class DhcpClientStateSelecting : DhcpClientState
    {
        private readonly TimeSpan StateTimeout = TimeSpan.FromSeconds(5);

        internal DhcpClientStateSelecting(DhcpClient client)
            : base(client, "Selecting")
        {
        }

        internal override void EnterEvent()
        {
            client.SetStateTimeout(DateTime.Now + StateTimeout);
        }

        internal override void StateTimeoutEvent()
        {
            // Received no valid offers
            client.ChangeState(new DhcpClientStateInitialize(client));
        }

        internal override void ReceiveEvent(DhcpFormat dhcp)
        {
            //DebugStub.WriteLine("FSM DHCP packet SELECTING.\n");

            // Check if message is in response to our request
            if (dhcp.BootMessageType != DhcpFormat.BootType.Reply   ||
                dhcp.TransactionID != client.TransactionID          ||
                dhcp.GetHardwareAddress() != client.MacAddress) {
                DebugStub.WriteLine("FSM DHCP bad id.\n");
                return;
            }

            IPv4 serverAddress = dhcp.NextServerIPAddress;

            // Check if offered address is valid (ie not zero
            // and below class E)
            IPv4 offeredAddress = dhcp.YourIPAddress;
            if (offeredAddress == IPv4.Any || offeredAddress.IsMulticast()) {
                DebugStub.WriteLine("FSM DHCP multicast addr.\n");
                return;
            }

            // Check if message is an offer
            SortedList offeredOptions = dhcp.GetOptions();
            DhcpByteOption messageType
                = offeredOptions[DhcpMessageType.OptionCode] as DhcpByteOption;
            if (messageType == null ||
                messageType.Value != (byte)DhcpFormat.MessageType.Offer) {
                DebugStub.WriteLine("FSM DHCP not an offer.\n");
                return;
            }

            // Must have parameters
            byte [] parameters = new byte [] {
                DhcpSubnetMask.OptionCode,
                DhcpRouter.OptionCode,
                // DhcpDomainNameServer.OptionCode
            };

            foreach (byte p in parameters) {
                IDhcpOption ido = offeredOptions[p] as IDhcpOption;
                if (ido == null) {
                    DebugStub.WriteLine("FSM DHCP missing option 0x{0:x2}.\n", DebugStub.ArgList(p));
                    return;
                }
            }

            client.CancelStateTimeout();
            client.ChangeState(new DhcpClientStateRequesting(client,
                                                             serverAddress,
                                                             offeredAddress,
                                                             offeredOptions));
        }
    }

    internal class DhcpClientStateRequesting : DhcpClientState
    {
        IPv4       serverAddress;
        IPv4       offeredAddress;
        SortedList offeredOptions;

        private readonly TimeSpan StateTimeout = TimeSpan.FromSeconds(5);

        internal DhcpClientStateRequesting(DhcpClient client,
                                           IPv4       serverAddress,
                                           IPv4       offeredAddress,
                                           SortedList offeredOptions)
            : base(client, "Requesting")
        {
            this.serverAddress  = serverAddress;
            this.offeredAddress = offeredAddress;
            this.offeredOptions = offeredOptions;
        }

        internal override void EnterEvent()
        {
            client.SetStateTimeout(DateTime.Now + StateTimeout);

            DhcpFormat dhcp =
                new DhcpFormat(DhcpFormat.MessageType.Request);

            dhcp.TransactionID      = client.TransactionID;
            dhcp.TransactionSeconds = client.TransactionSeconds;
            dhcp.SetHardwareAddress(client.MacAddress);
#if ADVERTISE_CLIENT_ID
            dhcp.AddOption(
                DhcpClientID.Create(client.MacAddress.GetAddressBytes())
                );
#endif
            dhcp.AddOption(
                DhcpRequestedIPAddress.Create(offeredAddress)
                );

            // Add parameters we'd like to know about
            dhcp.AddOption(DhcpParameterRequest.Create(
                               DhcpClient.StandardRequestParameters
                               )
                           );

            client.Send(EthernetAddress.Broadcast, dhcp);
        }

        private static void TakeOption(SortedList offeredOptions,
                                       byte        optionCode,
                                       DhcpFormat dhcpFormat)
        {
            IDhcpOption option = offeredOptions[optionCode] as IDhcpOption;
            if (option != null) {
                dhcpFormat.AddOption(option);
            }
        }

        internal override void StateTimeoutEvent()
        {
            client.ChangeState(new DhcpClientStateInitialize(client));
        }

        internal override void ReceiveEvent(DhcpFormat dhcp)
        {
            //DebugStub.WriteLine("FSM DHCP packet REQUESTING.\n");

            // Check if message is in response to our request
            if (dhcp.BootMessageType != DhcpFormat.BootType.Reply   ||
                dhcp.TransactionID != client.TransactionID          ||
                dhcp.GetHardwareAddress() != client.MacAddress) {
                return;
            }

            IPv4 serverAddress = dhcp.NextServerIPAddress;

            // Check if offered address is valid (ie not zero
            // and below class E)
            IPv4 offeredAddress = dhcp.YourIPAddress;
            if (offeredAddress == IPv4.Any || offeredAddress.IsMulticast()) {
                return;
            }

            // Check if message is an ack
            SortedList offeredOptions = dhcp.GetOptions();
            DhcpByteOption messageType
                = offeredOptions[DhcpMessageType.OptionCode] as DhcpByteOption;
            if (messageType == null) {
                return;
            }

            switch (messageType.Value) {
                case (byte) DhcpFormat.MessageType.Ack:
                    break;
                case (byte) DhcpFormat.MessageType.Nak:
                    client.ChangeState(new DhcpClientStateInitialize(client));
                    return;
                default:
                    return;
            }

            // Must have parameters
            byte [] parameters = new byte [] {
                DhcpSubnetMask.OptionCode,
                DhcpRouter.OptionCode,
                // DhcpDomainNameServer.OptionCode
            };

            foreach (byte p in parameters) {
                IDhcpOption ido = offeredOptions[p] as IDhcpOption;
                if (ido == null) {
                    return;
                }
            }

            client.CancelStateTimeout();
            client.ChangeState(new DhcpClientStateBound(client,
                                                        serverAddress,
                                                        offeredAddress,
                                                        offeredOptions));
        }
    }

    internal class DhcpClientStateBound : DhcpClientState
    {
        private IPv4       serverAddress;
        private IPv4       hostAddress;
        private SortedList hostOptions;

        internal DhcpClientStateBound(DhcpClient client,
                                      IPv4       serverAddress,
                                      IPv4       hostAddress,
                                      SortedList hostOptions)
            : base(client, "Bound")
        {
            this.serverAddress = serverAddress;
            this.hostAddress   = hostAddress;
            this.hostOptions   = hostOptions;
        }

        internal override void EnterEvent()
        {
            // Yay! We got DHCP configuration information
            DateTime now = DateTime.Now;

            // Set up renewal timer
            DhcpDWordOption renewalOption =
                hostOptions[DhcpRenewalTime.OptionCode] as DhcpDWordOption;

            uint renewalSeconds = 3600;
            if (renewalOption != null) {
                renewalSeconds = renewalOption.Value;
            }
            client.SetRenewalTimeout(now + TimeSpan.FromSeconds(renewalSeconds));

            // Set up rebinding timer
            DhcpDWordOption rebindOption =
                hostOptions[DhcpRebindingTime.OptionCode] as DhcpDWordOption;
            uint rebindSeconds = renewalSeconds + 60;
            if (rebindOption != null) {
                rebindSeconds = Math.Max(rebindOption.Value,
                                         renewalSeconds + 1);
            }
            client.SetRebindTimeout(now + TimeSpan.FromSeconds(rebindSeconds));

            // Add host address as a dhcp option and then get client
            // to install settings.
            hostOptions[DhcpRequestedIPAddress.OptionCode] =
                DhcpRequestedIPAddress.Create(hostAddress);

            if (client.InstallDhcpOptions(hostOptions) == false) {
                client.ChangeState(new DhcpClientStateInitialize(client));
            }
            DebugStub.Print("DHCP client acquired lease of " + hostAddress + " for " + rebindSeconds + " seconds. ");
        }

        internal override void ReceiveEvent(DhcpFormat dhcp)
        {
            //DebugStub.WriteLine("FSM DHCP packet BOUND.\n");
            // ignore
        }

        internal override void RenewalTimeoutEvent()
        {
#if NOTYET
            client.ChangeState(new DhcpClientStateRenewing(client,
                                                           hostOptions));
#endif
        }
    }

    internal class DhcpClientStateRenewing : DhcpClientState
    {
        SortedList hostOptions;

        internal DhcpClientStateRenewing(DhcpClient client,
                                         SortedList hostOptions)
            : base(client, "Renewing")
        {
            this.hostOptions = hostOptions;
        }

        internal override void EnterEvent()
        {
        }

        internal override void ReceiveEvent(DhcpFormat dhcp)
        {
            //DebugStub.WriteLine("FSM DHCP packet RENEWING.\n");
            // ignore
        }

        internal override void RebindTimeoutEvent()
        {
            // NB We use Debug.Assert here rather than Debug.Fail
            // as Singularity doesn't support the latter.
            Debug.Assert(false, "Rebind timeout in renewal state");
        }
    }

    internal class DhcpClientStateRebinding : DhcpClientState
    {
        internal DhcpClientStateRebinding(DhcpClient client)
            : base(client, "Rebinding")
        {
        }

        internal override void EnterEvent()
        {

        }

        internal override void ReceiveEvent(DhcpFormat dhcp)
        {
            //DebugStub.WriteLine("FSM DHCP packet REBINDING.\n");
        }

        internal override void RebindTimeoutEvent()
        {
        }
    }
}
