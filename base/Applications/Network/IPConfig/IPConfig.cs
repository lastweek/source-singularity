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
    [ConsoleCategory(HelpMessage="Configure nic with IP addresses", DefaultAction=true)]
    internal class DefaultConfig {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<IPContract.Imp:Start> ipRef;

        [StringParameter( "device", Mandatory=true, Position=0, HelpMessage="Nic to configure")]
        internal string device;

        [StringParameter( "address", Mandatory=true, Position=1, HelpMessage="address to give it")]
        internal string address;

        [StringParameter( "mask", Mandatory=true, Position=2, HelpMessage="mask to use")]
        internal string mask;

        [StringParameter( "gateway", Mandatory=true, Position=3, HelpMessage="gateway")]
        internal string gateway;

        reflective internal DefaultConfig();

        internal int AppMain() {
            return IPConfig.DefaultMain(this);
        }
    }

    [ConsoleCategory(Action="show", HelpMessage="SHOW nic' IP configuration" )]
    internal class ShowConfig {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<IPContract.Imp:Start> ipRef;

        [Endpoint]
        public readonly TRef<DNSContract.Imp:Start> dnsRef;

        reflective internal ShowConfig();

        internal int AppMain() {
            return  IPConfig.Show(this);
        }
    }

    [ConsoleCategory(Action="dhcp", HelpMessage="Configure nic via DHCP" )]
    internal class DhcpConfig {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<IPContract.Imp:Start> ipRef;

        [StringParameter( "device", Mandatory=true, Position=0, HelpMessage="Nic to configure")]
        internal string device;

        [StringParameter( "verb", Mandatory=true, Position=1, HelpMessage="verb (start or stop).")]
        internal string action;

        reflective internal DhcpConfig();

        internal int AppMain() {
            return  IPConfig.Dhcp(this);
        }
    }

    [ConsoleCategory(Action="verify", HelpMessage="check device interface" )]
    internal class VerifyConfig {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<IPContract.Imp:Start> ipRef;

        [StringParameter( "device", Mandatory=true, Position=0, HelpMessage="Nic to configure")]
        internal string device;

        reflective internal VerifyConfig();

        internal int AppMain() {
            return  IPConfig.Verify(this);
        }
    }

    /// <summary>
    /// Class for interface configuration related commands.
    /// </summary>
    public class IPConfig
    {

        // Marked unsafe for now since checker 
        // has problems with custom vector access.
        public static void ShowConfig(IPContract.Imp:ReadyState! ipConn, DNSContract.Imp:ReadyState! dnsConn)
        {
            int done = 0;
            char[]! in ExHeap hostName, domainName;

            ipConn.SendGetHostName();
            ipConn.RecvHostName(out hostName);
            ipConn.SendGetDomainName();
            ipConn.RecvDomainName(out domainName);

            Console.WriteLine("Hostname: {0}.{1}", Bitter.ToString2(hostName), Bitter.ToString2(domainName));
            delete hostName;
            delete domainName;

            Console.WriteLine("DNS Servers:");

            try {
                Utils.DNSShow(dnsConn);
            }
            finally {
            }

            char[][]! in ExHeap ifNames;
            ipConn.SendGetInterfaces();
            ipConn.RecvInterfaceList(out ifNames);

            for (int i = 0; i < ifNames.Length; ++i) {
                CustomVector.Expose(ifNames, i);
                char[] in ExHeap ifName = ifNames[i];
                if (ifName == null)
                    throw new Exception("ifName is null");
                string! deviceName = Bitter.ToString2(ifName);
                CustomVector.UnExpose(ifNames, i);
                ipConn.SendGetInterfaceState(Bitter.FromString2(deviceName));
                switch receive {
                    case ipConn.InterfaceNotFound() :
                        Console.WriteLine("Unexpected error");
                        break;

                    case ipConn.InterfaceState(InterfaceInfo ifInfo) :
                        ShowInterface(ifInfo, deviceName);
                        break;

                    case ipConn.ChannelClosed() :
                        throw new Exception("ipConn channel closed");
                }

                done++;
            }

            delete ifNames;

            if (done == 0)
                Console.WriteLine("No adapters present.");
        }

        public static void ConfigureInterface(IPContract.Imp!   ipConn,
                                              string!           adapterName,
                                              string!           addressString,
                                              string!           netmaskString,
                                              string!           gatewayString)
        {
            IPv4 ifAddress, netmask, gateway;

            if (IPv4.Parse(addressString, out ifAddress) == false ||
                IPv4.Parse(netmaskString, out netmask) == false ||
                IPv4.Parse(gatewayString, out gateway) == false)
            {
                return;
            }

            ipConn.SendSetInterfaceState(Bitter.FromString2(adapterName),
                                         (uint)ifAddress, (uint)netmask, (uint)gateway);

            switch receive {
                case ipConn.InterfaceNotFound() :
                    Console.WriteLine("No such interface found");
                    break;

                case ipConn.Err() :
                    Console.WriteLine("Error occurred setting interface state");
                    break;

                case ipConn.OK() :
                    Console.WriteLine("Successfully set interface state");
                    break;
            }
        }

        public static void ShowInterface([Claims] InterfaceInfo ifInfo, string! ifName)
        {
            Console.WriteLine("Interface:   {0}", ifName);
            Console.WriteLine("Adapter:     {0}",
                              Bitter.ToString(ifInfo.driverName));
            Console.WriteLine("Version:     {0}",
                              Bitter.ToString(ifInfo.driverVersion));
            Console.WriteLine("MAC address: {0}",
                              ChannelUtils.HardwareAddressToString(ifInfo.hardwareAddress));

            bool found = false;

            delete ifInfo.driverName;
            delete ifInfo.driverVersion;

            InterfaceIPInfo[] in ExHeap ipConfigs = ifInfo.ipConfigs;

            if (ipConfigs != null) {
                for (int i = 0; i < ipConfigs.Length; i++) {
                    InterfaceIPInfo ipc = ipConfigs[i];
                    Console.WriteLine("   Address: {0,-14}    NetMask: {1, -14}    Gateway: {2, -14}", new IPv4(ipc.address), new IPv4(ipc.netmask), new IPv4(ipc.gateway));
                    found |= true;
                }
                delete ipConfigs;
            }

            if (found == false)
                Console.WriteLine("   Not configured.");
        }

        public static void StartDhcp(IPContract.Imp! ipConn,
                                     string! adapterName)
        {
            ipConn.SendStartDhcp(Bitter.FromString2(adapterName));

            switch receive {
                case ipConn.InterfaceNotFound() :
                    Console.WriteLine("No such interface found");
                    break;

                case ipConn.OK() :
                    Console.WriteLine("Successfully started DHCP");
                    break;
            }
        }

        public static void StopDhcp(IPContract.Imp! ipConn,
                                    string! adapterName)
        {
            ipConn.SendStopDhcp(Bitter.FromString2(adapterName));

            switch receive {
                case ipConn.InterfaceNotFound() :
                    Console.WriteLine("No such interface found");
                    break;

                case ipConn.OK() :
                    Console.WriteLine("Successfully stopped DHCP");
                    break;
            }
        }

        internal static int Show(ShowConfig! config) 
        {
            IPContract.Imp ipConn = ((!)config.ipRef).Acquire();
            if (ipConn == null) { 
                throw new Exception("Unable to acquire handle to the IP network"); 
            } 
            ipConn.RecvReady(); 
            
            DNSContract.Imp dnsConn = ((!)config.dnsRef).Acquire();
            if (dnsConn == null) {
                Console.WriteLine("Could not initialize DNS endpoint.");
                delete ipConn;
                return -1;
            }
            dnsConn.RecvReady(); 

            ShowConfig(ipConn, dnsConn);
            delete ipConn;
            delete dnsConn;
            return 0; 
        }


        internal static int Dhcp(DhcpConfig! config) 
        {
            IPContract.Imp ipConn = ((!)config.ipRef).Acquire();
            if (ipConn == null) { 
                throw new Exception("Unable to acquire handle to the IP network"); 
            } 
            ipConn.RecvReady(); 

            if (config.action == "start") {
                StartDhcp(ipConn, (!)config.device);
            } 
            else if (config.action == "stop") {
                StopDhcp(ipConn, (!)config.device);
            } 
            else {
                Console.WriteLine("Unknown dhcp action:{0}", config.action); 
            }
            delete ipConn;
            return 0; 
        }
        
        internal static int Verify(VerifyConfig! config) 
        {
            string! arg1 = (!)config.device; 
            
            IPContract.Imp ipConn = ((!)config.ipRef).Acquire();
            if (ipConn == null) { 
                throw new Exception("Unable to acquire handle to the IP network"); 
            } 
            ipConn.RecvReady(); 
            ipConn.SendGetInterfaceState(Bitter.FromString2(arg1));

            switch receive {
                case ipConn.InterfaceNotFound() :
                    Console.WriteLine("Interface not found: \"" + arg1 + "\"");
                    break;

                case ipConn.InterfaceState(InterfaceInfo ifInfo) :
                    ShowInterface(ifInfo, arg1);
                    break;

                case ipConn.ChannelClosed() :
                    throw new Exception("ipConn channel closed");
            }
            delete ipConn;
            return 0;
        }
        
        internal static int DefaultMain(DefaultConfig! config)
        {

            IPContract.Imp ipConn = ((!)config.ipRef).Acquire();
            if (ipConn == null) { 
                throw new Exception("Unable to acquire handle to the IP network"); 
            } 
            ipConn.RecvReady(); 
            
            try {
                ConfigureInterface(ipConn,
                                    (!)config.device, 
                                    (!)config.address,
                                    (!)config.mask, 
                                    (!)config.gateway);
                delete ipConn;
                return 0;
            }
            catch (Exception e) {
                Console.WriteLine("Caught exception: " + e);
            }
            finally {
            }
            delete ipConn;
            return 1;
        }
    } // end class IPConfig
}
