///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IPContract.gs
//  Author: maiken
//  Note:   Provider-side helper for the IP Channel Contract
//

using System;
using System.Threading;
using System.Net.IP;
using Drivers.Net;
using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.NetStack;
using System.Collections;
using InterfaceInfo = Microsoft.Singularity.NetStack.InterfaceInfo;

namespace Microsoft.Singularity.NetStack2.Channels.Private
{
    public class IPContract
    {
        public IPContract()
        {
        }

        public String GetDomainName()
        {
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            return hostConfiguration.GetDomainName();
        }

        public void SetDomainName(String name)
        {
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            bool success = hostConfiguration.SetDomainName(name);

            if (!success) {
                throw new Exception("SetDomainName");
            }
        }

        public String GetHostName()
        {
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            return hostConfiguration.GetHostName();
        }

        public void SetHostName(String name)
        {
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            bool success = hostConfiguration.SetHostName(name);

            if (!success) {
                throw new Exception("SetHostName");
            }
        }

        public void StartDhcp(String ifName)
        {
            IAdapter intf = FindAdapter(ifName);

            if (intf == null) {
                throw new Exception("StartDhcp");
            }
            else {
                HostConfiguration hostConfiguration = IP.GetHostConfiguration();
                hostConfiguration.StartDhcp(intf);
            }
        }

        public void StopDhcp(String ifName)
        {
            IAdapter intf = FindAdapter(ifName);

            if (intf == null) {
                throw new Exception("StopDhcp");
            }
            else {
                HostConfiguration hostConfiguration = IP.GetHostConfiguration();
                hostConfiguration.StopDhcp(intf);
            }
        }

        public bool IsRunningDhcp(String ifName)
        {
            IAdapter intf = FindAdapter(ifName);

            if (intf == null) {
                throw new Exception("IsRunningDhcp");
            }
            else {
                HostConfiguration hostConfiguration = IP.GetHostConfiguration();
                return hostConfiguration.IsRunningDhcp(intf);
            }
        }

        public void SetInterfaceState(String ifName, uint addr, uint mask, uint gway)
        {
            IAdapter intf = FindAdapter(ifName);

            if (intf == null) {
                throw new Exception("SetInterfaceState");
            }
            else {
                HostConfiguration h = IP.GetHostConfiguration();

                // Remove existing interface binding, if any
                h.Bindings.Flush(intf);

                InterfaceIPConfiguration ipconf =
                    new InterfaceIPConfiguration(new IPv4(addr),
                                                 new IPv4(mask),
                                                 new IPv4(gway));

                if (h.Bindings.Add(intf, ipconf) == false) {
                    throw new Exception("SetInterfaceState");
                }
            }
        }

        public String[] GetInterfaces()
        {
            // Count the number of interfaces
            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            ICollection adapters = hostConfiguration.GetAdapterInfoCollection();
            String[] names = new String[adapters.Count];
            int i = 0;

            foreach (IAdapter ai in adapters) {
                names[i] = ai.NicName;
                i++;
            }

            return names;
        }

        public InterfaceInfo GetInterfaceState(String ifName)
        {
            IAdapter intf = FindAdapter(ifName);

            if (intf == null) {
                throw new Exception("GetInterfaceState");
            }
            else {
                HostConfiguration h = IP.GetHostConfiguration();
                InterfaceInfo retval = new InterfaceInfo();

                // Copy the global interface info
                retval.driverName = intf.DriverName;
                retval.driverVersion = intf.DriverVersion;
                retval.hardwareAddress = intf.HardwareAddress;
                retval.linkSpeed = intf.LinkSpeed;

                // Copy all the IP config info
                ArrayList configs = h.Bindings.GetAdapterIPConfigurations(intf);
                InterfaceIPInfo[] ipConfigs = new InterfaceIPInfo[configs.Count];
                int i = 0;

                foreach (InterfaceIPConfiguration ipc in configs) {
                    ipConfigs[i] = new InterfaceIPInfo();
                    ipConfigs[i].address = (uint)ipc.Address;
                    ipConfigs[i].netmask = (uint)ipc.NetMask;
                    ipConfigs[i].gateway = (uint)ipc.Gateway;
                    i++;
                }

                retval.ipConfigs = ipConfigs;
                return retval;
            }
        }

        public bool IsLocalAddress(uint addr)
        {
            HostConfiguration h = IP.GetHostConfiguration();
            bool isLocal = h.Bindings.IsLocalAddress(new IPv4(addr));
            return isLocal;
        }

        private IAdapter FindAdapter(string deviceName)
        {
            if (deviceName == null) return null;

            HostConfiguration hostConfiguration = IP.GetHostConfiguration();
            return hostConfiguration.FindAdapterByName(deviceName);
        }
    }
}
