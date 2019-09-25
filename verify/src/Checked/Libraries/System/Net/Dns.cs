 ////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Notes:
//  Ported from the Coriolis code base, with extensive changes to use
//  the channel interface to our NetStack instead of native calls.
//

namespace System.Net
{
    using System.Collections;
    using System.Text;
    using System.Net.Sockets;
    using System.Threading;
    using System.Net.IP;
    using DNSContract = Microsoft.Singularity.NetStack2.Channels.Private.DNSContract;
    using IPContract = Microsoft.Singularity.NetStack2.Channels.Private.IPContract;
    using DNSImpConnection = Microsoft.Singularity.NetStack2.DNSImpConnection;
    using InterfaceIPInfo = Microsoft.Singularity.NetStack.InterfaceIPInfo;
    using InterfaceInfo = Microsoft.Singularity.NetStack.InterfaceInfo;

    public sealed class Dns {
        // This is the slot we use to store the per-thread channel to the NetStack
        private static TRef/*DNSContract*/ DnsSlot = null;
        private static TRef/*IPContract*/  IPSlot = null;
        private static MonitorLock DnsSlotLock = new MonitorLock(); // Used for initialization
        private static MonitorLock IPSlotLock = new MonitorLock(); // ditto

        //
        // Constructor is private to prevent instantiation
        //
        private Dns() {
            // Shouldn't ever be called
        }

        // Must be balanced with a call to ReleaseDnsConnection()!
        internal static DNSContract/*.Imp*/ GetDnsConnection()
        {
            using(DnsSlotLock.Lock()) {
                if (DnsSlot == null) {
                    DnsSlot = new TRef(new DNSContract());
                }
            }
            return (DNSContract)(DnsSlot.Acquire());
        }

        internal static void ReleaseDnsConnection(DNSContract/*.Imp*/ connection)
        {
            DnsSlot.Release(connection);
        }

       // Must be balanced with a call to ReleaseIPConnection()!
        internal static IPContract/*.Imp*/ GetIPConnection()
        {
            using(IPSlotLock.Lock()) {
                if (IPSlot == null) {
                    IPSlot = new TRef(new IPContract());
                }
            }
            return (IPContract)(IPSlot.Acquire());
        }

        internal static void ReleaseIPConnection(IPContract/*.Imp*/ connection)
        {
            IPSlot.Release(connection);
        }

        public static IPHostEntry GetHostByName(string hostName) {
            if (hostName == null) {
                throw new ArgumentNullException("hostName");
            }

            return InternalGetHostByName(hostName);
        }

        internal static IPHostEntry InternalGetHostByName(string hostName) {
            return InternalResolve(hostName);
        } // GetHostByName


        public static IPAddress[] GetLocalHostAddresses() {

            IPAddress[] retval;
            IPContract/*.Imp*/ ipConn = GetIPConnection();

            try {
                String[] ifList;
                ArrayList addresses = new ArrayList();

                ifList = ipConn.GetInterfaces();

                    for (int i = 0; i < ifList.Length; ++i) {
                            InterfaceInfo ifInfo = ipConn.GetInterfaceState(ifList[i]);
                            ifList[i] = null;
                                  // Copy out all of this interface's addresses
                                  InterfaceIPInfo[] ipConfigs = ifInfo.ipConfigs;
                                  if (ipConfigs != null) {
                                      for (int j = 0; j < ipConfigs.Length; ++j) {
                                          addresses.Add(new IPAddress(ipConfigs[j].address));
                                      }
                                  }
                                  //ifInfo.Dispose();
                    }

                IPAddress[] ipAddresses = new IPAddress[addresses.Count];
                for (int i = 0; i < ipAddresses.Length; i++) {
                    ipAddresses[i] = (IPAddress)(addresses[i]);
                }
                return ipAddresses;
            }
            finally {
                ReleaseIPConnection(ipConn);
            }

        } // GetLocalHostAddresses


        public static IPHostEntry GetHostByAddress(string address) {

            if (address == null) {
                throw new ArgumentNullException("address");
            }

            IPHostEntry ipHostEntry = InternalGetHostByAddress(IPAddress.Parse(address));
            return ipHostEntry;
        } // GetHostByAddress

        public static IPHostEntry GetHostByAddress(IPAddress address) {

            if (address == null) {
                throw new ArgumentNullException("address");
            }

            IPHostEntry ipHostEntry = InternalGetHostByAddress(address);
            return ipHostEntry;
        } // GetHostByAddress

        internal static IPHostEntry InternalGetHostByAddress(IPAddress address)
        {
            // We only support IPv4 addresses under Singularity!
            if (address.AddressFamily != AddressFamily.InterNetwork) {
                //
                // Protocol not supported
                //
                throw new SocketException(SocketErrors.WSAEPROTONOSUPPORT);
            }

            // Turn the address into a string and resolve it
            return InternalResolve(address.ToString());

        } // InternalGetHostByAddress

        // host can be either a host's textual name, or the string of an address
        internal static IPHostEntry InternalResolve(string host)
        {
            DNSContract/*.Imp*/ dnsConn = GetDnsConnection();

            try {
                string[] aliases;
                IPv4[] addrs;

                if (DNSImpConnection.Resolve(dnsConn, host, out aliases, out addrs)) {
                    VTable.Assert(aliases != null);
                    VTable.Assert(addrs != null);
                    return DNSInfoToIPHostEntry(aliases, addrs); }
                else {
                    throw new SocketException(SocketErrors.WSAHOST_NOT_FOUND);
                }
            }
            finally {
                ReleaseDnsConnection(dnsConn);
            }
        } // InternalResolve

        internal static IPHostEntry DNSInfoToIPHostEntry(string[] aliases, IPv4[] addrs)
        {
            IPHostEntry retval = new IPHostEntry();

            IPAddress[] addressList = new IPAddress[addrs.Length];
            for (int i = 0; i < addrs.Length; ++i) {
                addressList[i] = new IPAddress(addrs[i]);
            }

            string[] resultAliases = new string[aliases.Length - 1];
            for (int i = 1; i < aliases.Length; ++i) {
                resultAliases[i] = aliases[i];
            }

            retval.Aliases = resultAliases;
            retval.AddressList = addressList;
            retval.HostName = aliases[0];
            return retval;
        }

        public static string GetHostName() {
            IPContract/*.Imp*/ ipConn = GetIPConnection();

            try {
                String hostName = ipConn.GetHostName();
                string strHostName = hostName;
                //delete hostName;
                return strHostName;
            }
            finally {
                ReleaseIPConnection(ipConn);
            }
        }


        public static IPAddress[] ResolveToAddresses(string hostName) {
            IPHostEntry entry  = Resolve(hostName);
            return entry.AddressList;
        }

        //
        // Note that in the case of multiple IP addresses, the address returned is
        // chosen arbitrarily.
        //
        public static IPHostEntry Resolve(string hostName) {
            if (hostName == null) {
                throw new ArgumentNullException("hostName");
            }

            return InternalResolve(hostName);
        }
    }
}
