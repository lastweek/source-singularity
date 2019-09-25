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

    using NetStack.Contracts;
    using NetStack.Channels.Public;
    using Microsoft.SingSharp;
    using Microsoft.Singularity;
    using Microsoft.Singularity.Channels;
    using Microsoft.Singularity.Directory;

    public sealed class Dns {
        // This is the slot we use to store the per-thread channel to the NetStack
        private static LocalDataStoreSlot DnsSlot = null;
        private static LocalDataStoreSlot IPSlot = null;
        private static object DnsSlotLock = new object(); // Used for initialization
        private static object IPSlotLock = new object(); // ditto

        //
        // Constructor is private to prevent instantiation
        //
        private Dns() {
            // Shouldn't ever be called
        }

        // All threads share a LocalDataStoreSlot object that identifies a thread-local
        // data "slot" that each thread can use. This object must be created in a thread-
        // safe way the first time it becomes necessary. See Thread.AllocateDataSlot().
        internal static LocalDataStoreSlot SafeSlotFetchOrInitialize(ref LocalDataStoreSlot slot,
                                                                     object slotLock)
        {
            // This initialization sequence is meant to be thread-safe
            if (slot == null) {
                lock (slotLock) {
                    if (slot == null) {
                        slot = Thread.AllocateDataSlot();
                    }
                }
            }

            return slot;
        }

        // Must be balanced with a call to ReleaseDnsConnection()!
        internal static DNSContract.Imp! GetDnsConnection()
        {
            LocalDataStoreSlot slot = SafeSlotFetchOrInitialize(ref DnsSlot, DnsSlotLock);

            if (Thread.GetData(slot) == null) {
                // We haven't created a channel for this thread yet. Create one.
                DNSContract.Imp! dnsImp;
                DNSContract.Exp! dnsExp;
                DirectoryServiceContract.Imp epNS = DirectoryService.NewClientEndpoint();

                DNSContract.NewChannel(out dnsImp, out dnsExp);

                try {
                    epNS.SendBind(Bitter.FromString2(DNSContract.ModuleName), dnsExp);

                    switch receive {
                        case epNS.NakBind(ServiceContract.Exp:Start rejectedEP, error) :
                            if (rejectedEP != null) {
                                delete rejectedEP;
                            }
                            delete dnsImp;
                            // Do nothing; we will return null below.
                            break;

                        case epNS.AckBind() :
                            // Success; put our remaining end of the channel
                            // into thread-local storage.
                            dnsImp.RecvReady();
                            TRef<DNSContract.Imp:ReadyState> dnsConnHolder = new TRef<DNSContract.Imp:ReadyState>(dnsImp);
                            Thread.SetData(slot, dnsConnHolder);
                            break;
                    }
                }
                finally {
                    delete epNS;
                }
            }

            // By now there should definitely be a channel in our thread-local storage.
            TRef<DNSContract.Imp:ReadyState>! connHolder = (TRef<DNSContract.Imp:ReadyState>!)Thread.GetData(slot);
            return connHolder.Acquire();
        }

        internal static void ReleaseDnsConnection([Claims] DNSContract.Imp:ReadyState! connection)
        {
            // Put the channel back into thread-local storage.
            TRef<DNSContract.Imp:ReadyState>! dnsConnHolder = (TRef<DNSContract.Imp:ReadyState>!)Thread.GetData(DnsSlot);
            dnsConnHolder.Release(connection);
        }

       // Must be balanced with a call to ReleaseIPConnection()!
        internal static IPContract.Imp! GetIPConnection()
        {
            LocalDataStoreSlot slot = SafeSlotFetchOrInitialize(ref IPSlot, IPSlotLock);

            if (Thread.GetData(slot) == null) {
                IPContract.Imp! ipImp;
                IPContract.Exp! ipExp;
                DirectoryServiceContract.Imp epNS = DirectoryService.NewClientEndpoint();

                IPContract.NewChannel(out ipImp, out ipExp);

                try {
                    epNS.SendBind(Bitter.FromString2(IPContract.ModuleName), ipExp);

                    switch receive {
                        case epNS.NakBind(ServiceContract.Exp:Start rejectedEP, error) :
                            // Do nothing; we will return null below.
                            delete ipImp;
                            if (rejectedEP != null) {
                                delete rejectedEP;
                            }
                            break;

                        case epNS.AckBind() :
                            // Success; put our remaining end of the channel
                            // into thread-local storage.
                            ipImp.RecvReady();
                            TRef<IPContract.Imp:ReadyState> ipConnHolder = new TRef<IPContract.Imp:ReadyState>(ipImp);
                            Thread.SetData(slot, ipConnHolder);
                            break;
                    }
                }
                finally {
                    delete epNS;
                }
            }

            TRef<IPContract.Imp:ReadyState>! connHolder = (TRef<IPContract.Imp:ReadyState>!)Thread.GetData(slot);
            return connHolder.Acquire();
        }

        internal static void ReleaseIPConnection([Claims] IPContract.Imp:ReadyState! connection)
        {
            // Put the channel back into thread-local storage.
            TRef<IPContract.Imp:ReadyState>! ipConnHolder = (TRef<IPContract.Imp:ReadyState>!)Thread.GetData(IPSlot);
            ipConnHolder.Release(connection);
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
            IPContract.Imp ipConn = GetIPConnection();

            try {
                char[][]! in ExHeap ifList;
                ArrayList addresses = new ArrayList();

                ipConn.SendGetInterfaces();
                ipConn.RecvInterfaceList(out ifList);

                try {
                    for (int i = 0; i < ifList.Length; ++i) {
                        expose(ifList[i]) {
                            ipConn.SendGetInterfaceState((!)ifList[i]);
                            ifList[i] = null;

                            switch receive {
                              case ipConn.InterfaceNotFound() :
                                  throw new SocketException(SocketErrors.SocketError);
                                  break;

                              case ipConn.InterfaceState(InterfaceInfo ifInfo) :
                              {
                                  // Copy out all of this interface's addresses
                                  InterfaceIPInfo[] in ExHeap ipConfigs = ifInfo.ipConfigs;
                                  if (ipConfigs != null) {
                                      for (int j = 0; j < ipConfigs.Length; ++j) {
                                          addresses.Add(new IPAddress(ipConfigs[j].address));
                                      }
                                  }
                                  ifInfo.Dispose();
                              }
                              break;
                            }
                        }
                    }
                }
                finally {
                    delete ifList; // This should hold only NULLs by now
                }

                return (IPAddress[])addresses.ToArray(typeof(IPAddress));
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

        internal static IPHostEntry InternalGetHostByAddress(IPAddress! address)
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
            return null;

        } // InternalGetHostByAddress

        // host can be either a host's textual name, or the string of an address
        internal static IPHostEntry! InternalResolve(string host)
        {
            DNSContract.Imp dnsConn = GetDnsConnection();

            try {
                string[] aliases;
                IPv4[] addrs;

                if (DNSImpConnection.Resolve(dnsConn, host, out aliases, out addrs)) {
                    assert aliases != null;
                    assert addrs != null;
                    return DNSInfoToIPHostEntry(aliases, addrs); }
                else {
                    throw new SocketException(SocketErrors.WSAHOST_NOT_FOUND);
                }
            }
            finally {
                ReleaseDnsConnection(dnsConn);
            }
        } // InternalResolve

        internal static IPHostEntry! DNSInfoToIPHostEntry(string[]! aliases, IPv4[]! addrs)
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
            IPContract.Imp ipConn = GetIPConnection();

            try {
                char[]! in ExHeap hostName;
                ipConn.SendGetHostName();
                ipConn.RecvHostName(out hostName);
                string strHostName = Bitter.ToString(hostName);
                delete hostName;
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
        public static IPHostEntry! Resolve(string hostName) {
            if (hostName == null) {
                throw new ArgumentNullException("hostName");
            }

            return InternalResolve(hostName);
        }
    }
}
