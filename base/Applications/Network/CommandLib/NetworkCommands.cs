///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Minimal Network Adapter Configuration Tool
//

using System;
using System.Diagnostics;
using System.Net.IP;

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using NetStack.Contracts;
using NetStack.Channels.Public;

namespace Microsoft.Singularity.Applications.Network
{
    public class Utils
    {
        public static bool ConnectEndPoint(string! lookupName, [Claims] ServiceContract.Exp! ep)
        {
            DirectoryServiceContract.Imp epNS = DirectoryService.NewClientEndpoint();

            try {
                ErrorCode errorOut; 
                bool ok = SdsUtils.Bind(lookupName, epNS, ep, out errorOut);
                if (!ok) {
                    return false; 
                 } 
                else {
                    return true; 
                }
//
//              epNS.SendBind(Microsoft.Singularity.Bitter.FromString2(lookupName), ep);
//
//              switch receive {
//                  case epNS.NakBind(ServiceContract.Exp:Start rejectedEP, error) :
//                      // failure
//                      delete rejectedEP;
//                      return false;
//                      break;
//
//                  case epNS.AckBind() :
//                      // success
//                      return true;
//                      break;
//
//                  case epNS.ChannelClosed() :
//                      // failure
//                      return false;
//              }
//                
            }
            finally {
                delete epNS;
            }
        }

        public static TcpConnectionContract.Imp:ReadyState GetNewTcpEndPoint()
        {
            TcpContract.Imp! tcpImp;
            TcpContract.Exp! tcpExp;
            TcpContract.NewChannel(out tcpImp, out tcpExp);

            if (ConnectEndPoint(TcpContract.ModuleName, tcpExp)) {
                tcpImp.RecvReady();

                TcpConnectionContract.Imp! connImp;
                TcpConnectionContract.Exp! connExp;
                TcpConnectionContract.NewChannel(out connImp, out connExp);

                tcpImp.SendCreateTcpSession(connExp);
                connImp.RecvReady();
                delete tcpImp;
                return connImp;
            }
            else {
                delete tcpImp;
                return null;
            }
        }

        public static UdpConnectionContract.Imp:ReadyState GetNewUdpEndPoint()
        {
            UdpContract.Imp! udpImp;
            UdpContract.Exp! udpExp;
            UdpContract.NewChannel(out udpImp, out udpExp);

            if (ConnectEndPoint(UdpContract.ModuleName, udpExp)) {
                udpImp.RecvReady();

                UdpConnectionContract.Imp! connImp;
                UdpConnectionContract.Exp! connExp;
                UdpConnectionContract.NewChannel(out connImp, out connExp);

                udpImp.SendCreateUdpSession(connExp);
                connImp.RecvReady();
                delete udpImp;
                return connImp;
            }
            else {
                delete udpImp;
                return null;
            }
        }
        
        public static void DNSShow(DNSContract.Imp:ReadyState! dnsConn)
        {
            string[] prefix = { "Primary", "Secondary" };
            int key = 0;
            IPv4[] servers = DNSImpConnection.GetNameServers(dnsConn);

            foreach (IPv4 nameserver in servers) {
                Console.WriteLine("    {0} name server {1}",
                                  prefix[key], nameserver);
                key = 1;
            }

            if (key == 0) {
                Console.WriteLine("No DNS servers configured.");
            }
        }
        
    }

}
