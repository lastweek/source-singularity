///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:
//
//  Note: Based on recommendations found in
//        "Efficient demultiplexing of incoming TCP packets"
//        Paul E. McKenny and Ken F Dove SIGCOMM '92
//

//#define DEBUG_CHAINED_HASH

using System;
using Drivers.Net;
using System.Net.IP;
using System.Threading;
using System.Diagnostics;

using Microsoft.Singularity;

namespace Microsoft.Singularity.NetStack2
{
    public class ChainedHash
    {
        [Conditional("DEBUG_CHAINED_HASH")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("ChainedHash: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        [Conditional("DEBUG_CHAINEDHASH")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print("ChainedHash: {0}",
                            DebugStub.ArgList(format));
        }

        //"A comparison of hashing schemes for address lookup in
        // computer networks" Raj Jain DEC tech report 1989
        //i.e. XOR rules!
        private byte Hash(IPv4 src, IPv4 dst, ushort sPort, ushort dPort)
        {
            uint t = ((uint) (src ^ dst)) ^ (uint) (sPort ^ dPort);
            byte h = (byte) (t ^ (t >> 24) ^ (t >> 16) ^ (t >> 8));
            return h;
        }

        public class ChainedHashNode
        {
            public LinkedList linkedList;
            public TCP         sideCache;

            public ChainedHashNode()
            {
                sideCache = null;
                linkedList = new LinkedList();
            }
        }

        private bool IsTCPSessionMatch(TCP tcp, IPv4 srcAddress,
                                       ushort srcPort, IPv4 destAddress,
                                       ushort destPort)
        {
            if ((tcp.localPort       == destPort)   &&
                (tcp.localIPAddress  == destAddress) &&
                (tcp.remotePort      == srcPort) &&
                (tcp.remoteIPAddress == srcAddress))     {
                return true;
            }
            return false;
        }

        public const int defaultHashSize = 256;
        private ChainedHashNode[] chainedHash;
        private int chainedHashSize;
        private bool activeMatch;

        [Microsoft.Contracts.NotDelayed]
        public ChainedHash(bool activeMatch)
        {
            DebugPrint("New chained hash --> active {0}\n", activeMatch);
            this.activeMatch = activeMatch;
            chainedHashSize = defaultHashSize;
            chainedHash = new ChainedHashNode[chainedHashSize];
            for (int i = 0; i < chainedHashSize; i++) {
                chainedHash[i] = new ChainedHashNode();
            }
        }

        public LinkedListNode InsertNewSession(TCP tcpSession)
        {
            byte hash = Hash(tcpSession.localIPAddress, tcpSession.remoteIPAddress,
                             tcpSession.localPort, tcpSession.remotePort);

            ChainedHashNode chainedHashNode = chainedHash[hash];
            VTable.Assert(chainedHashNode != null);
            //XXX check for duplicates!
            return chainedHashNode.linkedList.InsertHead(tcpSession);
        }

        private TCP MatchTCPSession(IPv4 srcAddress, ushort srcPort,
                                    IPv4 destAddress, ushort destPort, byte hash)
        {
            ChainedHashNode chainedHashNode = chainedHash[hash];
            VTable.Assert(chainedHashNode != null);
            TCP tcpSession = chainedHashNode.sideCache;

            if ((tcpSession != null) &&
                IsTCPSessionMatch(tcpSession, srcAddress, srcPort, destAddress, destPort)) {
                DebugPrint("Found TCP session in cache\n");
                return tcpSession;
            }
            tcpSession = null;
            LinkedListNode currentNode = chainedHashNode.linkedList.head;
            int numMatches = 0;
            while (currentNode != null) {
                TCP tmpTcpSession = currentNode.theObject as TCP;
                DebugStub.Assert (tmpTcpSession != null);
                VTable.Assert(tmpTcpSession != null);
                numMatches++;
                if (IsTCPSessionMatch(tmpTcpSession, srcAddress, srcPort, destAddress, destPort)) {
                    DebugPrint("Found TCP session -- {0} matches required\n", numMatches);
                    chainedHashNode.sideCache = tmpTcpSession;
                    tcpSession = tmpTcpSession;
                    break;
                }
                currentNode = currentNode.nxt;
            }
            return tcpSession;

        }

        public TCP GetTCPSession(IPv4 srcAddress, ushort srcPort, IPv4 destAddress, ushort destPort)
        {


            byte hash = Hash(destAddress, srcAddress, destPort, srcPort);
            DebugPrint("Connection src:port {0}:{1} dest:port {2}:{3} hash {4} \n",
                       srcAddress, srcPort, destAddress, destPort, hash);
            TCP tcpSession = MatchTCPSession(srcAddress, srcPort, destAddress, destPort, hash);
            if ((tcpSession == null) &&
                (activeMatch == false)) {
                hash  = Hash(destAddress, IPv4.Any, destPort, 0);
                tcpSession = MatchTCPSession(IPv4.Any, 0, destAddress, destPort, hash);
                if (tcpSession == null) {
                    hash  = Hash(IPv4.Any, IPv4.Any, destPort, 0);
                    tcpSession = MatchTCPSession(IPv4.Any, 0, IPv4.Any, destPort, hash);
                }
            }
            return tcpSession;
        }

        public bool RemoveTcpSession(TCP tcpSession, LinkedListNode tcpLLNode)
            //requires tcpSession.chainedHashLLNode != null;
        {
            byte hash = Hash(tcpSession.localIPAddress, tcpSession.remoteIPAddress,
                             tcpSession.localPort, tcpSession.remotePort);

            ChainedHashNode chainedHashNode = chainedHash[hash];
            VTable.Assert(chainedHashNode != null);
            if (tcpSession == chainedHashNode.sideCache) {
                chainedHashNode.sideCache = null;
            }
            LinkedList linkedList = chainedHashNode.linkedList;
            VTable.Assert(linkedList != null);
            TCP returnedSession = linkedList.Remove(tcpLLNode) as TCP;
            DebugStub.Assert(tcpSession == returnedSession);
            VTable.Assert(tcpSession == returnedSession);
            return true;
        }
    }
}
