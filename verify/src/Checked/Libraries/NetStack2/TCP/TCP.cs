//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:
//
//  Note: Goal -- implement TCP RENO
//
//#define DEBUG_TCP
//#define TCP_THREAD_POOL

using System;
using Drivers.Net;
using System.Net.IP;
using System.Threading;
using System.Diagnostics;
using System.Collections;
using System.Runtime.CompilerServices;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Io.Net;
using Microsoft.Singularity.V1.Services;
using Microsoft.SingSharp;
using Microsoft.Contracts;

using TcpError = NetStack.Contracts.TcpError;

namespace Microsoft.Singularity.NetStack2
{

    public enum TcpState : short
    {
        //we break camel case here for the sake of tradition
        CLOSED       = 0,
        LISTEN       = 1,
        SYN_SENT     = 2,
        SYN_RECEIVED = 3,
        ESTABLISHED  = 4,
        FIN_WAIT_1   = 5,
        FIN_WAIT_2   = 6,
        CLOSE_WAIT   = 7,
        CLOSING      = 8,
        LAST_ACK     = 9,
        TIME_WAIT    = 10,
    }

    [FlagsAttribute]
    public enum TcpFlags : byte
    {
        FIN = 0x01,
        SYN = 0x02,
        RST = 0x04,
        PSH = 0x08,
        ACK = 0x10,
        URG = 0x20,
        ECE = 0x40,
        CWR = 0x80,
    }

    enum TcpOptions : byte
    {
        EOL       = 0,
        NOP       = 1,
        MSS       = 2, //set the MSS
        WSF       = 3, //windows scaling
        TIMESTAMP = 8, //use timestamps
    }


    public struct TcpHeader
    {
        public const int MinSize = 20;

        public ushort srcPort;
        public ushort destPort;
        public uint   seqNumber;
        public uint   ackNumber;
        public byte   dataOffsetBytes; //offset counted in 4 byte intervals
        public byte   dataOffset;  //offset where data begins in 32 bit words
        public byte   flags;
        public ushort windowSize;
        public ushort checksum;
        public ushort urgentPointer;


        // Compare two TCP sequence numbers:
        //  - means A < B, 0 means A == B and + means A > B
        //[Pure]
        [Inline]
        private static int SequenceNumberCompare(uint seqA, uint seqB)
        {
            // Exploit integer underflow to compare correctly even in the case
            // of sequence number wraparound. This assumes the two numbers are
            // always in the same half of the numberspace.

            return unchecked((int)(unchecked(seqA - seqB)));
        }

        //[Pure]
        public static bool SeqEQ(uint seqA, uint seqB)
        {
            return TcpHeader.SequenceNumberCompare(seqA, seqB) == 0;
        }

        //[Pure]
        public static bool SeqNEQ(uint seqA, uint seqB)
        {
            return TcpHeader.SequenceNumberCompare(seqA, seqB) != 0;
        }

        //[Pure]
        public static bool SeqLEQ(uint seqA, uint seqB)
        {
            return TcpHeader.SequenceNumberCompare(seqA, seqB) <= 0;
        }

        //[Pure]
        public static bool SeqLess(uint seqA, uint seqB)
        {
            return TcpHeader.SequenceNumberCompare(seqA, seqB) < 0;
        }

        //[Pure]
        public static bool SeqGEQ(uint seqA, uint seqB)
        {
            return TcpHeader.SequenceNumberCompare(seqA, seqB) >= 0;
        }

        //[Pure]
        public static bool SeqGreater(uint seqA, uint seqB)
        {
            return TcpHeader.SequenceNumberCompare(seqA, seqB) >  0;
        }

        public TcpHeader(Bytes packet, int index)
        {

            srcPort = NetworkBitConverter.ToUInt16(packet, index);
            index += 2;

            destPort =  NetworkBitConverter.ToUInt16(packet, index);
            index += 2;

            seqNumber =  NetworkBitConverter.ToUInt32(packet, index);
            index += 4;

            ackNumber =  NetworkBitConverter.ToUInt32(packet, index);
            index += 4;

            dataOffsetBytes = packet[index++];
            dataOffset = (byte) ((dataOffsetBytes >> 4) * 4);

            flags = packet[index++];

            windowSize = NetworkBitConverter.ToUInt16(packet, index);
            index += 2;

            checksum = NetworkBitConverter.ToUInt16(packet, index);
            index += 2;

            urgentPointer = NetworkBitConverter.ToUInt16(packet, index);
        }

        public static ushort SumHeader(TcpHeader tcpHeader)
        {
            int checksum = tcpHeader.srcPort;
            checksum += tcpHeader.destPort;
            checksum += (int) (tcpHeader.seqNumber >> 16);
            checksum += (int) (tcpHeader.seqNumber & 0xffff);
            checksum += (int) (tcpHeader.ackNumber >> 16);
            checksum += (int) (tcpHeader.ackNumber & 0xffff);
            checksum += (((int)tcpHeader.dataOffsetBytes) << 8) | (int)tcpHeader.flags;
            checksum += (int) tcpHeader.windowSize;
            checksum += (int) tcpHeader.urgentPointer;

            // Double-wrap checksum
            checksum = (checksum & 0xFFFF) + (checksum >> 16);
            checksum = (checksum & 0xFFFF) + (checksum >> 16);
            return (ushort)checksum;
        }

        public static bool IsChecksumValid(IpHeader     ipHeader,
                                           TcpHeader    tcpHeader,
                                           Bytes buffer)
        {
            int ipOffset = EthernetHeader.Size;
            ushort ipPayloadSize = 0;
            // Compute partial checksums of headers
            ushort chksum = IpHeader.SumPseudoHeader(buffer, ipOffset, ref ipPayloadSize);

            chksum = IpHeader.SumShortValues(chksum, SumHeader(tcpHeader));

            // Checksum payload (without potential odd byte)
            //XXX we include tcp options in the 'payload' for checksumming...related to legacy code from
            //old netstack...should be cleaned up.
            int payloadOffset = TcpHeader.MinSize + IpHeader.Size + EthernetHeader.Size;
            int payloadLength = ipPayloadSize - TcpHeader.MinSize;
            //DebugStub.WriteLine("payload length {0}\n", DebugStub.ArgList(payloadLength));
            ushort payloadSum = IpHeader.SumShortValues(buffer, payloadOffset, payloadLength);

            chksum = IpHeader.SumShortValues(chksum, payloadSum);

            unchecked {
                chksum = (ushort)~chksum;
            }
            //who know.....
            if (chksum == (ushort) 0xFFFF) {
                chksum = 0;
            }
            else if (chksum == (ushort) 0x0) {
                chksum = 0xFFFF;
            }

            // Check for match.
            bool checksumMatch = (tcpHeader.checksum == chksum);

            // If checksum error, unconditionally output message to debugger.
            if (checksumMatch == false) {
                DebugStub.WriteLine("Bad TCP checksum {0:x4} != {1:x4}:  SEQ {2:x8}  ACK {3:x8}",
                    DebugStub.ArgList(tcpHeader.checksum, chksum,
                        tcpHeader.seqNumber,
                        tcpHeader.ackNumber
                    ));
            }

            // IsValid is a Match.
            //            return checksumMatch;
            return true;
        }

         public static void SetTcpChecksum(Bytes buffer,
                                           Bytes payload,
                                           int ipOffset,
                                           ushort tcpLength)
         {
             // sum IP pseudo
             ushort ipPayloadSize = 0;
             ushort headerSum = IpHeader.SumPseudoHeader(buffer, ipOffset,
                                                         ref ipPayloadSize);

             DebugStub.Assert((tcpLength + payload.Length) == ipPayloadSize);

             // now add it to the udp header + data
             int ipHeaderSize = (buffer[ipOffset] & 0xf) * 4;
             int tcpOffset     = ipOffset + ipHeaderSize;

             ushort tcpsum = IpHeader.SumShortValues(buffer, ipOffset+IpHeader.Size, tcpLength);

             DebugStub.Assert(buffer[tcpOffset + 16] == 0);
             DebugStub.Assert(buffer[tcpOffset + 17] == 0);

             ushort payloadSum = IpHeader.SumShortValues(payload, 0,
                                                         payload.Length);
             ushort hdrSum = IpHeader.SumShortValues(headerSum, tcpsum);
             ushort chksum;
             chksum = (ushort) ~(
                 IpHeader.SumShortValues(hdrSum, payloadSum)
                 );
             if (chksum == 0) {
                 chksum = (ushort) 0xFFFF;
             }

             buffer[tcpOffset + 16] = (byte) (chksum >> 8);
             buffer[tcpOffset + 17] = (byte) (chksum & 0xff);
         }

         public static void SetTcpChecksum(Bytes header,
                                           int ipOffset,
                                           ushort tcpLength)
         {
             // sum IP pseudo
             ushort ipPayloadSize = 0;
             ushort headerSum = IpHeader.SumPseudoHeader(header, ipOffset,
                                                         ref ipPayloadSize);

             DebugStub.Assert(tcpLength == ipPayloadSize);

             // now add it to the tcp header + data
             int ipHeaderSize = (header[ipOffset] & 0xf) * 4;
             int tcpOffset     = ipOffset + ipHeaderSize;
             // DebugStub.WriteLine("ipHeaderSize {0} tcpOffset {1}\n", DebugStub.ArgList(ipHeaderSize, tcpOffset));
             ushort tcpsum = IpHeader.SumShortValues(header, ipOffset+IpHeader.Size, tcpLength);

             DebugStub.Assert(header[tcpOffset + 16] == 0);
             DebugStub.Assert(header[tcpOffset + 17] == 0);

             ushort hdrSum = IpHeader.SumShortValues(headerSum, tcpsum);
             ushort chksum = (ushort) ~hdrSum;
             if (chksum == 0) {
                 chksum = (ushort) 0xFFFF;
             }

             header[tcpOffset + 16] = (byte) (chksum >> 8);
             header[tcpOffset + 17] = (byte) (chksum & 0xff);
         }

    }

    public class TCP
    {
        private const uint   DefaultRxWinSize = 65535;
        private const uint   DefaultTxWinSize = 65535;
        private static ushort  MaxPortNumber = 65535;

        //global data structures
        private static ushort srcMSS = 1460; //assuming ethernet
        private static uint   nextISS = 1;   //XXX wrong.

        private static MonitorLock   thisLock = new MonitorLock();
        private static MonitorLock   tcpPortsMtx;
        private static ushort  nextPortNumber;   //assigning ports on demand


        public  ushort localPort;
        public  ushort remotePort;
        public  IPv4   localIPAddress;
        public  IPv4   remoteIPAddress;
        public  LinkedListNode chainedHashLLNode; //pointer into location in chained hash table
        public  int    acceptQueueMaxSize;
        public  int    acceptQueueLength;
        public  int    acceptQueueHead;
        public  int    acceptQueueTail;
        public  TCP[]  acceptQueue;
        public  TCP    listenSocket;

        private static  TimerWheel  slowWheel;
        private static  TimerWheel  fastWheel;

        private static  ChainedHash activeHash;
        private static  ChainedHash passiveHash;

#if TCP_THREAD_POOL
        private static  NetStackThreadPool threadPool;
#endif
        public  bool activeOpen;


        //per connection data structures

        private ushort  defaultMaxSegSize = 536;   //default unless notified in SYN options
        private TcpState   currentState;    //where we are in the state machine

        private short   currentRxt;      //current retransmission timeout
        private short   dupAckCount;     //number consecutive dup acks received
        private ushort  maxSegSize;      //max segement size to send
        //what about push?
        private bool    ackNow;        //send ack right away
        private bool    delayAck;      //use del ack timer
        private bool    noDelay;       //disable nagle
        private bool    needFin;
        private bool    needAck;

        //TCP options
        private bool    rcvdScale;     //did we receive the windows scaling option?
        private bool    rcvdTimestamp; //did we receive request for echo timestamps?

        private bool    isBound;
        private bool    isConnected;

        //pointers into timer wheels
        private LinkedListNode delayAckTimeoutNode;
        private LinkedListNode retransmitTimeoutNode;
        private LinkedListNode connectionTimeoutNode;
        private LinkedListNode fin2MslTimeoutNode;      //used for both fin2 and TimeWait

        //delegates for timer wheel
        public TimerWheel.TimerDelegate connectionTimeoutDelegate;
        public TimerWheel.TimerDelegate delayAckTimeoutDelegate;
        public TimerWheel.TimerDelegate retransmitTimeoutDelegate;
        public TimerWheel.TimerDelegate fin2MslTimeoutDelegate;

        public  AutoResetEvent tcpWriterWait;
        public  AutoResetEvent tcpReaderWait;
        public  AutoResetEvent tcpConnWait;
        public bool    finacked;
        public bool readerWaiting;
        public bool writerWaiting;
        public bool    disposed;


        //RFC 793
        //Send Sequence Variables
        private uint sndUna;  // send unacknowledged
        private uint sndNxt;  // send next
        private uint sndMax;
        private uint sndWnd;  // send window
        private uint sndUp ;  // send urgent pointer
        private uint sndWn1;  // segment sequence number used for last window update
        private uint sndWn2;  // segment acknowledgment number used for last window update
        private uint iss;      // initial send sequence number

        //Receive Sequence Variables
        private uint rcvNxt; // receive next
        private uint rcvWnd; // receive window
        private uint rcvUp;  // receive urgent pointer
        private uint irs;    // initial receive sequence number

        private uint rcvAdv; //windows advertised by other end
        private ushort sndMss; //mss received in tcp options

        private long timeWaiting;

#if false
        //XXX implement later when congestion matters
        //congestion control comes later
        private uint cwnd;   //congestion control window
        private uint sndSSThresh; //size threshold for slow start

        //rtt estimators
        //these are set in 'ticks' of the slowTimer
        private short  rttEstimate;  //rtt estiamte
        private short  rttSequenceNumber; //seq currently timed
        private short  smoothedRtt; //smoothed rtt ticks x 8
        private short  rttVariance; //ticks x 4
        private ushort rttMinimum; //minimum allowed rtt
        private uint   maxSndWindow //largest window offered by peer
#endif

        private static  uint rxBufferSize; //size of buffers for apps
        private static  uint txBufferSize;

        private int timeoutValue;
        private int maxTimeoutValue;

        private TContainerTcpVectorQueueByte txContainer;         //send buffer
        private TContainerTcpVectorQueueByte rxAssemblyContainer; //reassemble out of order segments
        private TContainerTcpVectorQueueByte rxContainer;         //receieve buffer

        [Conditional("DEBUG_TCP")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("TCP: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        [Conditional("DEBUG_TCP")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print("TCP: {0}",
                            DebugStub.ArgList(format));
        }

        public TcpState CurrentState
        {
            get { return currentState; }
        }

        public bool AckNow
        {
            get { return this.ackNow; }
        }

        public static void Initialize()
        {
            //initialize timer wheels
            fastWheel = new TimerWheel(10, 200); //200 ms per 'tick'
            slowWheel = new TimerWheel(500);   //500ms per 'tick'
            //initialize chained hash tables for demultiplexing
            activeHash = new ChainedHash(true);
            passiveHash = new ChainedHash(false);
            rxBufferSize = DefaultRxWinSize;
            txBufferSize = DefaultTxWinSize;

            tcpPortsMtx = new MonitorLock();
            nextPortNumber = 1024;
#if TCP_THREAD_POOL
            threadPool = new NetStackThreadPool(16, 16*128);
#endif
        }

#if TCP_THREAD_POOL
        public static NetStackThreadPool ThreadPool {
            get { return threadPool; }
        }
#endif

        internal class ConnectionTimeout: TimerWheel.TimerDelegate
        {
            public override void Run(TCP tcpSession)
            {
                DebugStub.Print("Got connection timeout!\n");
                if (slowWheel.DeleteTimerEvent(ref tcpSession.retransmitTimeoutNode) == true) {
                    DisposeTcpSession(tcpSession);
                }
            }
        }

        public class DelayAckTimeout: TimerWheel.TimerDelegate
        {
            TCP tcp;
            internal DelayAckTimeout(TCP tcp) {this.tcp = tcp;}

            public override void Run(TCP tcpSession)
            {
                DebugStub.Print("Got ack delay timeout...sending latest ack\n");
                if (fastWheel.DeleteTimerEvent(ref tcpSession.delayAckTimeoutNode) == true) {
                    tcp.delayAckTimeoutNode = null;
                    tcp.ackNow = true;
                    tcp.SendPacket(TcpFlags.ACK, false);
                }
            }
        }

        public class RetransmitTimeout: TimerWheel.TimerDelegate
        {
            TCP tcp;
            internal RetransmitTimeout(TCP tcp) {this.tcp = tcp;}

            public override void Run(TCP tcpSession)
            {
                DebugStub.Print("Got retransmit timeout\n");

                if (slowWheel.DeleteTimerEvent(ref tcpSession.retransmitTimeoutNode) == true) {
                    //set timer to new backoff value
                    if (tcp.timeoutValue > tcp.maxTimeoutValue) {
                        DebugStub.Print("attempted final rentransmit....FAILED!\n");
                        DebugStub.Assert(false);
                        DebugStub.Break();
                    }
                    tcp.retransmitTimeoutNode = null;
                    tcp.timeoutValue = tcp.timeoutValue * 2;

                    if (tcp.currentState == TcpState.SYN_SENT) {
                        tcp.SendPacket(TcpFlags.SYN, true);
                    }
                    else if (tcp.currentState == TcpState.SYN_RECEIVED) {
                        tcp.SendPacket(TcpFlags.SYN | TcpFlags.ACK, true);
                    }
                    else {
                        tcp.ackNow = true;
                        tcp.SendPacket(TcpFlags.ACK, true);
                    }
                }
            }
        }

        internal class Fin2MslTimeout: TimerWheel.TimerDelegate
        {
            public override void Run(TCP tcpSession)
            {
                DebugPrint("Got Fin2Msl timeout!\n");
                if (slowWheel.DeleteTimerEvent(ref tcpSession.fin2MslTimeoutNode) == true) {
                    tcpSession.fin2MslTimeoutNode = null;
                    DisposeTcpSession(tcpSession);
                }
            }
        }

        public IPv4   RemoteAddress { get { return remoteIPAddress; } }
        public ushort RemotePort    { get { return remotePort; } }

        public IPv4   LocalAddress  { get { return localIPAddress; } }
        public ushort LocalPort     { get { return localPort; } }

        public TCP()
        {
            //begin with wildcards
            localIPAddress = IPv4.Any;
            localPort = 0;
            remotePort = 0;
            remoteIPAddress = IPv4.Any;

            iss = nextISS;
            nextISS += 64000;
            maxSegSize = defaultMaxSegSize;
            maxTimeoutValue = 80000;
            activeOpen = false;
            readerWaiting = false;
            writerWaiting = false;
            disposed = false;

            timeWaiting = 0;
            //default rtt estimates
#if false
            rttEstimate = 0;
            smoothedRtt = 0;
            rttVariance = 24;
            rttMinimum  = 1;  //minimum of 500 ms retransmission timeout... ugh
            currentRxt  = 12; //6 second initial retransmission timeout
#endif
            //flags
            noDelay     = true; //ignore nagle by default for now
            isBound     = false;
            isConnected = false;
            finacked    = false;
            ackNow      = false;

            needFin = false;
            needAck = false;

            //timers
            //Note -- we're currently not using the persist timer
            retransmitTimeoutNode = null;
            connectionTimeoutNode = null;
            fin2MslTimeoutNode    = null;
            delayAckTimeoutNode   = null;

            connectionTimeoutDelegate = new ConnectionTimeout();
            delayAckTimeoutDelegate = new DelayAckTimeout(this);
            fin2MslTimeoutDelegate = new Fin2MslTimeout();
            retransmitTimeoutDelegate = new RetransmitTimeout(this);

            listenSocket = null;

           //window sizes
            rcvWnd = DefaultRxWinSize;
            rcvUp = 0;

            //initialize the per connection buffers
            txContainer = new TContainerTcpVectorQueueByte(
                new TcpVectorQueueByte()
                );

            rxContainer = new TContainerTcpVectorQueueByte(
                new TcpVectorQueueByte()
                );

            rxAssemblyContainer = new TContainerTcpVectorQueueByte(
                new TcpVectorQueueByte()
                );

            currentState = TcpState.CLOSED;

            tcpWriterWait = new AutoResetEvent(false);
            tcpReaderWait  = new AutoResetEvent(false);
            tcpConnWait  = new AutoResetEvent(false);
        }

        //XXX Right now we get a port and then grok the hashtable
        //to see if it exists, and then ask for another port....
       private bool AssignNextAvailablePort()
        {
            using (tcpPortsMtx.Lock()) {
                this.localPort = nextPortNumber;
                //Sing# complains if we just allow it to roll over?
                if (nextPortNumber + 1 > MaxPortNumber) {
                    nextPortNumber = 1;
                }
                else {
                    nextPortNumber++;
                }
            }
            return true;
        }


        //add read/write/poll read etc etc etc.

        //write send function.  make changes to Nic so that we
        //can get a packetfifo a fill it with everything in the send buffer

        //finish writing timer delegates.

        public bool InternalConnect(IPv4 destIP, ushort destPort)
        {
            remoteIPAddress = destIP;
            remotePort = destPort;
            return true;
        }

        //interface calls

        //active open
        public bool Connect(IPv4 destIP, ushort destPort, out TcpError error)
        {
            error = TcpError.Unknown;

            if (isConnected == true) {
                error = TcpError.AlreadyConnected;
                return false;
            }
            InternalConnect(destIP, destPort);
            if (isBound == false) {
                if(AssignNextAvailablePort() == false) {
                    DebugPrint("Ran out of ports!\n");
                    error = TcpError.ResourcesExhausted;
                    return false;
                }
                HostConfiguration hostConfiguration = IP.GetHostConfiguration();
                RouteEntry e = hostConfiguration.RoutingTable.Lookup(destIP);

                if (e != null) {
                    localIPAddress = e.InterfaceAddress;
                    DebugPrint("local address now {0}\n", localIPAddress);
                }
                else {
                    DebugPrint("No route for {0}\n", destIP);
                    DebugStub.Assert(false);
                    //need better errors?
                    error = TcpError.ResourcesExhausted;
                    return false;
                }
            }
            DebugPrint("Starting connection src ip {0} port {1} dest ip {2} port {3}\n",
                       localIPAddress, localPort, destIP, destPort);
            chainedHashLLNode = activeHash.InsertNewSession(this);

            this.sndUna = iss;
            this.sndNxt = iss;
            this.sndMax = iss;;
            slowWheel.AddTimerEvent(75000, this,
                                    this.connectionTimeoutDelegate,
                                    ref this.connectionTimeoutNode);
            this.timeoutValue = 500;
            slowWheel.AddTimerEvent(this.timeoutValue, this,
                                    this.retransmitTimeoutDelegate,
                                    ref this.retransmitTimeoutNode);
            currentState = TcpState.SYN_SENT;
            SendPacket(TcpFlags.SYN, false);

            DebugPrint("Tcp.Connect...waiting for response...\n");
            tcpConnWait.WaitOne();
            DebugPrint("Connection complete!\n");
            activeOpen = true;

            return true;
        }

        public int GetNumWaitingListenSessions()
        {
            DebugPrint("GetNumWaitingListenSessions!\n");
            DebugStub.Break();
            return 0;
        }

        public bool IsDataAvailable()
        {
            bool rc;
            TcpVectorQueueByte rxBuffer = rxContainer.Acquire();
            rc = (rxBuffer.Size() > 0);
            rxContainer.Release(rxBuffer);

            return rc;
        }

        public bool Listen(int backlog)
        {
            DebugPrint("TCP: Listen\n");
            if (isBound == false) {
                DebugStub.Print("socket isn't bound...rejecting\n");
                return false;
            }
            if (backlog < 1 || backlog > 50) {
                DebugPrint("Backlog out of bounds...silently changing to 50\n");
                backlog = 50;
            }

            TCP tcpSession = passiveHash.GetTCPSession(this.localIPAddress, this.localPort,
                                                       IPv4.Any, 0);
            if (tcpSession != null) {
                if (tcpSession.currentState != TcpState.LISTEN) {
                    DebugStub.Print("Calling listen over existing contract.....overwriting\n");
                    DisposeTcpSession(tcpSession);
                    return false;
                } else {
                    DebugStub.Print("Failed!  Already listening....\n");
                    return false;
                }
            }

            this.acceptQueue = new TCP[backlog];
            this.acceptQueueHead = 0;
            this.acceptQueueTail = 0;
            for (int i = 0; i < backlog; i++) {
                this.acceptQueue[i] = null;
            }
            this.listenSocket = null;
            this.acceptQueueLength = 0;
            this.acceptQueueMaxSize = backlog;
            this.chainedHashLLNode = passiveHash.InsertNewSession(this);
            this.activeOpen = false;
            this.currentState = TcpState.LISTEN;
            return true;
        }

        public bool Bind(IPv4 sourceAddr, ushort sourcePort)
        {
            if (sourceAddr != IPv4.Any && !IsLocalAddress(sourceAddr)) {
                // Invalid address
                //set error
                return false;
            }
            localIPAddress = sourceAddr;
            DebugPrint("TCP port bound to {0}\n", localIPAddress);
            //check to see if this port/ip is in use.
            if ((this.localPort != sourcePort) && (sourcePort != 0)) {
                TCP tcpSession = activeHash.GetTCPSession(sourceAddr, sourcePort,
                                                          IPv4.Any, 0);
                if (tcpSession == null) {
                    tcpSession = passiveHash.GetTCPSession(sourceAddr, sourcePort,
                                                           IPv4.Any, 0);
                    if (tcpSession == null) {
                        this.localPort = sourcePort;
                        isBound = true;
                        return true;
                    }
                }
                isBound = false;
                return false;
            }
            isBound = true;

            return true;
        }

        public TCP Accept()
        {
            while (this.acceptQueue[this.acceptQueueHead] == null &&
                   this.currentState == TcpState.LISTEN) {
                bool rc;
                rc = this.tcpConnWait.WaitOne(TimeSpan.FromSeconds(5));
                if (rc == false) {
                    return null;
                }
            }
            if (this.currentState != TcpState.LISTEN) {
                DebugStub.Print("ack! no longer listening!!\n");
                return null;
            }
            TCP newConnection = this.acceptQueue[this.acceptQueueHead];
            DebugStub.Assert(newConnection != null);
            if (newConnection == null) {
                DebugStub.Break();
            }
            this.acceptQueueLength--;
            this.acceptQueue[this.acceptQueueHead] = null;
            this.acceptQueueHead =
                (this.acceptQueueHead + 1) % this.acceptQueueMaxSize;
            DebugPrint("AcceptQueueHead incremented now {0} " +
                       " acceptMaxQueueSize {1}\n",
                       this.acceptQueueHead, this.acceptQueueMaxSize);

            return newConnection;
        }

        public Bytes Read()
        {
            DebugPrint("TCP: Read\n");
            Bytes buff;

            while (((buff = PopData()) == null) &&
                   (currentState == TcpState.ESTABLISHED)) {
                tcpReaderWait.WaitOne();
            }
            return buff;
        }

        public Bytes[] ReadV()
        {
            DebugPrint("TCP:ReadV");

            Bytes[] buff = null;

            while (((buff = PopAllData()) == null) &&
                   (this.currentState == TcpState.ESTABLISHED)) {
                this.tcpReaderWait.WaitOne();
            }
            return buff;
        }

        public Bytes PollRead(TimeSpan timeout)
        {
            Bytes buff;
            bool rc = true;

            if ((buff = PopData()) == null) {
                rc = tcpReaderWait.WaitOne(timeout);
                if (rc == true) {
                    buff = PopData();
                }
            }

            return buff;
        }

        public Bytes[] PollReadV(TimeSpan timeout)
        {
            Bytes[] buff;
            bool rc = true;

            if ((buff = PopAllData()) == null) {
                rc = tcpReaderWait.WaitOne(timeout);
                if (rc == true) {
                    buff = PopAllData();
                }
            }

            return buff;
        }

        public void Close()
        {
            if (currentState == TcpState.ESTABLISHED) {
                needFin = true;
                SendPacket(TcpFlags.ACK, false);
            }
            else if (currentState == TcpState.CLOSE_WAIT) {
                //XXX might need a timer here
                needFin = true;
                SendPacket(TcpFlags.ACK, false);
            }
            else if (currentState == TcpState.CLOSED) {
                DisposeTcpSession(this);
            }
            else {
                DebugStub.WriteLine("Got close in state {0}\n", DebugStub.ArgList(currentState));
            }
        }

        public bool IsLocalAddress(IPv4 ipAddress)
        {
            return IP.IsLocalAddress(ipAddress);
        }


        private static Bytes GetHeader(int size)
        {
            //DebugPrint("Allocating header size {0}\n", size);
            byte[] header = new byte[size];
            return new Bytes(header);
        }

        //XXX need offset
        public static void BuildHeader(Bytes header, IPv4 destAddress,
                                       IPv4 srcAddress, ushort destPort, ushort srcPort,
                                       byte flags, uint seqNumber, uint ackNumber,
                                       uint windowSize, int optlen,
                                       short payloadLength, uint urgPtr, int ipHeaderOffset)
        {
            //            DebugPrint("BuildHeader optlen {0}\n", optlen);
            int totalLength = IpHeader.Size + TcpHeader.MinSize + payloadLength + optlen;

            //write ip header
            int offset = ipHeaderOffset;
            int o = ipHeaderOffset;

            header[o++] = 0x45;  //default version 4, header_len 5
            header[o++] = 0;     //tos
            header[o++] = (byte) (((ushort)totalLength) >> 8);  //total length of the ip header
            header[o++] = (byte) (((ushort)totalLength) & 0xff);
            header[o++] = (byte) (((ushort)0) >> 8);            //fragment id
            header[o++] = (byte) (((ushort)0) & 0xff);          //fragment id
            header[o++] = (byte) (((ushort)0) >> 8);   //fragment offset
            header[o++] = (byte) (((ushort)0) & 0xff); //fragment offset
            header[o++] = 128;             //default ttl
            header[o++] = 6;              // protocol ID --> tcp
            header[o++] = 0;               //ipchecksum (fill it in later)
            header[o++] = 0;               //ipchecksum

            srcAddress.CopyOut(header.Array, header.Start + o);
            o += IPv4.Length;

            // set the ip addresses
            destAddress.CopyOut(header.Array, header.Start + o);
            o += IPv4.Length;

            // calculate ip checksum
            ushort chk = IpHeader.CalculateChecksum(header, offset, IpHeader.Size);

            header[offset + 10] = (byte) (((ushort)chk) >> 8);
            header[offset + 11] = (byte) (((ushort)chk) & 0xff);

            //write tcp segment header
            header[o++] = (byte)(((ushort)srcPort) >> 8);
            header[o++] = (byte) (((ushort)srcPort) & 0xff);

            header[o++] = (byte)(((ushort)destPort) >> 8);
            header[o++] = (byte) (((ushort)destPort) & 0xff);

            header[o++] = (byte)(((uint)seqNumber) >> 24);
            header[o++] = (byte)(((uint)seqNumber) >> 16);
            header[o++] = (byte)(((uint)seqNumber) >> 8);
            header[o++] = (byte) (((uint)seqNumber) & 0xff);

            header[o++] = (byte)(((uint)ackNumber) >> 24);
            header[o++] = (byte)(((uint)ackNumber) >> 16);
            header[o++] = (byte)(((uint)ackNumber) >> 8);
            header[o++] = (byte) (((uint)ackNumber) & 0xff);

            byte off = (byte) ((TcpHeader.MinSize + optlen) >>  2);
            //            DebugPrint("BuildHeader: offset is {0}\n", off);
            header[o++] = (byte) (off << (byte) 4);
            header[o++] = flags;

            header[o++] = (byte)(((ushort)windowSize) >> 8);
            header[o++] = (byte) (((ushort)windowSize) & 0xff);

            // checksum
            header[o++] = 0;
            header[o++] = 0;

            header[o++] = (byte)(((ushort)urgPtr) >> 8);
            header[o++] = (byte) (((ushort)urgPtr) & 0xff);
            //            DebugPrint("BuildHeader: Complete\n");
        }

        public static void DeleteTimers(TCP tcpSession)
        {
            slowWheel.DeleteTimerEvent(ref tcpSession.retransmitTimeoutNode);
            slowWheel.DeleteTimerEvent(ref tcpSession.connectionTimeoutNode);
            slowWheel.DeleteTimerEvent(ref tcpSession.fin2MslTimeoutNode);
            fastWheel.DeleteTimerEvent(ref tcpSession.delayAckTimeoutNode);
        }

        public static void DisposeTcpSession(TCP tcpSession)
        {
            if (tcpSession.disposed == true) {
                return;
            }

            tcpSession.disposed = true;

            //check to see whether this was a passive or active open
            if (tcpSession.activeOpen) {
                activeHash.RemoveTcpSession(tcpSession, tcpSession.chainedHashLLNode);
            }
            else {
                passiveHash.RemoveTcpSession(tcpSession, tcpSession.chainedHashLLNode);
            }

            tcpSession.currentState = TcpState.CLOSED;

            DeleteTimers(tcpSession);

            TcpVectorQueueByte txBuffer = tcpSession.txContainer.Acquire();
            uint bufferSize = txBuffer.Size();
            if (bufferSize > 0) {
                txBuffer.ReleaseDataFromTxBuffer(bufferSize);
                txBuffer.SetTxBuffTotalOffset(tcpSession.sndNxt - tcpSession.sndUna);
            }
            tcpSession.txContainer.Release(txBuffer);

        }

        public long TimeWaiting()
        {
            return this.timeWaiting;
        }

        //app level send
        public int Send(Bytes data)
        {
            TcpVectorQueueByte txBuffer = txContainer.Acquire();
            int bytesLeft = data.Length;
            int rc = bytesLeft;
            DebugPrint("Sending {0} bytes\n", data.Length);
            while (bytesLeft != 0) {
                Bytes dataToSave = null;
                if (bytesLeft > (txBufferSize - txBuffer.Size())) {
                    uint offset = txBufferSize - txBuffer.Size();
                    if (offset > 0) {
                        dataToSave = Bitter.SplitOff(ref data, (int) offset);
                        txBuffer.AddTail(data, 0, offset);
                        bytesLeft -= (int) offset;
                    }
                    else {
                        dataToSave = data;
                    }
                }
                else {
                    txBuffer.AddTail(data, 0, (uint) bytesLeft);
                    bytesLeft = 0;
                }
                //execute internal send
                if (bytesLeft > 0) {
                    txContainer.Release(txBuffer);
                    SendPacket(TcpFlags.ACK, false);
                    tcpWriterWait.WaitOne();
                    if (currentState != TcpState.ESTABLISHED) {
                        DebugPrint("Connection closed!\n");
                        //delete dataToSave;
                        return -1;
                    }
                    txBuffer = txContainer.Acquire();
                    VTable.Assert(dataToSave != null);
                    data = dataToSave;
                    dataToSave = null;
                }
            }
            txContainer.Release(txBuffer);
            SendPacket(TcpFlags.ACK, false);
            return rc;
        }


        public void ProcessOptions(Bytes packet, int optionsSize)
        {
            int offset = EthernetHeader.Size + IpHeader.Size + TcpHeader.MinSize;
            int limit = offset + optionsSize;
            DebugPrint("Options size {0}\n", optionsSize);
            for(int i = offset; i < limit; i++) {
                byte p = packet[i];
                if (p == (byte) TcpOptions.EOL || p == (byte) TcpOptions.NOP) {
                    continue;
                }
                if (p == (byte) TcpOptions.MSS) {
                    i++;
                    byte s = packet[i++];
                    DebugStub.Assert(s == 4);
                    VTable.Assert(s == 4);
                    byte[] toConvert;
                    toConvert = new byte[2];
                    toConvert[0] = packet[i++];
                    toConvert[1] = packet[i];
                    ushort mss;
                    mss = NetworkBitConverter.ToUInt16(toConvert, 0);
                    DebugPrint("Reveived MSS option of {0}\n", mss);
                    sndMss = mss;
                }
                else {
                    byte s = packet[i + 1];
                    DebugPrint("Unhandled options: {0} size {1}...\n", (int)p, (int)s);
                    i += ((int)s-1);
                }
            }
        }


        public static void SendError(IpHeader ipHeader, TcpHeader tcpHeader, TcpFlags flags)
        {
            Bytes header;
            Bytes ethernetHeader;
            if (flags == TcpFlags.RST) {
                DebugPrint("Sending RST\n");
                header = new Bytes(new byte[IpHeader.Size + TcpHeader.MinSize]);
                ethernetHeader = new Bytes(new byte[EthernetHeader.Size]);

                BuildHeader (header, ipHeader.destAddress, ipHeader.srcAddress,
                             tcpHeader.destPort, tcpHeader.srcPort, (byte) TcpFlags.RST,
                             tcpHeader.ackNumber, 0, 0, 0, 0, 0, 0);
                TcpHeader.SetTcpChecksum(header, 0, TcpHeader.MinSize);
                IP.SendOutgoingPacket(ethernetHeader, header, ipHeader.srcAddress);

            }
            else if (((TcpFlags.RST & flags) != 0) &&
                     ((TcpFlags.ACK & flags) != 0)) {
                DebugPrint("Sending RST | ACK\n");
                header = new Bytes(new byte[IpHeader.Size + TcpHeader.MinSize]);
                ethernetHeader = new Bytes(new byte[EthernetHeader.Size]);

                uint headerLength = (uint) (EthernetHeader.Size + IpHeader.Size + tcpHeader.dataOffset);
                uint segmentLength = (uint) (ipHeader.totalLength - IpHeader.Size) - headerLength;
                BuildHeader (header, ipHeader.destAddress, ipHeader.srcAddress, tcpHeader.destPort,
                             tcpHeader.srcPort, (byte) (TcpFlags.RST | TcpFlags.ACK),
                             0, tcpHeader.seqNumber + segmentLength, 0, 0, 0, 0, 0);
            }
            else {
                DebugStub.Assert(false);
            }
        }

        private Bytes GetNextBuffer(out uint seqNmb)
        {
            TcpVectorQueueByte txBuffer = txContainer.Acquire();

            uint txBufferOffset = (this.sndNxt - this.sndUna);
            uint numBytes = (txBuffer.Size() - txBufferOffset);

            DebugPrint("size {0} offset {1} bytes {2}\n",
                       txBuffer.Size(), txBufferOffset, numBytes);

            seqNmb = this.sndNxt;

            if (txBuffer.Size() == 0  || numBytes == 0 ||
                (this.sndWnd < 2*this.sndMss)) {
                 txContainer.Release(txBuffer);
                 return null;
            }

            int bufLen;
            int bufStart;
            int bufByteToSend;

            Bytes targetBuffer = txBuffer.GetCurrentBuffer(out bufStart, out bufLen, out bufByteToSend,
                                                                      (int) txBufferOffset);

            //"bufStart" represents the oficial start of the buffer (unacknowledged data to be sent
            //"bufByteToSend" represents that next byte to be sent
            if (bufByteToSend != bufStart) {
                if (bufByteToSend < bufStart) {
                    DebugStub.Break();
                }
                bufLen = bufLen - (bufByteToSend - bufStart);
            }
            //we ended at the end of a previous buffer
            //on a new buffer, bufByteToSend is always equal to bufStart
            if (bufLen == 0) {
                targetBuffer = txBuffer.GetNextBuffer(out bufStart, out bufLen);
                DebugPrint("GetNextBuffer result start {0} length {1}\n",
                           bufStart, bufLen);
                bufByteToSend = bufStart;
            }
            DebugPrint("GetCurrentBuffer result start {0} length {1} offset {2}\n",
                       bufStart, bufLen, bufByteToSend);

            DebugStub.Assert(targetBuffer != null);
            VTable.Assert(targetBuffer != null);

            int pcktLen = Math.Min((int) numBytes, this.sndMss);
            if(pcktLen > 1460 || pcktLen < 0) {
                DebugStub.WriteLine("sndNxt {0} sndUna {1} sndMax {2} buffer size {3}",
                                    DebugStub.ArgList(this.sndNxt, this.sndUna, this.sndMax, txBuffer.Size()));
                DebugStub.WriteLine("bufStart {0} bufLen {1} bufByteToSend{2}",
                                    DebugStub.ArgList(bufStart, bufLen, bufByteToSend));
                DebugStub.Break();
            }
            Bytes cpBuf  = new Bytes(new byte[pcktLen]);

            while(pcktLen > 0) {
                //copy the lesser of the space left in
                //the send buffer and the space left in the packet
                int cpLen = Math.Min(bufLen, pcktLen);
                int cpOff = 0;
                try {
                    Bitter.Copy(cpBuf, cpOff, cpLen, targetBuffer, (int) bufByteToSend);
                }
                catch (Exception e) {
                    DebugStub.Print("copy failed exception {0}\n", DebugStub.ArgList(e.ToString()));
                    DebugStub.Print("cpOff {0} cplen {1} cp.Len {2} targetoffset {3} targetlen {4}length {5}\n",
                                    DebugStub.ArgList(cpOff, cpLen, cpBuf.Length, bufByteToSend, (targetBuffer).Length,
                                              pcktLen));
                    DebugStub.Break();
                    DebugStub.Assert(false);
                    VTable.Assert(false);
                }
                //                DebugStub.WriteLine("pcktLen {0} cpOff {1} bufLen {2} cpLen {3}\n",
                //                    DebugStub.ArgList(pcktLen, cpOff, bufLen, cpLen));
                pcktLen -= cpLen;
                cpOff += cpLen;
                bufLen -= cpLen;

                //we've run out of buffer to copy from and we still have space
                //in this packet...
                if (bufLen == 0) {
                    txBuffer.AdvanceBufferOffset((uint) cpLen);
                    if (pcktLen != 0) {
                        targetBuffer = txBuffer.GetNextBuffer(out bufStart, out bufLen);
                        DebugPrint("GetNextBuffer result start {0} length {1}\n",
                                   bufStart, bufLen);
                        bufByteToSend = bufStart;
                    }
                }
                else {
                    txBuffer.AdvanceBufferOffset((uint) cpLen);
                    bufByteToSend += cpLen;
                }
            }
            this.sndWnd -= (uint) cpBuf.Length;
            this.sndNxt += (uint) cpBuf.Length;
            if (TcpHeader.SeqGreater(this.sndNxt, this.sndMax)) {
                this.sndMax = this.sndNxt;
            }
            txBuffer.SetTxBuffTotalOffset(this.sndNxt - this.sndUna);
            txContainer.Release(txBuffer);
            return cpBuf;
        }

        public void SendPacket(TcpFlags flags, bool resetSndNxt)
        {
           using (thisLock.Lock()) {
                //three factors decide how many packets we generate
                //1) the amount of data waiting to be sent in the txBuffer
                //2) how many bytes are available in the remote window
                //3) the number of packets available in the NIC
                //we want the min of these three
                bool dataToSend = false;

                if (resetSndNxt == true) {
                    sndNxt = sndUna;
                    DebugStub.Print("SendPacket: sendWnd {0} rcvNxt {1} rcvWnd {2} " +
                                    " flags 0x{4:x}, resetSndNxt {5}\n",
                                    DebugStub.ArgList(this.sndWnd, this.rcvNxt, this.rcvWnd,
                                              (uint) flags, sndNxt, resetSndNxt));
                }

                DebugPrint("SendPacket: sendWnd {0} rcvNxt {1} rcvWnd {2} " +
                           " flags 0x{3:x}, resetSndNxt {4}\n",
                           this.sndWnd, this.rcvNxt, this.rcvWnd, (uint) flags, sndNxt);
#if false
                int bufferedBytes = (int) Math.Min (sndWnd, txBuffer.Size() - txBufferOffset);
                if (bufferedBytes == 0 &&
                    sndWnd == 0 &&
                    TcpHeader.SeqLess(sndNxt, sndMax)) {
                    DebugStub.Print("zero window but resending....\n");
                    bufferedBytes = (int) (txBuffer.Size() - txBufferOffset);
                }
#endif
                uint seqNmb = 0;
                Bytes pckt = GetNextBuffer(out seqNmb);

                bool ackOnly = false;

                while(pckt != null) {
                    dataToSend = true;
                    Bytes header =
                        new Bytes(new byte[EthernetHeader.Size + IpHeader.Size + TcpHeader.MinSize]);
                    if (pckt.Length < this.sndMss) {
                        flags |= TcpFlags.PSH;
                    }
                    BuildHeader (header, this.remoteIPAddress, this.localIPAddress, this.remotePort,
                                 this.localPort, (byte) flags, seqNmb, this.rcvNxt, this.rcvWnd,
                                 0, (short) pckt.Length, 0, EthernetHeader.Size);
                    TcpHeader.SetTcpChecksum(header, pckt, EthernetHeader.Size, (ushort) TcpHeader.MinSize);
                    IP.SendOutgoingPacket(header, pckt, this.remoteIPAddress);
                    pckt = GetNextBuffer(out seqNmb);
                }

                if (this.sndMax == this.sndUna &&
                    needFin == true) {
                    DebugPrint("Sending FIN\n");
                    flags |= TcpFlags.FIN;
                    switch(this.currentState) {
                        case TcpState.ESTABLISHED:
                            currentState = TcpState.FIN_WAIT_1;
                            DebugPrint("Sending FIN -- moving to state FIN_WAIT_1");
                            break;
                        case TcpState.CLOSE_WAIT:
                            currentState = TcpState.LAST_ACK;
                            DebugPrint("Sending FIN -- moving to state LAST_ACK");
                            break;
                        default :
                            DebugStub.WriteLine("Sending FIN from state {0}??", DebugStub.ArgList(this.currentState));
                            DebugStub.Break();
                            break;
                    }
                }
                if (dataToSend == false &&
                    (ackNow == true || ((flags & (TcpFlags.SYN | TcpFlags.FIN)) != 0))) {
                    ushort optionsSize = 0;
                    Bytes ethernetHeader = new Bytes(new byte[EthernetHeader.Size]);
                    Bytes header;
                    if ((flags & TcpFlags.SYN) != 0) {
                        DebugPrint("Creating options for SYN packet srcmss {0}\n", srcMSS);
                        header = new Bytes(new byte[IpHeader.Size + TcpHeader.MinSize + 4]);

                        ushort mss;
                        ushort o = IpHeader.Size + TcpHeader.MinSize;
                        header[o++] = (byte) TcpOptions.MSS;
                        header[o++] = 4;
                        NetworkBitConverter.PutBytes(TCP.srcMSS, header.Array, header.Start + o);
                        optionsSize = 4;
                    }
                    else {
                        DebugPrint("sending packet either FIN or ACK flags {0}\n", flags);
                        header = new Bytes(new byte[IpHeader.Size + TcpHeader.MinSize]);
                    }
                    BuildHeader (header, this.remoteIPAddress, this.localIPAddress, this.remotePort,
                                 this.localPort, (byte) flags, seqNmb, this.rcvNxt,
                                 this.rcvWnd, optionsSize, 0, 0, 0);
                    TcpHeader.SetTcpChecksum(header, 0, (ushort) (TcpHeader.MinSize + optionsSize));
                    if ((flags & (TcpFlags.SYN | TcpFlags.FIN)) != 0) {
                        this.sndNxt++;
                        if (TcpHeader.SeqGreater(this.sndNxt, this.sndMax)) {
                            this.sndMax = this.sndNxt;
                        }
                    }
                    else {
                        ackOnly = true;
                    }
                    IP.SendOutgoingPacket(ethernetHeader, header, remoteIPAddress);
                }
                ackNow = false;

                fastWheel.DeleteTimerEvent(ref this.delayAckTimeoutNode);

                if (ackOnly == false) {
                    if(resetSndNxt == false) {
                        this.timeoutValue = 500;
                    }
                    slowWheel.AddTimerEvent(this.timeoutValue, this,
                                            this.retransmitTimeoutDelegate,
                                            ref this.retransmitTimeoutNode);
                }
           }
        }

        public Bytes[] PopAllData()
        {
            TcpVectorQueueByte rxBuffer = rxContainer.Acquire();

            if (rxBuffer.Size() == 0) {
                 rxContainer.Release(rxBuffer);
                 return null;
            }

            int cnt = rxBuffer.Count();
            VTable.Assert(cnt > 0);

            Bytes[] ba = new Bytes[cnt];

            for(int i = 0; i < cnt; i++) {

                Bytes buf;
                uint startOffset;
                uint length;

                buf = rxBuffer.ExtractHead(out startOffset, out length);
                VTable.Assert(buf != null);

                if (startOffset == 0 && length == buf.Length) {
                    ba[i] = buf;
                }
                else if (startOffset == 0 && length < buf.Length) {
                    VTable.Assert(buf != null);
                    //XXX without dummy, Sing# gets confused and is unsure which method
                    //is called.
                    Bytes dummy = buf;
                    Bytes leftOver = Bitter.SplitOff(ref dummy, (int) length);
                    //delete leftOver;
                    ba[i] = buf;
                }
                else {
                    Bytes buffer = new Bytes(new byte[length]);
                    Bitter.Copy(buffer, 0, (int) length, buf, (int) startOffset);
                    //delete buf;
                    ba[i] = buffer;
                }
            }
            //The window is now fully open
            rcvWnd = DefaultRxWinSize;
            rxContainer.Release(rxBuffer);

            return ba;
        }
        public Bytes PopData()
        {
            TcpVectorQueueByte rxBuffer = rxContainer.Acquire();

            Bytes buf;
            uint startOffset;
            uint length;
            buf = rxBuffer.ExtractHead(out startOffset, out length);
            if (buf != null) {
                this.rcvWnd += length;
            }
            rxContainer.Release(rxBuffer);
            if (buf == null) {
                return null;
            }
            else if (startOffset == 0 && length == buf.Length) {
                 return buf;
            }
            else if (startOffset == 0 && length < buf.Length) {
                VTable.Assert(buf != null);
                //XXX without dummy, Sing# gets confused and is unsure which method
                //is called.
                Bytes dummy = buf;
                Bytes leftOver = Bitter.SplitOff(ref dummy, (int) length);
                //delete leftOver;
                return buf;
            }

            Bytes buffer = new Bytes(new byte[length]);
            Bitter.Copy(buffer, 0, (int) length, buf, (int) startOffset);
            //delete buf;

            return buffer;
        }


        public void PushPacket(Bytes packet, uint packetLength, TcpHeader tcpHeader)
        {

            int offset = EthernetHeader.Size + IpHeader.Size + tcpHeader.dataOffset;
            if (tcpHeader.dataOffset > TcpHeader.MinSize) {
                DebugPrint("WARNING: processing data packet and ignoring options??\n");
            }
            if (offset == packetLength) {
                DebugPrint("Received pure ack packet..\n");
                //delete packet;
                SendPacket(TcpFlags.ACK, false);
                return;
            }
            Bytes packetData = Bitter.SplitOff(ref packet, offset);
            //delete packet;
            packetLength = packetLength - (uint) offset;
            TcpVectorQueueByte rxAssembly = rxAssemblyContainer.Acquire();
            TcpVectorQueueByte rxBuffer = rxContainer.Acquire();

            if (tcpHeader.seqNumber == this.rcvNxt) {

                if (packetLength > this.rcvWnd) {
                    packetLength = rcvWnd;
                }
                DebugPrint("adding packet to rxbuffer of size {0} byte length {1}\n", packetLength, packetData.Length);
                rxBuffer.AddTail(packetData, tcpHeader.seqNumber, packetLength);
                this.rcvWnd = this.rcvWnd - packetLength;

                //avoid silly window syndrome
                if (this.rcvWnd < this.maxSegSize * 2) {
                    this.rcvWnd = 0;
                    DebugPrint("rcvWnd closed to 0 to avoid silly window syndrom\n");
                }
                this.rcvNxt += packetLength;

                if (rxAssembly.Empty == false) {
                    DebugStub.Print("going into assembly queue...\n");
                    int startOffset;
                    int length;
                    TcpVectorQueueByte.TcpVectorNode tcpVNode;
                    Bytes data;
                    while ((tcpVNode = rxAssembly.PopNextContiguousSegment(this.rcvNxt, this.rcvWnd)) != null) {
                        VTable.Assert(tcpVNode.length <= this.rcvWnd);
                        this.rcvWnd = this.rcvWnd - tcpVNode.length;
                        this.rcvNxt += tcpVNode.length;
                        rxBuffer.AddTail(tcpVNode);
                    }
                }

                //two segments in a row...ack immediately
                if (fastWheel.DeleteTimerEvent(ref this.delayAckTimeoutNode) == true) {
                    DebugPrint("Received two segments in a row...ack'ing immediately\n");
                    ackNow = true;
                }
                else {
                    //delay the ack, hoping for an app message to piggy back
                    DebugPrint("Setting the ack delay timer\n");
                    fastWheel.AddTimerEvent(200, this,
                                            this.delayAckTimeoutDelegate,
                                            ref this.delayAckTimeoutNode);
                }
                //signal app thread if it is waiting for data
                tcpReaderWait.Set();
            }
            else {
                DebugPrint("received packet out of order, immediate ack in progress\n");
                //XXX BUG BUG BUG we've effectively disabled fragmentation for now.
                //                rxAssembly.AddInSeqOrder(packetData, tcpHeader.seqNumber, packetLength);
                ackNow = true;
            }
            rxContainer.Release(rxBuffer);
            rxAssemblyContainer.Release(rxAssembly);

            if (ackNow == true) {
                SendPacket(TcpFlags.ACK, false);
            }
        }

        public static void ProcessIncomingPacket(Bytes packet,
                                                 IpHeader ipHeader)
        {
            //14 byte ethernet header + 20 byte IP header
            int offset = EthernetHeader.Size + IpHeader.Size;
            bool hasOptions = false;
            int packetLength = ipHeader.totalLength + EthernetHeader.Size;
            TcpHeader tcpHeader = new TcpHeader(packet, offset);

            if (!TcpHeader.IsChecksumValid(ipHeader, tcpHeader, packet)) {
                DebugPrint("checksum failed, dropping packet\n");
                //delete packet;
                return;
            }

            int length = ipHeader.totalLength;
            if (tcpHeader.dataOffset < TcpHeader.MinSize ||
                tcpHeader.dataOffset + IpHeader.Size > length) {
                DebugPrint("offset of tcp packet {0} invalid length:{1}\n", tcpHeader.dataOffset, length);
                //delete packet;
                return;
            }
            length = packetLength - (EthernetHeader.Size + IpHeader.Size + tcpHeader.dataOffset);

            //process options
            if ((tcpHeader.dataOffset - TcpHeader.MinSize) > 0) {
                hasOptions = true;
            }

            //DebugPrint("ProcessIncomingPackets: tcp payload length {0}\n", length);
            TCP tcpSession = activeHash.GetTCPSession(ipHeader.srcAddress, tcpHeader.srcPort,
                                                      ipHeader.destAddress, tcpHeader.destPort);
            if (tcpSession == null) {
                tcpSession = passiveHash.GetTCPSession(ipHeader.srcAddress, tcpHeader.srcPort,
                                                       ipHeader.destAddress, tcpHeader.destPort);
                if (tcpSession == null) {
                    DebugStub.Print("Failed to find tcp session for conn {0}:{1} -> {2}:{3}\n", DebugStub.ArgList(
                                    ipHeader.srcAddress, tcpHeader.srcPort,
                                    ipHeader.destAddress, tcpHeader.destPort));
                    //delete packet;
                    return;
                }
            }

            DebugPrint("Received TCP packet source ip {0} source port {1}\n" +
                            "dest ip {2} dest port {3} \nflags 0x{4,2:x} seq {5} ack {6}\n" +
                            "window size {7} length {8}\n", ipHeader.srcAddress, tcpHeader.srcPort,
                            ipHeader.destAddress, tcpHeader.destPort, tcpHeader.flags,
                            tcpHeader.seqNumber, tcpHeader.ackNumber, tcpHeader.windowSize,
                            length);

            //header prediction fast path
            if (tcpSession.currentState == TcpState.ESTABLISHED &&
                (tcpHeader.flags & (byte) (TcpFlags.SYN | TcpFlags.RST | TcpFlags.URG | TcpFlags.ACK)) == (int) TcpFlags.ACK &&
                (tcpHeader.seqNumber == tcpSession.rcvNxt) &&
                //                (tcpHeader.windowSize == tcpSession.sndWnd) &&
                (tcpSession.sndNxt == tcpSession.sndMax)) {

                if (length ==  0) {
                    if (TcpHeader.SeqGreater(tcpHeader.ackNumber, tcpSession.sndUna) &&
                        TcpHeader.SeqLEQ(tcpHeader.ackNumber, tcpSession.sndMax)) {
                        uint acked = tcpHeader.ackNumber - tcpSession.sndUna;

                        TcpVectorQueueByte txBuffer = tcpSession.txContainer.Acquire();

                        tcpSession.sndUna = tcpHeader.ackNumber;
                        tcpSession.sndWnd = tcpHeader.windowSize;
                        tcpSession.sndWn1 = tcpHeader.seqNumber;
                        tcpSession.sndWn2 = tcpHeader.ackNumber;

                        if (acked > 0) {
                            txBuffer.ReleaseDataFromTxBuffer(acked);
                        }
                        txBuffer.SetTxBuffTotalOffset(tcpSession.sndNxt - tcpSession.sndUna);

                        slowWheel.DeleteTimerEvent(ref tcpSession.retransmitTimeoutNode);

                        bool sendit = false;
                        if (TcpHeader.SeqGreater(tcpSession.sndMax, tcpSession.sndUna)) {
                            tcpSession.timeoutValue = 500;
                            slowWheel.AddTimerEvent(tcpSession.timeoutValue, tcpSession,
                                                    tcpSession.retransmitTimeoutDelegate,
                                                    ref tcpSession.retransmitTimeoutNode);
                        }
                        else {
                            sendit = true;
                        }

                        tcpSession.txContainer.Release(txBuffer);
                        tcpSession.tcpWriterWait.Set();

                        if (sendit == true || tcpSession.needFin == true) {
                            tcpSession.SendPacket(TcpFlags.ACK, false);
                        }

                        return;
                    }
                }
                else if (tcpHeader.ackNumber == tcpSession.sndUna) {

                    int fast_offset = EthernetHeader.Size + IpHeader.Size + tcpHeader.dataOffset;

                    Bytes packetData = Bitter.SplitOff(ref packet, fast_offset);
                    //delete packet;
                    packetLength = packetLength - fast_offset;

                    TcpVectorQueueByte rxAssembly = tcpSession.rxAssemblyContainer.Acquire();
                    TcpVectorQueueByte rxBuffer = tcpSession.rxContainer.Acquire();

                    if (rxAssembly.Empty == true &&
                        tcpSession.rcvWnd >= packetLength) {

                        rxBuffer.AddTail(packetData, tcpHeader.seqNumber, (uint) packetLength);
                        tcpSession.rcvWnd = tcpSession.rcvWnd - (uint) packetLength;
                        tcpSession.rcvNxt += (uint) packetLength;

                        if (fastWheel.DeleteTimerEvent(ref tcpSession.delayAckTimeoutNode) == true) {
                                DebugPrint("Received two segments in a row...ack'ing immediately\n");
                                tcpSession.ackNow = true;
                        }
                        else {
                            //delay the ack, hoping for an app message to piggy back
                            fastWheel.AddTimerEvent(200, tcpSession,
                                                    tcpSession.delayAckTimeoutDelegate,
                                                    ref tcpSession.delayAckTimeoutNode);
                        }
                    }

                    tcpSession.rxContainer.Release(rxBuffer);
                    tcpSession.rxAssemblyContainer.Release(rxAssembly);

                    //signal app thread if it is waiting for data
                    tcpSession.tcpReaderWait.Set();
                    return;
                }
            }

            DebugPrint("tcpSession state is currently {0}\n", tcpSession.currentState);

            if(tcpSession.currentState == TcpState.LISTEN) {
                //ignore RST
                if ((tcpHeader.flags & (byte) TcpFlags.RST) != 0) {
                    DebugPrint("Got RST in Listen state...discarding\n");
                    //delete packet;
                    return;
                }
                if ((tcpHeader.flags & (byte) TcpFlags.FIN) != 0) {
                    DebugPrint("Got FIN in Listen state...discarding\n");
                    //delete packet;
                    return;
                }
                if ((tcpHeader.flags & (byte) TcpFlags.ACK) != 0) {
                    DebugPrint("Got packet with ack flag in listen state...sending RST\n");
                    SendError(ipHeader, tcpHeader, TcpFlags.RST);
                    //delete packet;
                    return;
                }

                //complete the connection
                if ((tcpHeader.flags & (byte) TcpFlags.SYN) == 0) {
                    //delete packet;
                    return;
                }

                if (tcpSession.acceptQueueLength >= tcpSession.acceptQueueMaxSize) {
                    DebugStub.Print("No space left on listen queue...dumping packet\n");
                    //delete packet;
                    return;
                }
                DebugPrint("Received SYN on listening socket.  Sending syn-ack queue length {0}\n",
                           (tcpSession.acceptQueueLength));
                //see if there is space in the receivers accept queue
                TCP activeTcpSession = new TCP();
                activeTcpSession.localIPAddress = ipHeader.destAddress;
                activeTcpSession.localPort = tcpHeader.destPort;

                activeTcpSession.InternalConnect(ipHeader.srcAddress, tcpHeader.srcPort);
                activeTcpSession.chainedHashLLNode = activeHash.InsertNewSession(activeTcpSession);
                activeTcpSession.listenSocket = tcpSession;
                tcpSession.acceptQueueLength++;

                activeTcpSession.rcvNxt = tcpHeader.seqNumber + 1;
                activeTcpSession.irs    = tcpHeader.seqNumber;
                activeTcpSession.sndWn1 = tcpHeader.seqNumber - 1;
                activeTcpSession.sndNxt = activeTcpSession.iss;
                activeTcpSession.sndMax = activeTcpSession.iss;
                activeTcpSession.sndUna = activeTcpSession.iss;
                activeTcpSession.sndWnd = tcpHeader.windowSize;
                activeTcpSession.activeOpen = true;
                activeTcpSession.currentState = TcpState.SYN_RECEIVED;

                if (hasOptions == true) {
                    activeTcpSession.ProcessOptions(packet,
                                                    (tcpHeader.dataOffset - TcpHeader.MinSize));
                }

                activeTcpSession.SendPacket(TcpFlags.SYN | TcpFlags.ACK, false);
                slowWheel.AddTimerEvent(75000, activeTcpSession,
                                        activeTcpSession.connectionTimeoutDelegate,
                                        ref activeTcpSession.connectionTimeoutNode);
                //delete packet;
                return;
            }
            else if (tcpSession.currentState == TcpState.SYN_SENT) {
                bool ackRcvd = false;
                if ((tcpHeader.flags & (byte) TcpFlags.FIN) != 0) {
                    DebugPrint("Got FIN in syn_sent state...discarding\n");
                    //delete packet;
                    return;
                }
                if ((tcpHeader.flags & (byte) TcpFlags.ACK) != 0) {
                    ackRcvd = true;
                    if (TcpHeader.SeqLEQ(tcpHeader.ackNumber, tcpSession.iss) ||
                        TcpHeader.SeqGreater(tcpHeader.ackNumber, tcpSession.sndNxt)) {
                        if ((tcpHeader.flags & (byte) TcpFlags.RST) != 0) {
                            DebugPrint("SYN_SENT: Received bogus ack with RST dropping...\n");
                            //delete packet;
                            return;
                        }
                        SendError(ipHeader, tcpHeader, TcpFlags.RST);
                        //delete packet;
                        return;
                    }
                    DebugStub.Assert(tcpHeader.ackNumber >= tcpSession.sndUna &&
                                     tcpHeader.ackNumber <= tcpSession.sndNxt);
                }
                if ((tcpHeader.flags & (byte) TcpFlags.RST) != 0) {
                    DebugStub.Print("SYN_SENT: received RST\n");
                    tcpSession.currentState = TcpState.CLOSED;
                    tcpSession.tcpConnWait.Set();
                    DisposeTcpSession(tcpSession);
                    //delete packet;
                    return;
                }
                if ((tcpHeader.flags & (byte) TcpFlags.SYN) == 0) {
                    DebugPrint("SYN_SENT: No SYN flag in packet...dropping\n");
                    //delete packet;
                    return;
                }
                //ok..we've got a syn and no RST.  We can continue the connection
                //                DebugPrint("Received SYN ack value {0} in SYN_SENT state\n", ackRcvd);
                tcpSession.rcvNxt = tcpHeader.seqNumber + 1;
                tcpSession.irs = tcpHeader.seqNumber;
                tcpSession.sndWn1 = tcpHeader.seqNumber - 1;
                if (ackRcvd == true) {
                    tcpSession.sndUna = tcpHeader.ackNumber;

                    if (TcpHeader.SeqGreater(tcpSession.sndUna, tcpSession.iss)) {
                        //DebugPrint("Entering state ESTABLISHED...woohoo! sending ack\n");
                        ////delete the connection timeout timer.
                        slowWheel.DeleteTimerEvent(ref tcpSession.connectionTimeoutNode);
                        slowWheel.DeleteTimerEvent(ref tcpSession.retransmitTimeoutNode);

                        tcpSession.currentState = TcpState.ESTABLISHED;
                        tcpSession.sndWnd = tcpHeader.windowSize;
                        tcpSession.sndWn1 = tcpHeader.seqNumber;
                        tcpSession.sndWn2 = tcpHeader.ackNumber;
                        if (hasOptions == true) {
                            tcpSession.ProcessOptions(packet,
                                                      (tcpHeader.dataOffset - TcpHeader.MinSize));
                        }
                        tcpSession.ackNow = true;
                        tcpSession.SendPacket(TcpFlags.ACK, false);
                    }
                    //delete packet;
                }
                else {
                    DebugPrint("Simultaneous open! ack!\n");
                    DebugStub.Assert(false);
                    //delete packet;
                }
                tcpSession.tcpConnWait.Set();
                return;
            }
            else if (tcpSession.currentState == TcpState.CLOSED) {
                //on a closed socket packets containing RST get an RST back.
                if ((tcpHeader.flags & (byte) TcpFlags.RST) == 0) {
                    DebugPrint("Received packet on closed socket...sending RST\n");
                    if ((tcpHeader.flags & (byte) TcpFlags.FIN) != 0) {
                        //delete packet;
                        return;
                    }
                    if ((tcpHeader.flags & (byte) TcpFlags.ACK) != 0) {
                        SendError(ipHeader, tcpHeader, TcpFlags.RST);
                    }
                    else {
                        SendError(ipHeader, tcpHeader, TcpFlags.RST | TcpFlags.ACK);
                    }
                }
                //delete packet;
                return;
            }
            else {
                //first check whether the sequence number is valid
                bool badSegment = false;
                if (length == 0 && tcpSession.rcvWnd == 0) {
                    if (tcpHeader.seqNumber != tcpSession.rcvNxt) {
                        badSegment = true;
                    }
                }
                else if (length == 0 && tcpSession.rcvWnd > 0) {
                    if (TcpHeader.SeqLess(tcpHeader.seqNumber, tcpSession.rcvNxt) ||
                        TcpHeader.SeqGEQ(tcpHeader.seqNumber, (tcpSession.rcvNxt + tcpSession.rcvWnd))) {
                        badSegment = true;
                    }
                }
                else if (length > 0 && tcpSession.rcvWnd == 0) {
                    badSegment = true;
                }
                else {
                    if (TcpHeader.SeqLess(tcpHeader.seqNumber, tcpSession.rcvNxt) ||
                        TcpHeader.SeqGEQ(tcpHeader.seqNumber, (tcpSession.rcvNxt + tcpSession.rcvWnd))) {
                        badSegment = true;
                    }
                    else  if (TcpHeader.SeqLess((tcpHeader.seqNumber + (uint) length - 1), tcpSession.rcvNxt) ||
                              TcpHeader.SeqGEQ((tcpHeader.seqNumber + (uint) length - 1),
                                               (tcpSession.rcvNxt + tcpSession.rcvWnd))) {
                        badSegment = true;
                    }
                }
                if (badSegment == true) {
                    DebugPrint("Received bad segment in state {0}\n", tcpSession.currentState);
                    DebugPrint("rcvNxt {0} rcvwnd {1} rcvnxt + rcvwnd {2} seqnumber {3}\n",
                               tcpSession.rcvNxt, tcpSession.rcvWnd, tcpSession.rcvNxt + tcpSession.rcvWnd,
                               tcpHeader.seqNumber);
                    if ((tcpHeader.flags & (byte) TcpFlags.RST) == 0) {
                        tcpSession.ackNow = true;
                        tcpSession.SendPacket(TcpFlags.ACK, false);
                    }
                    //delete packet;
                    return;
                }
                //check the RST bit next
                if ((tcpHeader.flags & (byte) TcpFlags.RST) != 0) {
                    DebugPrint("received RST\n");
                    if (tcpSession.currentState == TcpState.SYN_RECEIVED) {
                        //ok we need to propagate this up to the client somehow
                        DisposeTcpSession(tcpSession);
                        //send unsolicited "connection refused" error
                        //delete packet;
                        return;
                    }
                    else if (tcpSession.currentState >= TcpState.ESTABLISHED &&
                             tcpSession.currentState <= TcpState.CLOSE_WAIT) {
                        //send unsolicited "connection reset by peer"
                        DisposeTcpSession(tcpSession);
                        //delete packet;
                        return;
                    }
                    else {
                        //no error to propagate here
                        DisposeTcpSession(tcpSession);
                        //delete packet;
                        return;
                    }
                }
                //check for the SYN bit
                if ((tcpHeader.flags & (byte) TcpFlags.SYN) != 0) {
                    DebugPrint("received SYN in unexpected state {1}\n", tcpSession.currentState);
                    Bytes header = GetHeader(IpHeader.Size + TcpHeader.MinSize);
                    Bytes ethernetHeader = GetHeader(EthernetHeader.Size);
                    BuildHeader (header, ipHeader.destAddress, ipHeader.srcAddress,
                                 tcpHeader.destPort, tcpHeader.srcPort, (byte) TcpFlags.RST,
                                 tcpSession.sndNxt, tcpSession.rcvNxt, tcpSession.rcvWnd, 0, 0, tcpSession.sndUp, 0);
                    TcpHeader.SetTcpChecksum(header, 0, TcpHeader.MinSize);
                    IP.SendOutgoingPacket(ethernetHeader, header, ipHeader.srcAddress);
                    DisposeTcpSession(tcpSession);
                    //delete packet;
                    return;
                }
                //ack processing
                if ((tcpHeader.flags & (byte) TcpFlags.ACK) == 0) {
                    DebugPrint("No ack...discarding packet\n");
                    //delete packet;
                    return;
                }
                //XXX BUG BUG BUG if listener closed we need to close this connection.
                if (tcpSession.currentState == TcpState.SYN_RECEIVED) {
                    if (TcpHeader.SeqLEQ(tcpSession.sndUna, tcpHeader.ackNumber) &&
                        TcpHeader.SeqGEQ(tcpSession.sndNxt, tcpHeader.ackNumber)) {

                        tcpSession.sndWnd = tcpHeader.windowSize;
                        tcpSession.sndWn1 = tcpHeader.seqNumber;
                        tcpSession.sndWn2 = tcpHeader.ackNumber;
                        tcpSession.sndUna = tcpHeader.ackNumber;
                        tcpSession.currentState = TcpState.ESTABLISHED;
                        TCP listener = tcpSession.listenSocket;
                        if (listener == null) {
                            DebugStub.Break();
                        }
                        if (listener.currentState != TcpState.LISTEN) {
                            DebugStub.Break();
                        }

                        DebugPrint("SYN_RECEIVED: Entering ESTABLISHED state tail is {0}\n", listener.acceptQueueTail);

                        listener.acceptQueue[listener.acceptQueueTail] = tcpSession;
                        listener.acceptQueueTail =
                            (listener.acceptQueueTail + 1) % listener.acceptQueueMaxSize;

                        slowWheel.DeleteTimerEvent(ref tcpSession.retransmitTimeoutNode);
                        slowWheel.DeleteTimerEvent(ref tcpSession.connectionTimeoutNode);

                        VTable.Assert(tcpSession.listenSocket != null);
                        listener.tcpConnWait.Set();
                        //delete packet;
                        return;
                    }
                    else {
                        DebugStub.Print("Received out of band sequence number in state SYN_RECEIVED\n");
                        //XXX should cleanup session here
                        SendError(ipHeader, tcpHeader, TcpFlags.RST);
                        //delete packet;
                        return;
                    }
                }
                else if (tcpSession.currentState == TcpState.ESTABLISHED ||
                         tcpSession.currentState == TcpState.FIN_WAIT_1  ||
                         tcpSession.currentState == TcpState.FIN_WAIT_2  ||
                         tcpSession.currentState == TcpState.CLOSE_WAIT  ||
                         tcpSession.currentState == TcpState.CLOSING) {

                    if (TcpHeader.SeqGreater(tcpHeader.ackNumber, tcpSession.sndMax)) {
                        DebugStub.Print("Received ack: {0} > sndMax {1}...discaring\n",
                                        DebugStub.ArgList(tcpHeader.ackNumber, tcpSession.sndMax));
                        tcpSession.ackNow = true;
                        tcpSession.SendPacket(TcpFlags.ACK, false);
                        //delete packet;
                        return;
                    }

                    bool dupAck = false;
                    if (TcpHeader.SeqLEQ(tcpHeader.ackNumber, tcpSession.sndUna)) {
                        if (TcpHeader.SeqLess(tcpSession.sndWn1, tcpHeader.seqNumber) ||
                            (TcpHeader.SeqEQ(tcpSession.sndWn1, tcpHeader.seqNumber) &&
                             (TcpHeader.SeqLEQ(tcpSession.sndWn2, tcpHeader.ackNumber) ||
                              tcpSession.sndWn1 == tcpHeader.ackNumber &&
                              tcpHeader.windowSize > tcpSession.sndWnd))) {
                            DebugPrint("dup ack pure window update updating sndWnd wn1 and wn2\n");
                            tcpSession.sndWnd = tcpHeader.windowSize;
                            tcpSession.sndWn1 = tcpHeader.seqNumber;
                            tcpSession.sndWn2 = tcpHeader.ackNumber;

                            tcpSession.tcpWriterWait.Set();
                        }
                        else {
                            DebugPrint("ignoring duplicate ack\n");
                        }
                        dupAck = true;
                    }

                    if (dupAck == false) {
                        //update the send window
                        //release bytes from the send queue
                        //Need to make sure we send a window update
                        uint acked = tcpHeader.ackNumber - tcpSession.sndUna;

                        //DebugPrint("Acked {0} bytes\n", acked);
                        TcpVectorQueueByte txBuffer = tcpSession.txContainer.Acquire();
                        uint toFree;
                        if (acked > txBuffer.Size()) {
                            DebugPrint("FIN was acked...\n");
                            tcpSession.needFin = false;
                            tcpSession.finacked = true;
                            toFree = txBuffer.Size();
                        }
                        else {
                            toFree = acked;
                        }

                        tcpSession.sndUna = tcpHeader.ackNumber;
                        if (TcpHeader.SeqLess(tcpSession.sndNxt, tcpSession.sndUna)) {
                            //if we're in retransmission mode, drag sndnxt along
                            tcpSession.sndNxt = tcpSession.sndUna;
                        }

                        if (toFree > 0) {
                            DebugPrint("Release {0} bytes\n", toFree);
                            txBuffer.ReleaseDataFromTxBuffer(toFree);
                            txBuffer.SetTxBuffTotalOffset(tcpSession.sndNxt - tcpSession.sndUna);
                            slowWheel.DeleteTimerEvent(ref tcpSession.retransmitTimeoutNode);
                            VTable.Assert(tcpSession.retransmitTimeoutNode == null);
                            tcpSession.tcpWriterWait.Set();
                        }

                        if (TcpHeader.SeqGreater(tcpSession.sndMax, tcpSession.sndNxt)) {
                            tcpSession.timeoutValue = 500;
                            slowWheel.AddTimerEvent(tcpSession.timeoutValue, tcpSession,
                                                    tcpSession.retransmitTimeoutDelegate,
                                                    ref tcpSession.retransmitTimeoutNode);
                        }
                        tcpSession.txContainer.Release(txBuffer);

                        if (TcpHeader.SeqLess(tcpSession.sndWn1, tcpHeader.seqNumber) ||
                            (TcpHeader.SeqEQ(tcpSession.sndWn1, tcpHeader.seqNumber) &&
                             (TcpHeader.SeqLEQ(tcpSession.sndWn2, tcpHeader.ackNumber) ||
                              tcpSession.sndWn1 == tcpHeader.ackNumber &&
                              tcpHeader.windowSize > tcpSession.sndWnd))) {
                            //DebugPrint("updating sndWnd wn1 and wn2\n");
                            tcpSession.sndWnd = tcpHeader.windowSize;
                            tcpSession.sndWn1 = tcpHeader.seqNumber;
                            tcpSession.sndWn2 = tcpHeader.ackNumber;
                        }
                        if (tcpSession.currentState == TcpState.FIN_WAIT_1) {
                            DebugPrint("in FIN_WAIT_1 finacked is {0}\n", tcpSession.finacked);
                            if (tcpSession.finacked == true) {
                                slowWheel.DeleteTimerEvent(ref tcpSession.retransmitTimeoutNode);
                                slowWheel.AddTimerEvent(30000, tcpSession,
                                                        tcpSession.fin2MslTimeoutDelegate,
                                                        ref tcpSession.fin2MslTimeoutNode);
                                tcpSession.currentState = TcpState.FIN_WAIT_2;
                            }
                        }
                        else if (tcpSession.currentState == TcpState.CLOSING) {
                            if (tcpSession.finacked == true) {
                                DebugPrint("CLOSING Received ack for FIN\n");
                                DeleteTimers(tcpSession);
                                tcpSession.currentState = TcpState.TIME_WAIT;
                                slowWheel.AddTimerEvent(30000, tcpSession,
                                                        tcpSession.fin2MslTimeoutDelegate,
                                                        ref tcpSession.fin2MslTimeoutNode);
                                //delete packet;
                                return;
                            }
                        }
                    }//if (dupAck == false)
                }
                else if (tcpSession.currentState == TcpState.LAST_ACK) {
                    if (TcpHeader.SeqLEQ(tcpSession.sndUna, tcpHeader.ackNumber) &&
                        TcpHeader.SeqGEQ(tcpSession.sndNxt, tcpHeader.ackNumber)) {

                        uint acked = tcpHeader.ackNumber - tcpSession.sndUna;

                        //DebugPrint("Acked {0} bytes\n", acked);
                        TcpVectorQueueByte txBuffer = tcpSession.txContainer.Acquire();
                        uint size = txBuffer.Size();
                        tcpSession.txContainer.Release(txBuffer);

                        if (acked > size) {
                            //DebugPrint("our fin was acked in LAST_ACK...disposing of session\n");
                            tcpSession.currentState = TcpState.CLOSED;
                            DisposeTcpSession(tcpSession);
                            return;
                        }
                    }
                }
                else if (tcpSession.currentState == TcpState.TIME_WAIT) {
                    //DebugPrint("time to ack and restart 2msl timer\n");
                    slowWheel.DeleteTimerEvent(ref tcpSession.fin2MslTimeoutNode);
                    slowWheel.AddTimerEvent(30000, tcpSession,
                                            tcpSession.fin2MslTimeoutDelegate,
                                            ref tcpSession.fin2MslTimeoutNode);
                    tcpSession.ackNow = true;
                    tcpSession.SendPacket(TcpFlags.ACK, false);
                    //delete packet;
                    return;
                }
                else {
                    DebugStub.Print("We're in a bad state!!\n");
                    DebugStub.Assert(false);
                }

                if ((tcpHeader.flags & (byte) TcpFlags.URG) != 0) {
                    DebugPrint("Got urgent data!!!\n");
                    DebugStub.Break();
                    //delete packet;
                    return;
                }
                //now we process the data in the segment
                //this method takes care of delayed acks etc.
                tcpSession.PushPacket(packet, (uint) packetLength, tcpHeader);

                //finally, process the fin bit
                if ((tcpHeader.flags & (byte) TcpFlags.FIN) != 0) {
                    tcpSession.rcvNxt++;
                    if ((tcpSession.currentState == TcpState.SYN_RECEIVED) ||
                        (tcpSession.currentState == TcpState.ESTABLISHED)) {
                        DebugPrint("Recieved FIN in {0} state...closing connection moving to CLOSE_WAIT\n",
                                   tcpSession.currentState);
                        tcpSession.currentState = TcpState.CLOSE_WAIT;
                        tcpSession.tcpWriterWait.Set();
                        tcpSession.tcpReaderWait.Set();
                        tcpSession.tcpConnWait.Set();
                    }
                    else if (tcpSession.currentState == TcpState.FIN_WAIT_1) {
                        tcpSession.currentState = TcpState.CLOSING;
                        DebugPrint("Received FIN in FIN_WAIT_1..simultaneous close\n");
                        slowWheel.DeleteTimerEvent(ref tcpSession.retransmitTimeoutNode);
                        slowWheel.AddTimerEvent(30000, tcpSession,
                                                tcpSession.fin2MslTimeoutDelegate,
                                                ref tcpSession.fin2MslTimeoutNode);
                        /* clean up our sending queue */
                        TcpVectorQueueByte txBuffer = tcpSession.txContainer.Acquire();
                        if (txBuffer.Size() > 0) {
                            txBuffer.ReleaseDataFromTxBuffer(txBuffer.Size());
                        }
                        tcpSession.txContainer.Release(txBuffer);
                    }
                    else if (tcpSession.currentState == TcpState.FIN_WAIT_2) {
                        //DebugPrint("Recieved FIN in FIN_WAIT_2 entering TIME_WAIT\n");
                        tcpSession.currentState = TcpState.TIME_WAIT;
                        DeleteTimers(tcpSession);
                        slowWheel.AddTimerEvent(30000, tcpSession,
                                                tcpSession.fin2MslTimeoutDelegate,
                                                ref tcpSession.fin2MslTimeoutNode);
                    }
                    else if (tcpSession.currentState == TcpState.TIME_WAIT) {
                        //not sure what to do here
                    } //else stay in same state
                    tcpSession.ackNow = true;
                    tcpSession.SendPacket(TcpFlags.ACK, false);
                }
            }
        }
    }
}



