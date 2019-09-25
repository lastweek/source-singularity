///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:
//
//  Note:
//

//#define DEBUG_UDP

using System;
using Drivers.Net;
using System.Net.IP;
using System.Threading;
using System.Diagnostics;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity;
using Microsoft.Singularity.V1.Services;
using Microsoft.SingSharp;

//using Allocation = SharedHeapService.Allocation;

namespace Microsoft.Singularity.NetStack2
{

    //4 byte aligned (for ARM) UDPHeader
    //TODO add function to check incoming UDP checksum
    public class UDPHeader
    {
         public ushort srcPort;
         public ushort pad0;
         public ushort dstPort;
         public ushort pad1;
         public ushort length;  // data+header
         public ushort pad2;
         public ushort checksum;

         public const int Size = 8; //size of UDP header

         public UDPHeader(Bytes packet, int index)
         {
             srcPort = NetworkBitConverter.ToUInt16(packet, index);
             index += 2;

             dstPort = NetworkBitConverter.ToUInt16(packet, index);
             index += 2;

             length =  NetworkBitConverter.ToUInt16(packet, index);
             index += 2;

             checksum = NetworkBitConverter.ToUInt16(packet, index);
             //sgc complains
             pad0 = 0;
             pad1 = 0;
             pad2 = 0;
         }


         public static void SetUdpChecksum(Bytes buffer,
                                           Bytes payload,
                                           int ipOffset,
                                           ushort udplength)
         {
             // sum IP pseudo
             ushort ipPayloadSize = 0;
             ushort headerSum = IpHeader.SumPseudoHeader(buffer, ipOffset,
                                                         ref ipPayloadSize);

             DebugStub.Assert(udplength == ipPayloadSize);

             // now add it to the udp header + data
             int ipHeaderSize = (buffer[ipOffset] & 0xf) * 4;
             int udpOffset     = ipOffset + ipHeaderSize;

             ushort udpsum = IpHeader.SumShortValues(buffer, ipOffset+IpHeader.Size, UDPHeader.Size);

             DebugStub.Assert(buffer[udpOffset + 6] == 0);
             DebugStub.Assert(buffer[udpOffset + 7] == 0);

             ushort payloadSum = IpHeader.SumShortValues(payload, 0,
                                                         payload.Length);
             ushort hdrSum = IpHeader.SumShortValues(headerSum, udpsum);
             ushort chksum;
             chksum = (ushort) ~(
                 IpHeader.SumShortValues(hdrSum, payloadSum)
                 );

             buffer[udpOffset + 6] = (byte) (chksum >> 8);
             buffer[udpOffset + 7] = (byte) (chksum & 0xff);
         }
    }

    //oddities -- we currently disallow binding to port 0...you can't receive all packets on all ports...
    public class UDP
    {
        public static  bool    UDPInitialized = false;
        private static ushort  MaxPortNumber = 65535;
        private static UDP[]   udpSessions;  //used to demultiplex incoming packets
        private static MonitorLock udpSessionsMtx;
        private static ushort  nextPortNumber;   //assigning ports on demand

        //protects the incoming packet queue of each udp instance
        private MonitorLock  thisLock;
        private TContainerVectorQueueByte  packetContainer; //one queue for every active port
        private int    byteCount;

        private IPv4    localIPAddress;
        private ushort  localPort;
        private IPv4    remoteIPAddress;
        private ushort  remotePort;

        public  uint   dropped;
        public  AutoResetEvent udpWaitEvent;


        [Conditional("DEBUG_UDP")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("UDP: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        [Conditional("DEBUG_UDP")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print("UDP: {0}",
                            DebugStub.ArgList(format));
        }

        private static UDP GetUDPSession(ushort port)
        {
            if (UDPInitialized == false) {
                return null;
            }
            using (udpSessionsMtx.Lock()) {
                return udpSessions[port];
            }
        }


        //fails if new port is in use
        private bool UpdatePort(ushort newPort)
        {
            bool success = false;

            using (udpSessionsMtx.Lock()) {
                DebugPrint("Updating udp port old port {0} new port {1} \n", this.localPort, newPort);
                if (udpSessions[newPort] != null) {
                    DebugPrint("port taken!!!\n");
                    return false;
                }
                if (this.localPort != 0) {
                    VTable.Assert(udpSessions[this.localPort]  == this);
                    udpSessions[this.localPort] = null;
                }
                if (newPort != 0) {
                    udpSessions[newPort] = this;
                }
                this.localPort = newPort;
                success = true;
            }
            return success;
        }

        private bool AssignNextAvailablePort()
        {
            bool success = false; //fails only if we run out of ports
            ushort startPortNumber = nextPortNumber;
            using (udpSessionsMtx.Lock()) {
                do {
                    if (udpSessions[nextPortNumber] == null) {
                        DebugPrint("Assigning new dynamic port number {0}\n", nextPortNumber);
                        udpSessions[nextPortNumber] = this;
                        this.localPort = nextPortNumber;
                        success = true;
                    }
                    //Sing# complains if we just allow it to roll over?
                    if (nextPortNumber + 1 > MaxPortNumber) {
                        nextPortNumber = 1;
                    }
                    else {
                        nextPortNumber++;
                    }
                } while ((success == false) && (nextPortNumber != startPortNumber));
            }
            return success;
        }

        //a struct representing UDP connection (port numbers, ip address, and a wait event)
        //currently the system is structured to have one Exp thread per socket.
        //this allows us to safely sleep on a ReadFrom and Read.

        //need a way to create lasting connection between the Exp..static
        public static void Initialize()
        {
            //RAM is cheap.
            udpSessions = new UDP[MaxPortNumber];
            int i;
            for(i = 0; i < MaxPortNumber; i++) {
                udpSessions[i] = null;
            }
            nextPortNumber = 1024;
            UDPInitialized = true;
            udpSessionsMtx = new MonitorLock();
        }

        public UDP()
        {
            thisLock = new MonitorLock();
            this.packetContainer =
                new TContainerVectorQueueByte(
                    new VectorQueueByte()
                    );

            localIPAddress = IPv4.Any;
            localPort = 0;
            remoteIPAddress = IPv4.Any;
            remotePort = 0;
            byteCount = 0;
            udpWaitEvent = new AutoResetEvent(false);
        }

        //process incoming packet
        public static bool ProcessIncomingPacket(Bytes packet, IpHeader ipHeader)
        {
            int offset = EthernetHeader.Size + IpHeader.Size; //14 byte ethernet header + 20 byte IP header
            VTable.Assert(offset == 34);

            UDPHeader udpHeader   =   new UDPHeader(packet, offset);
            DebugPrint("ProcessIncomingPacket: Received packet from address {0} port {1}\n",
                       ipHeader.srcAddress.ToString(), udpHeader.srcPort);
            UDP udp = GetUDPSession(udpHeader.dstPort);

            //now we check to see whether the udp session wants to packet
            //XXX review this logic...
            //todo: check if udp is bound to local IP that dest IP matches.
            //UDP header?
            if ((udp != null) &&
                ((udp.LocalAddress == IPv4.Any) ||
                 (udp.RemoteAddress == ipHeader.srcAddress && udp.RemotePort == udpHeader.srcPort) ||
                 (udp.RemotePort == 0))) {

                offset += UDPHeader.Size;
                Bytes data = Bitter.SplitOff(ref packet, offset);
                //delete packet;
                udp.PushPacket(data);
                udp.udpWaitEvent.Set();
                return true;
            }

            DebugPrint("Received packe destined for inactive UDP port {0}" +
                       " source address {1} source port {2}\n",
                       udpHeader.dstPort, ipHeader.srcAddress.ToString(), udpHeader.srcPort);
            //delete  packet;
            return false;
        }

        // get some info
        public IPv4   RemoteAddress { get { return remoteIPAddress; } }
        public ushort RemotePort    { get { return remotePort; } }

        public IPv4   LocalAddress  { get { return localIPAddress; } }
        public ushort LocalPort     { get { return localPort; } }

        public void PushPacket(Bytes packet)
        {
            DebugPrint("Pushing packet\n");
            using (thisLock.Lock()) {
                byteCount += packet.Length;
                VectorQueueByte incomingPacketQueue = packetContainer.Acquire();
                incomingPacketQueue.AddTail(packet);
                packetContainer.Release(incomingPacketQueue);
            }
        }

        public Bytes PopSinglePacket()
        {
            Bytes packet = null;

            using (thisLock.Lock()) {
                VectorQueueByte incomingPacketQueue = packetContainer.Acquire();
                packet = incomingPacketQueue.ExtractHead();
                if (packet != null) {
                    byteCount -= packet.Length;
                }
                packetContainer.Release(incomingPacketQueue);
            }
            return packet;
        }

        public Bytes PopAllPackets()
        {
            Bytes packet;
            int sizeOfData;
            Bytes buffer;
            if (byteCount <=0) {
                DebugStub.WriteLine("UDP PopAllPackets: no data???\n");
                DebugStub.Break();
                return null;
            }
            using (thisLock.Lock()) {
                DebugPrint("Popping {0} bytes of data to client\n", byteCount);
                buffer = new Bytes(new byte[byteCount]);

                VectorQueueByte incomingPacketQueue = packetContainer.Acquire();
                int offset = 0;
                while((packet = incomingPacketQueue.ExtractHead()) != null) {
                    VTable.Assert(packet != null);
                    Bitter.Copy(buffer, offset, packet.Length, packet, 0);
                    offset += packet.Length;
                    byteCount -= packet.Length;
                    //delete packet;
                }
                packetContainer.Release(incomingPacketQueue);
                DebugStub.Assert(byteCount == 0);
            }
            return buffer;
        }

        public void Close()
        {
            //free any remaining messages in the queue
            DebugPrint("Closing udp instance freeing port {0}\n", this.localPort);
            bool rc = this.UpdatePort(0);
            VTable.Assert(rc == true);
            //cleanup any remaining data
            Bytes packet;
            VectorQueueByte incomingPacketQueue = packetContainer.Acquire();
            while((packet = incomingPacketQueue.ExtractHead()) != null) {
                //delete packet;
            }
            packetContainer.Release(incomingPacketQueue);
        }


        public bool IsLocalAddress(IPv4 ipAddress)
        {
            return IP.IsLocalAddress(ipAddress);
        }

        public bool Bind(IPv4 sourceAddr, ushort sourcePort)
        {
             if (sourceAddr != IPv4.Any && !IsLocalAddress(sourceAddr)) {
                // Invalid address
                //set error
                return false;
            }
            localIPAddress = sourceAddr;
            DebugPrint("UDP port bound to {0}\n", localIPAddress);
            //check to see if this port/ip is in use.
            if ((this.localPort != sourcePort) && (sourcePort != 0)) {
                return this.UpdatePort(sourcePort);
            }
            return true;
        }

        public bool Connect(IPv4 remoteAddr, ushort remotePort)
        {
            this.remoteIPAddress = remoteAddr;
            this.remotePort = remotePort;

            return true;
        }

        //This function does not return data
        //it only sets a status bit if data is available.
        public bool PollSelectRead(int millis)
        {
            return udpWaitEvent.WaitOne(TimeSpan.FromMilliseconds(millis));
        }

        //Eventually we'll need to worry about overflow.
        public bool PollSelectWrite(int millis)
        {
            return true;
        }

        //Give as much data as we've got
        public Bytes ReadData()
        {
            return PopAllPackets();
        }

        //This function selects and then returns data when it is available.
        public Bytes PollReadData(TimeSpan timeout)
        {
            bool rc = true;
            if (byteCount == 0) {
                rc = udpWaitEvent.WaitOne(timeout);
            }
            if (rc == true) {
                return PopSinglePacket();
            }
            return null;
        }

        public bool WriteData(Bytes buffer)
        {
            //Create a header in the ExHeap.  Send the buffer and the header
            if (remoteIPAddress == IPv4.Any ||
                remotePort == 0) {
                DebugPrint("Attempting to send UDP packet without port or address\n");
                //delete buffer;
                return false;
            }

            WriteTo(this.remoteIPAddress, this.remotePort, buffer);
            return true;
        }


        //There are several different flavors of implementation for WriteTo
        //BSD Unix assigns an ephemeral port for every packet, while Linux
        //picks an ephemeral port and assigns it permanantly.  I'm unsure of the
        //behavior of windows.
        public bool WriteTo(IPv4 remoteAddr,
                            ushort remotePort,
                            Bytes buffer)
        {
            //allocate a local port
            if (localPort == 0) {
                bool rc;
                DebugPrint("Assigning local port to process for WriteTo\n");
                rc = AssignNextAvailablePort();
                VTable.Assert(rc);
            }

            if (localIPAddress == IPv4.Any) {
                HostConfiguration hostConfiguration = IP.GetHostConfiguration();
                RouteEntry e = hostConfiguration.RoutingTable.Lookup(remoteAddr);

                if (e != null) {
                    localIPAddress = e.InterfaceAddress;
                    DebugPrint("local address now {0}\n", localIPAddress);
                }
                else {
                    DebugPrint("No route for {0}\n", remoteAddr);
                }
            }

            int headerSize = EthernetHeader.Size + IpHeader.Size + UDPHeader.Size;
            Bytes header = new Bytes(new byte[headerSize]);
            WriteCompleteUDPHeader(header, buffer, buffer.Length);
            DebugPrint("Sending UDP packet\n");
            IP.SendOutgoingPacket(header, buffer, remoteAddr);
            return true;
        }

        //assume ethernet
        //we have to expose this for the DhcpClient
        //Once we move the Dhcp client into an app this can be hidden again
        public void WriteCompleteUDPHeader(Bytes header, Bytes data, int payloadLength)
        {

            int totalLength = IpHeader.Size + UDPHeader.Size + payloadLength;
            //write ip header
            int offset = EthernetHeader.Size;

            int o = EthernetHeader.Size;
            DebugStub.Assert(payloadLength < 0xffff);

            header[o++] = 0x45;  //default version 4, header_len 5
            header[o++] = 0;     //tos
            header[o++] = (byte) (((ushort)totalLength) >> 8);  //total length of the ip header
            header[o++] = (byte) (((ushort)totalLength) & 0xff);
            header[o++] = (byte) (((ushort)0) >> 8);            //fragment id
            header[o++] = (byte) (((ushort)0) & 0xff);          //fragment id
            header[o++] = (byte) (((ushort)0) >> 8);   //fragment offset
            header[o++] = (byte) (((ushort)0) & 0xff); //fragment offset
            header[o++] = 128;             //default ttl
            header[o++] = 17;              // protocol ID --> udp
            header[o++] = 0;               //ipchecksum (fill it in later)
            header[o++] = 0;               //ipchecksum

            // set the ip addresses
            localIPAddress.CopyOut(header.Array, header.Start + o);
            o += IPv4.Length;

            remoteIPAddress.CopyOut(header.Array, header.Start + o);
            o += IPv4.Length;

            // calculate checksum
            ushort chk = IpHeader.CalculateChecksum(header, offset, IpHeader.Size);

            header[offset + 10] = (byte) (((ushort)chk) >> 8);
            header[offset + 11] = (byte) (((ushort)chk) & 0xff);

            //write the udp header
            header[o++] = (byte)(((ushort)localPort) >> 8);
            header[o++] = (byte)(((ushort)localPort) & 0xff);

            header[o++] = (byte)(((ushort)remotePort) >> 8);
            header[o++] = (byte)(((ushort)remotePort) & 0xff);

            ushort udpLength = (ushort) (UDPHeader.Size + payloadLength);
            header[o++] = (byte)(((ushort)udpLength) >> 8);
            header[o++] = (byte)(((ushort)udpLength) & 0xff);

            // udp checksum (forget for now)
            header[o++] = 0;
            header[o++] = 0;

            UDPHeader.SetUdpChecksum(header, data, EthernetHeader.Size, udpLength);
        }


    }


}
