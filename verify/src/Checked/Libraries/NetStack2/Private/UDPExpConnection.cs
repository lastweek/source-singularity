///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   UdpExpConnection.sg
//
//  Note:   Provider-side helper for the Udp Channel Contract
//

// #define DEBUG_UDPEXPCONNECTION

using System.Threading;
using System.Net.IP;
using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.NetStack;
using System.Collections;
using System;

namespace Microsoft.Singularity.NetStack2.Channels.Private
{
    public class UdpConnectionContract
    {
        private UDP udp;
        private State state = State.Start;

        public enum State
        {
            Start,
            ReadyState,
            ConnectResult,
            BindResult,
            ConnectFromLocallyBoundResult,
            Connected,
            LocallyBound,
            Closed,
        }

        public bool InState(State s)
        {
            return s == state;
        }

        [ System.Diagnostics.Conditional("DEBUG_UDPEXPCONNECTION") ]
        static void DebugPrint(string format, params object [] args)
        {
            DebugStub.Print(
                "UdpConnectionExpThread [{0}]: {1}",
                DebugStub.ArgList(
                    string.Format(format, args)
                    )
                );
        }

        public void BindLocalEndPoint(IPv4 srcIP, ushort srcPort)
        {
            DebugPrint("BindLocalEndPoint ({0:x8}/{1} ->)\n",
                       srcIP, srcPort);
            IPv4 srcAddr = srcIP;
            if (srcAddr != IPv4.Any &&
                udp.IsLocalAddress(srcAddr) == false) {
                throw new Exception("BindLocalEndPoint: InvalidEndPoint");
            }
            else {
                udp.Bind(srcAddr, srcPort);
                state = State.LocallyBound;
            }
        }

        public void ConnectWithAnyLocalEndPoint(IPv4   dstIP,
                                            ushort dstPort)
        {
            DebugPrint(
                "ConnectWithAnyLocalEndPoint (-> {0:x8}/{1})\n",
                dstIP, dstPort
                );

            udp.Connect(dstIP, dstPort);
            state = State.Connected;
        }

        public void Connect(IPv4 srcIP, ushort srcPort,
                        IPv4 dstIP, ushort dstPort)
        {
            DebugPrint(
                "BindLocalEndPoint ({0:x8}/{1} -> {2:x8}/{3})\n",
                srcIP, srcPort, dstIP, dstPort
                );
            udp.Bind(srcIP, srcPort);
            udp.Connect(dstIP, dstPort);
            state = State.Connected;
        }

        public bool PollSelectRead(int millis)
        {
            state = State.Connected;
            return udp.PollSelectRead(millis);
        }

        public bool PollSelectWrite(int millis)
        {
            state = State.Connected;
            return udp.PollSelectWrite(millis);
        }

        public Bytes Read()
        {
            return udp.ReadData();
        }

        public Bytes PollRead(int timeoutMillis)
        {
            return udp.PollReadData(TimeSpan.FromMilliseconds(timeoutMillis));
        }

        public void Write(Bytes data)
        {
            DebugPrint("Write {0} bytes.\n", data.Length);
            if (!udp.WriteData(data)) {
                throw new Exception("Write: DataTooLarge");
            }
        }

        public void WriteTo(uint dstIP, ushort dstPort, Bytes data)
        {
            DebugPrint("WriteTo {0} bytes -> {1:x8}/{2}.\n",
                       data.Length, dstIP, dstPort);
            bool written = udp.WriteTo(new IPv4(dstIP),
                                      dstPort, data);
            if (!written) {
                throw new Exception("WriteTo: DataTooLarge");
            }
            state = State.ReadyState;
        }

        public void Close()
        {
            udp.Close();
            state = State.Closed;
        }

        public IPv4 GetLocalAddress()
        {
            return udp.LocalAddress;
        }

        public ushort GetLocalPort()
        {
            return udp.LocalPort;
        }

        public IPv4 GetRemoteAddress()
        {
            return udp.RemoteAddress;
        }

        public ushort GetRemotePort()
        {
            return udp.RemotePort;
        }

        public UdpConnectionContract()
        {
            udp = new UDP();
            state = State.ReadyState;
        }

#if false
        private UdpConnectionContract(UdpSession newSession)
        {
            this.session = newSession;
            state = State.ReadyState;
        }
#endif
    }
}
