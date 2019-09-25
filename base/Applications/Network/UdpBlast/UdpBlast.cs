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
using System.Threading;

using Microsoft.Singularity;
using Microsoft.SingSharp;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
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
    [ConsoleCategory(HelpMessage="Send UDP data to and ipAddress and port",
                     DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<UdpContract.Imp:Start> udpRef;

        [LongParameter("p", Mandatory=false, HelpMessage="Packet size (bytes)", Default = 1500)]
        internal long packetBytes;

        [LongParameter("r", Mandatory=false, HelpMessage="Transmission rate in bits per second", Default = 64000)]
        internal long bitsPerSecond;

        [LongParameter("t", Mandatory=false, HelpMessage="Seconds to send packets for", Default = 30)]
        internal long seconds;

        [BoolParameter("v", Mandatory=false, HelpMessage="Verbose output", Default = true)]
        internal bool verbose;

        [StringParameter("Address", Mandatory=true, Position=0, HelpMessage="Destination IP Address")]
        internal string address;

        [LongParameter("port", Mandatory=true, Position=1, HelpMessage="Destination UDP port")]
        internal long port;

        reflective internal Parameters();

        internal int AppMain() {
            return UdpBlast.AppMain(this);
        }
    }

    public class UdpBlast
    {
        private const uint FixedHeaderBytes = 42; // Ether + IP + UDP

        private static bool verbose;

        public static void VerboseWriteLine(string format,
                                            params Object [] args)
        {
            string msg = String.Format(format, args);
            DebugStub.WriteLine(msg);
            if (verbose) {
                Console.WriteLine(format, args);
            }
        }

        private static void
        SendPackets(
            UdpConnectionContract.Imp:ReadyState! udpConn,
            long   bitsPerSecond,
            uint   bytesPerPacket,
            long   durationSeconds
            )
        {
            DateTime startTime  = DateTime.Now;
            DateTime endTime    = (startTime +
                                   TimeSpan.FromSeconds(durationSeconds));

            DateTime secondStart = startTime;
            DateTime secondEnd   = startTime + TimeSpan.FromSeconds(1);

            DateTime now = startTime;

            uint second         = 0;
            long bitsThisSecond = 0;
            long totalBits      = 0;
            int  totalPackets   = 0;

            VerboseWriteLine("UdpBlast: {0} bytesPerPacket, Limiting transfer to {1} bitsPerSecond, for {2} seconds",
                              bytesPerPacket, bitsPerSecond, durationSeconds);

            while (now < endTime) {
                int pps = 0;

                while (now < secondEnd && bitsThisSecond < bitsPerSecond) {
                    // XXX: Just bursting packets out for
                    // now rather than pacing them,
                    // interested mainly in saturation case.
                    byte[] in ExHeap pkt;
                    uint pktSize;
                    if ((long)bytesPerPacket * 8 < bitsPerSecond - bitsThisSecond) {
                        pktSize = bytesPerPacket;
                    }
                    else {
                        // Send a final runt packet for this cycle to keep us under
                        // the agreed total bits per second rate.
                        pktSize = (uint)((bitsPerSecond - bitsThisSecond) / 8);
                        if (pktSize <= FixedHeaderBytes) {
                            pktSize = FixedHeaderBytes + 1;
                        }
                    }
                    pkt = new [ExHeap] byte [pktSize - FixedHeaderBytes];
                    udpConn.SendWrite(pkt);
                    udpConn.RecvOK();
                    bitsThisSecond += pktSize * 8;
                    now = DateTime.Now;
                    pps++;
                    totalPackets++;
                }

                while (now < secondEnd) {
                    Thread.Sleep(0);
                    now = DateTime.Now;
                }

                TimeSpan tau = secondEnd - secondStart;

                long bytesPerSecond = (bitsThisSecond / tau.TotalSeconds) / 8;

                VerboseWriteLine(
                    "Round {0} duration(secs) {1:f2} rate (pps) {2} rate (bps) {3:e3}, bytes/sec {4:e3}",
                    second, tau.TotalSeconds,
                    pps,
                    bitsThisSecond / tau.TotalSeconds,
                    bytesPerSecond);

                second++;
                totalBits      += bitsThisSecond;
                bitsThisSecond  = 0;
                secondStart     = now;
                secondEnd       = now + TimeSpan.FromSeconds(1);
            }

            Console.WriteLine(
                "Average rate: packets/sec {0}, bits/sec {1:e3}, bytes/sec {2:e3}",
                totalPackets / (now - startTime).TotalSeconds,
                totalBits / (now - startTime).TotalSeconds,
                (totalBits / (now - startTime).TotalSeconds) / 8
                );
        }

        public static int
        Blast(
            [Claims] UdpConnectionContract.Imp:ReadyState! udpConn,
            IPv4   address,
            ushort port,
            long   bitsPerSecond,
            long   bytesPerPacket,
            long   durationSeconds
            )
        {
            Console.WriteLine("UdpBlast({0}, {1})", address, port);

            try {
                udpConn.SendConnectWithAnyLocalEndPoint((uint)address, port);

                switch receive {
                    case udpConn.OK() :
                        // success;
                        Console.WriteLine("Connected");
                        break;

                    case udpConn.InvalidEndPoint(ip, rejectedPort) :
                        throw new Exception("udpConn address and port rejected");

                    case udpConn.ChannelClosed() :
                        throw new Exception("udpConn channel closed");
                }

                SendPackets(udpConn,
                            bitsPerSecond,
                            (uint)bytesPerPacket,
                            durationSeconds);
                Console.WriteLine("Closing connection");

                udpConn.SendClose();
            }
            catch (Exception e) {
                Console.WriteLine("Unexpected exception: {0}", e);
            }
            finally {
                delete udpConn;
            }

            return 0;
        }

        internal static int AppMain(Parameters! config)
        {
            IPv4 host;
            try {
                host = IPv4.Parse(config.address);
            }
            catch (FormatException e) {
                Console.WriteLine("{0}: {1}", e, config.address);
                return -1;
            }

            if (config.port > 65536 || config.port < 0) {
                Console.WriteLine("Port number out of range: {0}", config.port);
                return -1;
            }
            ushort port = (ushort) config.port;

            if ((uint)config.packetBytes < FixedHeaderBytes) {
                Console.WriteLine("Packet size needs to be larger than fixed header size ({0} bytes)", FixedHeaderBytes);
                return -1;
            }

            UdpBlast.verbose = config.verbose;

            UdpContract.Imp udpConn = ((!)config.udpRef).Acquire();
            if (udpConn == null) {
                Console.WriteLine("Could not initialize TCP endpoint.");
                return 1;
            }
            udpConn.RecvReady();

            UdpConnectionContract.Imp! connImp;
            UdpConnectionContract.Exp! connExp;
            UdpConnectionContract.NewChannel(out connImp, out connExp);

            udpConn.SendCreateUdpSession(connExp);
            connImp.RecvReady();
            delete udpConn;

            return Blast(connImp,
                         host, port,
                         config.bitsPerSecond,
                         config.packetBytes,
                         config.seconds
                         );
        }
    } // end class UdpBlast
}
