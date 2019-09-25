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
    [ConsoleCategory(HelpMessage="Receive UDP data from a ipAddress, port",
                     DefaultAction = true)]
    internal class Parameters
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<UdpContract.Imp:Start> udpRef;

        [LongParameter("t", Mandatory = false, HelpMessage = "Seconds to send packets for", Default = 30)]
        internal long seconds;

        [StringParameter("a", Mandatory = false, HelpMessage = "Local address to bind to.", Default = "0.0.0.0")]
        internal string address;

        [LongParameter("port", Mandatory = true, Position = 0, HelpMessage = "port to gulp from")]
        internal long port;

        reflective internal Parameters();

        internal int AppMain()
        {
            return UdpGulp.AppMain(this);
        }
    }

    public class UdpGulp
    {
        private const int FixedHeaderBytes = 42;    // Ether + IP + UDP

        private static void
        ReceivePackets(
            UdpConnectionContract.Imp:ReadyState! udpConn,
            long totalSeconds
            )
        {
            int bytesThisRound   = 0;
            int packetsThisRound = 0;

            DateTime now        = DateTime.Now;
            DateTime epochEnd   = now + TimeSpan.FromSeconds(1);
            DateTime epochStart = now;

            while (--totalSeconds >= 0) {
                while (now < epochEnd) {
                    udpConn.SendPollRead((epochEnd - now).Milliseconds);
                    switch receive {
                        case udpConn.NoData() :
                            // No data to read. This doesn't
                            // necessarily mean the connection
                            // is closed.
                            Thread.Yield();
                            break;
                            case udpConn.Data(uint addr, ushort port2, byte[]! in ExHeap data):
                                bytesThisRound += data.Length + FixedHeaderBytes;
                                packetsThisRound++;
                                delete data;
                                break;
                        case udpConn.ChannelClosed():
                            throw new Exception("udpConn channel closed");
                    }
                    now = DateTime.Now;
                }

                TimeSpan delta = now - epochStart;
                string msg = String.Format(
                    "Duration(s) {0:f2} rate {1:e3} bps, {2:e3} bytes/sec, {3:e3} pps",
                    delta.TotalSeconds,
                    8.0 * bytesThisRound / delta.TotalSeconds,
                    8.0 * bytesThisRound / delta.TotalSeconds,
                    1.0 * packetsThisRound / delta.TotalSeconds
                    );

                Console.WriteLine(msg);
                DebugStub.WriteLine(msg);

                bytesThisRound = 0;
                packetsThisRound = 0;
                epochStart     = DateTime.Now;
                epochEnd       = epochStart + TimeSpan.FromSeconds(1);
            }
        }

        public static int
        Gulp([Claims] UdpConnectionContract.Imp:ReadyState! udpConn,
             IPv4   address,
             ushort port,
             long   totalSeconds)
        {
            Console.WriteLine("UdpGulp({0}, {1})", address, port);

            try {
                // Bind local endpoint
                udpConn.SendBindLocalEndPoint((uint)address, port);

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

                ReceivePackets(udpConn, totalSeconds);

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

            if (config.port > 0xffff || config.port < 0) {
                Console.WriteLine("Port number out of range: {0}",
                                  config.port);
                return -1;
            }
            ushort port = (ushort) config.port;

            UdpContract.Imp udpConn = ((!)config.udpRef).Acquire();
            if (udpConn == null) {
                Console.WriteLine("Could not initialize TCP endpoint.");
                return 1;
            }

            Console.WriteLine("Waiting for ready");
            udpConn.RecvReady();

            UdpConnectionContract.Imp! connImp;
            UdpConnectionContract.Exp! connExp;
            UdpConnectionContract.NewChannel(out connImp, out connExp);

            Console.WriteLine("Creating session");
            udpConn.SendCreateUdpSession(connExp);
            connImp.RecvReady();
            delete udpConn;
            Console.WriteLine("Ready");
            return Gulp(connImp, host, port, config.seconds);
        }
    } // end class UdpGulp
}
