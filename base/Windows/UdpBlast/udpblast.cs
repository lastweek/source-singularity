///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   UdpBlast.cs
//
//  Note:
//

using System;
using System.Net;
using System.Net.Sockets;
using System.Threading;

namespace Microsoft.Singularity.Test.Network
{
    public class UdpBlast
    {
        private const int FixedHeaderBytes = 42;    // Ether + IP + UDP

        static bool verbose = true;

        public static void Usage()
        {
            Console.WriteLine("UdpBlast [-p <bytesPerPkt>] [-r <bitsPerSec>] [-t duration] [-v] host port");
            Environment.Exit(-2);
        }

        public static void VerboseLog(string format, params object [] args)
        {
            if (verbose) {
                Console.Write(format, args);
            }
        }

        private static int
        GetPacketSize(long bitsPerSecond,
                      long bitsThisSecond,
                      int  bytesPerPacket)
        {
            long bitsRemaining = bitsPerSecond - bitsThisSecond;
            if (bitsRemaining >= (long)8 * bytesPerPacket) {
                return bytesPerPacket - FixedHeaderBytes;
            }
            else {
                int size = ((int)(bitsPerSecond - bitsThisSecond) / 8
                            - FixedHeaderBytes);
                if (size < 1) {
                    return 1;
                }
                return size;
            }
        }

        public static void
        Blast(Socket s,
              uint   bitsPerSecond,
              int    bytesPerPacket,
              uint   durationSeconds
              )
        {
            byte [] bigPacket   =
                new byte[GetPacketSize(bitsPerSecond, 0, bytesPerPacket)];
            byte [] smallPacket = null;

            DateTime startTime  = DateTime.Now;
            DateTime endTime    = (startTime +
                                   TimeSpan.FromSeconds(durationSeconds));

            DateTime secondStart = startTime;
            DateTime secondEnd   = startTime + TimeSpan.FromSeconds(1);

            DateTime now = startTime;

            uint second         = 0;
            long bitsThisSecond = 0;
            long pktsThisSecond = 0;
            long totalBits      = 0;
            long totalPackets   = 0;

            VerboseLog("UdpBlast: {0} bytesPerPacket, Limiting transfer to {1} bitsPerSecond, for {2} seconds",
                              bytesPerPacket, bitsPerSecond, durationSeconds);

            while (now < endTime) {
                byte [] packet = bigPacket;
                while (now < secondEnd && bitsThisSecond < bitsPerSecond) {
                    int size = GetPacketSize(bitsPerSecond,
                                             bitsThisSecond,
                                             bytesPerPacket);
                    if (size != packet.Length) {
                        if (smallPacket == null || size != smallPacket.Length)
                            smallPacket = new byte [size];
                        packet = smallPacket;
                        Console.Write(".");
                    }
                    s.Send(packet);
                    bitsThisSecond += (packet.Length + FixedHeaderBytes) * 8;
                    pktsThisSecond++;
                    totalPackets++;
                    now = DateTime.Now;
                }

                while (now < secondEnd) {
                    Thread.Sleep(0);
                    now = DateTime.Now;
                }

                TimeSpan tau = secondEnd - secondStart;

                long bytesPerSecond = (long)((bitsThisSecond / tau.TotalSeconds) / 8);

                VerboseLog(
                    "Round {0} duration(secs) {1:f2} packets {2} rate (bps) {3:e3}, bytes/sec {4:e3}\n",
                    second, tau.TotalSeconds,
                    pktsThisSecond,
                    bitsThisSecond / tau.TotalSeconds,
                    bytesPerSecond
                    );

                second++;
                totalBits      += bitsThisSecond;
                bitsThisSecond  = 0;
                pktsThisSecond   = 0;
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

        public static IPAddress ParseAddress(string srep)
        {
            try {
                return IPAddress.Parse(srep);
            }
            catch {
                try {
                    VerboseLog("Resolving: {0}\n", srep);
                    IPHostEntry iphe = Dns.GetHostEntry(srep);
                    return iphe.AddressList[0];
                }
                catch {
                    VerboseLog("Falling back to any address");
                    return IPAddress.Any;
                }
            }
        }

        private static bool ParseUInt32(string srep, out UInt32 value)
        {
            try {
                value = UInt32.Parse(srep);
                return true;
            }
            catch (FormatException) {
            }
            catch (OverflowException) {
            }
            value = 0;
            return false;
        }

        private static bool ParseDouble(string srep, out Double value)
        {
            try {
                value = Double.Parse(srep);
                return true;
            }
            catch (FormatException) {
            }
            catch (OverflowException) {
            }
            value = 0;
            return false;
        }

        public static int Main(string [] args)
        {
            int i = 0;

            uint bitsPerSecond  = 64000;
            uint bytesPerPacket = 1500;
            uint duration       = 30;

            double rate;

            while (i < args.Length &&
                   (args[i][0] == '-' || args[i][0] == '/')) {
                switch (Char.ToLower(args[i][1])) {
                    case 'p':
                        if (args.Length - i < 2)
                            Usage();
                        if (!ParseUInt32(args[++i], out bytesPerPacket) ||
                            bytesPerPacket <= FixedHeaderBytes) {
                            Console.WriteLine("Bad packet size: {0}", args[i]);
                            Environment.Exit(-1);
                            return -1;
                        }
                        break;
                    case 'r':
                        if (args.Length - i < 2)
                            Usage();
                        if (!ParseDouble(args[++i], out rate) ||
                            rate < 0 || rate > UInt32.MaxValue * 1.0) {
                            Console.WriteLine("Bad rate: {0}", args[i]);
                            return -1;
                        }
                        bitsPerSecond = (UInt32)rate;
                        break;
                    case 't':
                        if (args.Length - i < 2)
                            Usage();
                        if (!ParseUInt32(args[++i], out duration)) {
                            Console.WriteLine("Bad duration: {0}", args[i]);
                            return -1;
                        }
                        break;
                    case 'v':
                        verbose = true;
                        break;
                }
                i++;
            }

            if (args.Length - i < 2) {
                Usage();
            }

            IPAddress address = ParseAddress(args[i]);
            if (address == IPAddress.Any) {
                Console.WriteLine("Invalid address: {0}", args[i]);
                return -1;
            }

            uint port;
            if (!ParseUInt32(args[++i], out port) || port > 0xffff) {
                Console.WriteLine("Bad port: {0}", args[i]);
                return -1;
            }

            VerboseLog("Sending to {0} {1}\n", address, port);
            VerboseLog("Packet size = {0} bytes\n", bytesPerPacket);
            VerboseLog("Send rate = {0} bps ({1} pps).\n",
                       bitsPerSecond, bitsPerSecond / (8 * bytesPerPacket));

            Socket s = new Socket(AddressFamily.InterNetwork,
                                  SocketType.Dgram,
                                  ProtocolType.Udp);
            s.Connect(new IPEndPoint(address, (ushort)port));
            Blast(s, bitsPerSecond, (int)bytesPerPacket, duration);

            return 0;
        }
    }
}
