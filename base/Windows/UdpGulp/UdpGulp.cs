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

        public static void Usage()
        {
            Console.WriteLine("UdpGulp [-a <address>] [-t <seconds>] port");
            Environment.Exit(-2);
        }

        public static void Gulp(Socket s, uint seconds)
        {
            long totalBytesReceived  = 0;
            long recentBytesReceived = 0;

            byte [] buffer = new byte [4096];

            DateTime now      = DateTime.Now;
            DateTime epochEnd = now + TimeSpan.FromSeconds(1);

            int sleepMillis = 0;

            while (seconds-- != 0) {
                int pps = 0;
                while (now < epochEnd) {
                    if (s.Available > 0) {
                        int bytesReceived = s.Receive(buffer);
                        bytesReceived += FixedHeaderBytes;
                        totalBytesReceived += bytesReceived;
                        recentBytesReceived += bytesReceived;
                        pps++;
                    }
                    else {
                        Thread.Sleep(sleepMillis);
                    }
                    now = DateTime.Now;
                }
                Console.WriteLine("Data rate = {0:e3} bps ({1} pps), {2} bytes/sec",
                                  recentBytesReceived * 8.0,
                                  pps,
                                  recentBytesReceived
                                  );
                epochEnd = now + TimeSpan.FromSeconds(1);
                sleepMillis = (pps > 0) ? 0 : 100;
                recentBytesReceived = 0;
            }
        }

        private static IPAddress ParseAddress(string srep)
        {
            try {
                return IPAddress.Parse(srep);
            }
            catch {
                try {
                    IPHostEntry iphe = Dns.Resolve(srep);
                    return iphe.AddressList[0];
                }
                catch {
                    return IPAddress.Any;
                }
            }
        }

        private static bool ParseUInt32(string srep, out uint value)
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

        public static int Main(string [] args)
        {
            int i = 0;

            IPAddress address = IPAddress.Any;
            uint      seconds = 30;

            while (i < args.Length &&
                   (args[i][0] == '-' || args[i][0] == '/')) {
                switch (Char.ToLower(args[i][1])) {
                    case 'a':
                        if (args.Length - i < 2)
                            Usage();
                        address = ParseAddress(args[++i]);
                        break;
                    case 't':
                        if (args.Length - i < 2)
                            Usage();
                        if (!ParseUInt32(args[++i], out seconds)) {
                            Console.WriteLine("Invalid duration: {0}",
                                              args[i]);
                            return -1;
                        }
                        break;
                    default:
                        Usage();
                        break;
                }
                i++;
            } // end while

            if (args.Length - i != 1) {
                Usage();
            }

            uint port;
            if (!ParseUInt32(args[i], out port) || port > 0xffff) {
                Console.WriteLine("Bad port: {0}", args[i]);
                return -1;
            }
            Socket s = new Socket(AddressFamily.InterNetwork,
                                  SocketType.Dgram,
                                  ProtocolType.Udp);
            s.Bind(new IPEndPoint(address, (ushort)port));
            Gulp(s, seconds);
            return 0;
        }
    }
}
