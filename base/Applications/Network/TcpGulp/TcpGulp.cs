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

using Microsoft.Singularity;
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
    [ConsoleCategory(HelpMessage="Gulp TCP data from an ipAddress, port", DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<TcpContract.Imp:Start> tcpRef;

        [StringParameter( "ipAddress", Mandatory=true, Position=0, HelpMessage="IP Address to send to")]
        internal string ipAddress;


        [StringParameter( "port", Mandatory=true, Position=1, HelpMessage="port to blats")]
        internal string port;

        reflective internal Parameters();

        internal int AppMain() {
            return TcpGulp.AppMain(this);
        }
    }

    public class TcpGulp
    {
        public static int Gulp(TcpConnectionContract.Imp:ReadyState! tcpConn, IPv4 address, ushort port)
        {
            Console.WriteLine("TcpGulp({0}, {1})", address, port);

            try {
                // Try to connect to the remote host
                tcpConn.SendConnect((uint)address, port);

                switch receive {
                    case tcpConn.CouldNotConnect(TcpError error):
                    {
                        Console.WriteLine("Failed to connect: TcpError = " + System.Net.Sockets.TcpException.GetMessageForTcpError(error));
                        return -1;
                    }
                    break;

                    case tcpConn.OK() :
                        // success;
                        break;

                    case tcpConn.ChannelClosed() :
                        // how rude
                        Console.WriteLine("Netstack channel closed unexpectedly");
                        return -1;
                        break;
                }

                Console.WriteLine("Connected");
                bool connected = true;
                int messages = 0; 
                int bytesRead = 0; 
                
                while (connected) {
                    tcpConn.SendRead();

                    switch receive {
                        case tcpConn.Data(byte[]! in ExHeap data) :
                            Console.Write('.'); 
                            messages++; 
                            bytesRead += data.Length; 
#if false                            
                            Console.WriteLine("Read {0} bytes :", data.Length);

                            for (int i = 0; i < data.Length; ++i) {
                                if (data[i] < 32) {
                                    Console.Write("<" + (int)data[i] + ">");
                                }
                                else {
                                    Console.Write((char)data[i]);
                                }
                            }
#endif 
                            delete data;
                            break;

                        case tcpConn.ConnectionClosed() :
                            tcpConn.SendClose(); // Zombie -> Closed
                            connected = false;
                            break;

                        case tcpConn.NoMoreData() :
                            // We're never going to send anything
                            tcpConn.SendClose(); // SendOnly -> Closed
                            connected = false;
                            break;

                        case tcpConn.ChannelClosed() :
                            // How rude
                            connected = false;
                            break;
                    }
                }

                Console.WriteLine("\nConnection closed");
                Console.WriteLine("got {0} messages {1} bytes ",
                    messages, bytesRead); 
            }
            catch (Exception e) {
                Console.WriteLine("Unexpected exception: {0}", e);
            }
            finally {
            }

            return 0;
        }

        public static void Usage()
        {
            Console.WriteLine("tcpgulp <ipAddress> <port>");
        }

        internal static int AppMain(Parameters! config)
        {
            IPv4 host;



            try {
                host = IPv4.Parse(config.ipAddress);
            }
            catch (FormatException e) {
                Console.WriteLine("{0}: {1}", e, config.ipAddress);
                return -1;
            }

            ushort port;
            try {
                port = UInt16.Parse(config.port);
            }
            catch (FormatException) {
                Console.WriteLine("Malformed port number: {0}", config.port);
                return -1;
            }
            catch (OverflowException) {
                Console.WriteLine("Port number out of range: {0}", config.port);
                return -1;
            }

            TcpContract.Imp tcpConn = ((!)config.tcpRef).Acquire(); 
            if (tcpConn == null) {
                Console.WriteLine("Could not initialize TCP endpoint.");
                return 1;
            }
            tcpConn.RecvReady(); 
            
            TcpConnectionContract.Imp! connImp;
            TcpConnectionContract.Exp! connExp;
            TcpConnectionContract.NewChannel(out connImp, out connExp);

            tcpConn.SendCreateTcpSession(connExp);
            connImp.RecvReady();
            delete tcpConn;

            int result =  Gulp(connImp, host, port);
            delete connImp;
            return result; 
        }
    } // end class TcpGulp
}
