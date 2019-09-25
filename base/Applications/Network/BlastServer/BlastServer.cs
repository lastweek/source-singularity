////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program.
//

using System;
using System.Net;
using System.Net.Sockets;
using System.Threading;
using System.Collections;

#if SINGULARITY
using Microsoft.Contracts;
using System.IO;
using System.Runtime.InteropServices;

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using NetStack.Contracts;
using NetStack.Channels.Public;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]
#endif
 

namespace Microsoft.Singularity.Applications.Network
{
#if SINGULARITY
    [ConsoleCategory(HelpMessage="BlastServer TCP data to a ipAddress, port", DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<TcpContract.Imp:Start> tcpRef;


        [LongParameter( "port", Mandatory=true, Position=0, HelpMessage="port to gulp from ")]
        internal long port;


        [LongParameter( "numBytes", Mandatory=false, Position=1, HelpMessage="Total bytes to send", Default = 10000)]
        internal long numBytes;


        [LongParameter( "chunkSize", Mandatory=false, Position=2, HelpMessage="Chunks size to send", Default = 256)]
        internal long chunkSize;

        reflective internal Parameters();

        internal int AppMain() {
            return BlastServer.AppMain(this);
        }
    }
#endif 

    public class BlastServer
    {
        ///////////////////////////////////////////////////////////////////////
        // Constants
        private const int WorkerThreads = 32;
        private const int MaxWorkItems  = 32 * WorkerThreads;
        private const string RepeatPattern = "Here is a repeating string of text that serves as content. ";

        ///////////////////////////////////////////////////////////////////////
        // class variables 
        ushort      port;
        uint        numBytes;
        uint        chunkSize;
        byte[]      chunkBuffer; 
        ThreadPool  threadPool;
        
        private void DispatchRequest(object dispatchObject)
        {
            Console.WriteLine(dispatchObject as string);
            Console.WriteLine("We should Never get here");
#if SINGULARITY
            DebugStub.Break();
#endif            
        }

        private void test (object dispatchObject)
        {
            Console.Write(dispatchObject as string);
        }
        
        private void Blaster (object sock)
        {
            Socket socket = sock as Socket; 
#if SINGULARITY
            assert socket != null; 
#endif            
            int bytesSent = 0;
            int iterations =0;
            
            Console.WriteLine("Got connection...");

            uint bytesLeft = numBytes, patternLength = (uint)RepeatPattern.Length;
            try {
                while (bytesLeft > 0) {
                    uint thisPass = chunkSize < bytesLeft ? chunkSize : bytesLeft;
                    if (thisPass == chunkSize) {
                        socket.Send(chunkBuffer);
                    }
                    else {
                        byte[] thisPassBuffer = new byte[thisPass]; 
                        for (uint i = 0; i < thisPass; i++) {
                            thisPassBuffer [(int)i] = (byte)RepeatPattern[(int)i % (int)patternLength];
                        }   
                        socket.Send(thisPassBuffer);
                    }
                   bytesLeft -= thisPass;
                   bytesSent += (int) thisPass;
                   iterations++;
                   Console.Write(".");
                }
            }
            catch (ArgumentNullException ae) {
                Console.WriteLine("ArgumentNullException : {0}", ae.ToString());
            }
            catch (SocketException se) {
                Console.WriteLine("SocketException : {0}", se.ToString());
            }
            catch (Exception e) {
                Console.WriteLine("Unexpected exception : {0}", e.ToString());
            }

            Console.WriteLine("\nSent {0} bytes in {1} iterations",bytesSent,iterations); 

            socket.Shutdown(SocketShutdown.Both);
            socket.Close(); 
            Thread.Sleep(2);
        }
        
        private void Listen() {
            Socket socket = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);
            socket.Bind(new IPEndPoint(IPAddress.Any, (int)this.port));
            socket.Listen((int)SocketOptionName.MaxConnections);
            while (true) {
                Socket s = socket.Accept();
                threadPool.QueueUserWorkItem(new ThreadPool.WorkCallback(Blaster), s);
            }
        }

#if SINGULARITY
        [NotDelayed]
#endif
        public BlastServer (ushort port, uint numBytes, uint chunkSize)
        {
            this.port = port; 
            this.numBytes = numBytes; 
            this.chunkSize = chunkSize;
            
            chunkBuffer = new byte[chunkSize]; 
            for (uint i = 0; i < chunkSize; i++) {
                chunkBuffer [(int)i] = (byte)RepeatPattern[(int)i % (int)RepeatPattern.Length];
            }

            Console.WriteLine("BlastServer listening on  port {0} for {1} bytes in {2}-byte chunks",
                              port, numBytes, chunkSize);

            threadPool = new ThreadPool(
                            WorkerThreads, MaxWorkItems,
                            new ThreadPool.WorkCallback(DispatchRequest)
                            );
#if blee                            
           for (int i = 0; i < 50; i++) {
                for (int j = 0; j < 40; j++) {
                    bool isFull = threadPool.QueueUserWorkItem(new ThreadPool.WorkCallback(test), ".");
                    while (isFull) {
                        Thread.Sleep(2); 
                        isFull = threadPool.QueueUserWorkItem(new ThreadPool.WorkCallback(test), "yes\n");
                    }
                }
                Thread.Sleep(300);
            }
#endif 
        }

        public static void Usage()
        {
            Console.WriteLine("blastserver  <port> <numBytes> <chunkSize>");
        }
        
        public void  Shutdown()
        {
            threadPool.Shutdown(); 
        }
#if SINGULARITY        
        internal static int AppMain(Parameters! config)
        {
        
            if (config.port > 65536 || config.port < 0) {
                Console.WriteLine("Port number out of range: {0}", config.port);
                return -1;
            }
        
            ushort port = (ushort) config.port; 
            uint numBytes = (uint) config.numBytes;
            uint chunkSize = (uint) config.chunkSize;
            BlastServer bs = new BlastServer( port, numBytes, chunkSize); 
                    
            bs.Listen();            
            bs.Shutdown(); 
            return 0; 
        }
#else         
        public static int Main(string[] /*!*/ args)
        {
            int start = -1;
            if (args.Length < 4 + start) {
                Usage();
                return 1;
            }

            ushort port;

            try {
                port = UInt16.Parse(args[1+start]);
            }
            catch (FormatException) {
                Console.WriteLine("Malformed port number: {0}", args[1+start]);
                return -1;
            }
            catch (OverflowException) {
                Console.WriteLine("Port number out of range: {0}", args[1+start]);
                return -1;
            }

            uint numBytes;

            try {
                numBytes = UInt32.Parse(args[2+start]);
            }

            catch (FormatException) {
                Console.WriteLine("Malformed number of bytes: {0}", args[2+start]);
                return -1;
            }
            catch (OverflowException) {
                Console.WriteLine("Byte count out of range: {0}", args[2+start]);
                return -1;
            }

            uint chunkSize;

            try {
                chunkSize = UInt32.Parse(args[3+start]);
            }
            catch (FormatException) {
                Console.WriteLine("Malformed chunk size: {0}", args[3+start]);
                return -1;
            }
            catch (OverflowException) {
                Console.WriteLine("Chunk size out of range: {0}", args[3+start]);
                return -1;
            }
            BlastServer bs = new BlastServer( port, numBytes, chunkSize); 
            
            bs.Listen();            
            bs.Shutdown(); 
            return 0; 
        }
#endif        
    } // end class TcpBlast
}
