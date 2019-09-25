///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

using System;
using System.Net.Sockets;
using System.Net;
using System.Text;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.FileSystem;
using Microsoft.Singularity.V1.Services;

using FileSystem.Utils;

namespace Microsoft.Singularity.Applications
{
    internal enum TftpOpcode : ushort
    {
        RRQ=1, WRQ=2, DATA=3, ACK=4, ERROR=5
    };

    internal struct TftpHdr
    {
        public TftpOpcode Opcode;
        public ushort Arg;

        public TftpHdr(byte[]! buffer, int offset)
        {
            Opcode = (TftpOpcode)((ushort)buffer[offset+0] << 8 | buffer[offset+1]);
            Arg    = (ushort)((ushort)buffer[offset+2] << 8 | buffer[offset+3]);
            //              UnMarshal(buffer, offset);
        }
        public void Marshal(byte[]! buffer, int offset)
        {
            buffer[offset+0] = (byte)((ushort)Opcode>>8 & 0xff);
            buffer[offset+1] = (byte)((ushort)Opcode>>0 & 0xff);
            buffer[offset+2] = (byte)(Arg>>8 & 0xff);
            buffer[offset+3] = (byte)(Arg>>0 & 0xff);
        }
        public void UnMarshal(byte[]! buffer, int offset)
        {
            Opcode = (TftpOpcode)((ushort)buffer[offset+0] << 8 | buffer[offset+1]);
            Arg    = (ushort)((ushort)buffer[offset+2] << 8 | buffer[offset+3]);
        }
    };

     public class TftpClient
    {
        Socket! s;

        public TftpClient(IPAddress! server)
        {
            Socket s = this.s = new Socket(AddressFamily.InterNetwork, SocketType.Dgram, ProtocolType.Udp);
            IPEndPoint ep = new System.Net.IPEndPoint(server, 69);
            Console.Write("EP= {0}\n", ep);
            // Connect here
            s.Connect(ep);
        }

        static int BuildRequest(byte[]! packet, TftpOpcode op, string! filename)
        {
            TftpHdr hdr = new TftpHdr();
            byte[] tmp;

            hdr.Opcode = op;
            hdr.Marshal(packet, 0);
            int off = 2;
            tmp = Encoding.ASCII.GetBytes(filename);
            tmp.CopyTo(packet, off);
            off += tmp.Length;
            packet[off++] = 0;
            tmp = Encoding.ASCII.GetBytes("octet");
            tmp.CopyTo(packet, off);
            off += tmp.Length;
            packet[off++] = 0;
            Console.WriteLine("Done");
            return off;
        }

        public string Get(string! filename, string localName, bool verboseMode)
        {
            TftpHdr hdr = new TftpHdr();
            byte[] request;
            byte[] reply = new byte[8192];
            int success;
            FileContract.Imp persistHandle = null ;
            long curPos = 0 ;
            int len;
            int rc;

            if (null != localName) {
                Console.WriteLine ("Creating file "+localName);
                success = FileUtils.CreateFile(localName);
                if (0 == success) {
                    persistHandle = FileUtils.OpenFile(localName);
                    if (null == persistHandle) {
                        Console.WriteLine("unable to open file " + localName);
                        return "";
                    }
                }
                else {
                    Console.WriteLine("unable to create file " + localName);
                    return "";
                }
            }

            request = new byte[4 + 512];

            len = BuildRequest(request, TftpOpcode.RRQ, filename);
            bool done = false;
            hdr.UnMarshal(request, 0);
            rc = s.Send(request, len, SocketFlags.None);
            if (verboseMode) Console.WriteLine("Sent RRQ rc={0}", rc);

            byte []! in ExHeap buf = new[ExHeap] byte[512];
            //string str = null;
            int count = 0;
            int lastBlock = -1;
            while (!done) {
                //Socket.Select(listenList, null, null, 1000);
                if (s.Poll(1000000, SelectMode.SelectRead)) {
                    rc = s.Receive(reply);
                    if (verboseMode) Console.WriteLine("Receive rc={0}", rc);
                    if (rc >= 4) {
                        TftpHdr rh = new TftpHdr(reply, 0);
                        //Console.WriteLine("Opcode {0} Arg {1} rc={2} curPos={3}", rh.Opcode, rh.Arg, rc, curPos);
                        if (rh.Arg == lastBlock)
                                Console.WriteLine(" duplicate block? block ="+rh.Arg);
                        lastBlock = rh.Arg;
                        if (rh.Opcode == TftpOpcode.DATA) {
                            if (!verboseMode) {
                                Console.Write(".");
                                if (count++ > 50) {
                                    count = 0;
                                    Console.Write("\n");
                                }
                            }
                            else {
                                //str = Encoding.ASCII.GetString(reply, 4, rc-4);
                                //Console.WriteLine("pos="+curPos+" str="+str);
                                //str = null;
                            }
                            if (persistHandle != null) {
                                Bitter.FromByteArray(buf,0,rc-4,reply,4);
                                persistHandle.SendWrite(buf,0,curPos,rc-4);
                                switch receive {
                                    case persistHandle.AckWrite( _buf, bytesWritten,  error) :
                                        buf = _buf;
                                        curPos = rh.Arg * 512;
                                        break;
                                    case persistHandle.ChannelClosed() :
                                        Console.WriteLine("File handle closed. Quitting");
                                        delete persistHandle;
                                        return null;
                                        break;
                                    case unsatisfiable:
                                        Console.WriteLine("receive is unsatisfiable. Quitting");
                                        delete persistHandle;
                                        return null;
                                        break;
                                }
                            }
                        }
                        // Build new ack packet - acts as REQ for next block
                        hdr.Opcode = TftpOpcode.ACK;
                        hdr.Arg = rh.Arg;
                        hdr.Marshal(request, 0);
                        len = 4;
                    }
                    if (rc < 512 + 4) done = true;
                }
                else {
                    //Console.WriteLine("poll for data failed!");
                    //return null;
                }
                rc = s.Send(request, len, SocketFlags.None);
                if (verboseMode)Console.WriteLine("Sent {0} {1}  rc {2}", hdr.Opcode, hdr.Arg, rc);
                //Thread.Sleep(1000);
            }
            if (persistHandle != null) {
                Console.WriteLine("Closing EP handle via delete");
                delete persistHandle;
            }
            delete buf;
            return null;
        }

        public string Put(string! filename, string localName)
        {
            TftpHdr hdr = new TftpHdr();
            byte[] request;
            byte[] reply = new byte[8192];
            byte []! in ExHeap buf;
            FileContract.Imp  fileHandle = null ;

            int len;
            int rc;
            long fileLength = 0;
            ErrorCode errorOut; 

            if (null != localName) {
                DirectoryServiceContract.Imp! rootNS = DirectoryService.NewClientEndpoint();
                FileAttributesRecord record;
                bool ok  = FileUtils.GetAttributes(localName, rootNS, out record, out  errorOut);
                delete rootNS; 
                
                if (!ok) {
                    Console.WriteLine("Unable to open file ({0}) for send. reason:{1}",
                        localName, SdsUtils.ErrorCodeToString(errorOut)
                        );
                    return null;
                }

                fileLength = record.FileSize;

                fileHandle = FileUtils.OpenFile(localName);
                if (null == fileHandle) {
                    Console.WriteLine("Unable to open file "+localName+" for send");
                    return null;
                }
            }
            request = new byte[4 + 512];

            len = BuildRequest(request, TftpOpcode.WRQ, filename);
            int pos = 0;
            bool done = false;

            rc = s.Send(request, len, SocketFlags.None);
            Console.WriteLine("Sent WRQ rc={0}", rc);

            buf = new[ExHeap] byte[512];
            int threshold = 20;
            int waitCount = 0;
            Console.WriteLine(" file size =" + fileLength);
            while (!done) {
                //Socket.Select(listenList, null, null, 1000);
                if (s.Poll(100000, SelectMode.SelectRead)) {
                    rc = s.Receive(reply);
                    Console.WriteLine("Receive rc={0}", rc);
                    if (rc >= 4) {
                        TftpHdr rh = new TftpHdr(reply, 0);
                        Console.WriteLine("PUT: Opcode {0} Arg {1}", rh.Opcode, rh.Arg);

                        if (rh.Opcode == TftpOpcode.ACK) {
                            int datalen;
                            int error;
                            long bytesRead;
                            Console.WriteLine("ACK for block {0}, pos={1}", rh.Arg,pos);
                            waitCount = 0;
                            if (pos >= fileLength) {
                                Console.WriteLine(" here");
                                bytesRead = 0;
                            }
                            else {
                if (fileHandle == null)
                    throw new Exception("fileHandle is null when I want to SendRead");
                                fileHandle.SendRead(buf, 0, pos, 512);
                                fileHandle.RecvAckRead(out buf, out bytesRead, out error);
                                if (error != 0) DebugStub.Break();

                                // If we get an ack we can send the next block
                                pos = (rh.Arg+1) * 512;
                            }
                             // Build new DATA packet
                            hdr.Opcode = TftpOpcode.DATA;
                            hdr.Arg = rh.Arg;
                            hdr.Arg++;
                            hdr.Marshal(request, 0);
                            datalen = Math.Min(512, (int)bytesRead);
                            if (datalen < 512) done = true;
                            //Encoding.ASCII.GetBytes(contents, pos, datalen, request, 4);
                            Bitter.ToByteArray(buf,0,datalen,request,4);
                            len = 4 + datalen;
                        }
                        else {
                            Console.WriteLine("NOT AN ACK!\n");
                            DebugStub.Break();
                        }
                    }
                    rc = s.Send(request, len, SocketFlags.None);
                    Console.WriteLine("Sent {0} {1}  rc {2}", hdr.Opcode, hdr.Arg, rc);
                }
                else {
                    Console.WriteLine("Waiting.");
                    waitCount++;
                    if (waitCount > threshold) {
                        Console.WriteLine (" exceeded timeout threshold");
                        done = true;
                        break;
                    }
                }
                //Thread.Sleep(1000);
            }
            Console.WriteLine("Done");
            delete buf;
            if (fileHandle != null)
                delete fileHandle;
            return null;
        }

        private static IPAddress GetServerAddress(string server)
        {
            try {
                return IPAddress.Parse(server);
            }
            catch {
            }

            try {
                IPHostEntry he = Dns.GetHostByName(server);
                return he.AddressList[0];
            }
            catch {
            }
            return null;
        }

        private static void Usage()
        {
            Console.WriteLine("Usage: tftpclient <server> [-i] <put|get> <getfilename> [ <putfilename> ]");
        }

        /// <summary>
        /// The main entry point for the application.
        /// </summary>
        public static int Main(string[]! args)
        {
            bool verboseMode = false;
            String localName, remoteName;
            if (args.Length < 4 || args.Length > 6) {
                Usage();
                return 1;
            }

            IPAddress server = GetServerAddress(args[1]);
            if (server == null) {
                Console.WriteLine("Could not find server : {0}", args[1]);
                return 2;
            }

            int pos =2;
            if (args[pos] == "-v") {
                verboseMode = true;
                pos++;
            }

            bool doGet;
            switch (args[pos]) {
                case "get":
                    doGet = true;
                    break;
                case "put":
                    doGet = false;
                    break;
                default:
                    Usage();
                    return -1;
            }
            pos++;
            remoteName = (!)args[pos];
            pos++;
            localName = null;
            if (pos >= args.Length) {
                Console.WriteLine("no destination given");
            }
            else {
                localName = args[pos];
            }
            Console.WriteLine("doGet="+doGet+" src="+remoteName+" dest="+localName);
            TftpClient tftpClient = new TftpClient(server);
            if (doGet) {
                string contents = tftpClient.Get(remoteName,localName,verboseMode);
                if (verboseMode) Console.WriteLine("Contents:\n{0}", contents);
            }
            else {
                //put
                tftpClient.Put(remoteName,localName);
            }
            return 0;
        } // end Main
    } // end class TftpClient
} // end namespace Microsoft.Singularity.Shell
