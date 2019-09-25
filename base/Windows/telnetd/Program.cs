// Microsoft Research Singularity
// Copyright (c) Microsoft Corporation.  All rights reserved.
// 
// Project: telnet daemon (testing purposs only)
// 
// NOTES / CAVEATS:
// - Doesn't echo keyboard input until carriage return.
// - Doesn't support control sequences (Ctrl-C, history, etc.)
// - Doesn't negotiate.  Only works with the Windows XP telent client.
// - Doesn't shutdown gracefully.
// - Doesn't try to be robust (handle exceptions, etc.)
// 
using System;
using System.Diagnostics;
using System.Net;
using System.Net.NetworkInformation;
using System.Net.Sockets;

namespace telnetd
{
    class Program
    {
        private Process p;
        private byte[] bufOutput;
        private byte[] bufError;
        private TcpClient client;
        private NetworkStream stm;
        private byte[] bufNet;

        const byte IAC = 255;                   // telnet "interpret as command" escape
        const byte CODE_WILL = 251;             // telnet commands
        const byte CODE_WONT = 252;
        const byte CODE_DO = 253;
        const byte CODE_DONT = 254;
        const byte OPTION_ECHO = 0x01;          // telnet command options
        const byte OPTION_SUPPRESSGA = 0x03;

        Program(TcpClient c)
        {
            client = c;
            stm = client.GetStream();
        }

        void SendString(string s)
        {
            Byte[] data = System.Text.Encoding.ASCII.GetBytes(s);
            stm.Write(data, 0, data.Length);
        }

        void SendOption(byte code, byte option)
        {
            byte[] data = new byte[3];
            data[0] = IAC;
            data[1] = code;
            data[2] = option;
            stm.Write(data, 0, data.Length);
        }

        void ReadOption(out byte code, out byte option)
        {
            int b1 = stm.ReadByte();
            int b2 = stm.ReadByte();
            int b3 = stm.ReadByte();
            code = (byte)b2;
            option = (byte)b3;
        }

        void StdOutCallback(IAsyncResult result)
        {
            int cb = p.StandardOutput.BaseStream.EndRead(result);
            if (cb > 0) {
                stm.Write(bufOutput, 0, cb);
            }
            p.StandardOutput.BaseStream.BeginRead(bufOutput, 0, bufOutput.Length, StdOutCallback, null);
        }

        void StdErrCallback(IAsyncResult result)
        {
            int cb = p.StandardError.BaseStream.EndRead(result);
            if (cb > 0) {
                stm.Write(bufError, 0, cb);
            }
            p.StandardError.BaseStream.BeginRead(bufError, 0, bufError.Length, StdErrCallback, null);
        }

        void NetworkReadCallback(IAsyncResult result)
        {
            int cb = stm.EndRead(result);
            if (cb > 0) {
                ProcessEscapes(bufNet, cb);
                string s = System.Text.Encoding.ASCII.GetString(bufNet, 0, cb);
                p.StandardInput.Write(s);
            }
            IAsyncResult res = stm.BeginRead(bufNet, 0, bufNet.Length, NetworkReadCallback, null);
        }

        int ProcessEscapes(byte[] buf, int cb)
        {
            // TODO:
            //
            //for (int i = 0; i < cb; i++) {
            //  if (bufNet[i] == IAC) {
            //      Debug.WriteLine("IAC " + bufNet[i + 1] + " " + bufNet[i + 2]);
            //  }
            //}
            //
            return cb;
        }

        void Run()
        {
            // Negotiate
            SendOption(CODE_WILL, OPTION_ECHO);
            SendOption(CODE_WILL, OPTION_SUPPRESSGA);
            byte code, option;
            ReadOption(out code, out option);
            ReadOption(out code, out option);

            // Send welcome message
            SendString("Welcome to the Singularity Telnet Service on ");
            IPGlobalProperties ipGlobal = IPGlobalProperties.GetIPGlobalProperties();
            SendString(ipGlobal.HostName);
            SendString("\r\n\r\n");

            // Create redirected command shell with ansi pipes
            p = new Process();
            p.StartInfo.FileName = "cmd.exe";
            p.StartInfo.Arguments = "/A";
            p.StartInfo.UseShellExecute = false;
            p.StartInfo.CreateNoWindow = true;
            p.StartInfo.RedirectStandardInput = true;
            p.StartInfo.RedirectStandardOutput = true;
            p.StartInfo.RedirectStandardError = true;
            p.Start();

            // Begin the async stdio reads
            bufOutput = new byte[256];
            bufError = new byte[256];
            p.StandardOutput.BaseStream.BeginRead(bufOutput, 0, bufOutput.Length, StdOutCallback, null);
            p.StandardError.BaseStream.BeginRead(bufError, 0, bufError.Length, StdErrCallback, null);

            // Begin the async network reads
            bufNet = new byte[256];
            IAsyncResult res = stm.BeginRead(bufNet, 0, bufNet.Length, NetworkReadCallback, null);

            // Wait for the shell to exit
            p.WaitForExit();
            client.Close();
        }

        static void Main(string[] args)
        {
            // Listen for incoming telnet sessions
            TcpListener listener = null;
            try {
                listener = new TcpListener(IPAddress.Parse("127.0.0.1"), 23);
                listener.Start();
                while (true) {
                    TcpClient c = listener.AcceptTcpClient();
                    Program p = new Program(c);
                    p.Run();
                }
            }
            catch (SocketException ex) {
                Console.WriteLine("SocketException {0}", ex);
            }
            finally {
                if (listener != null)
                    listener.Stop();
            }
        }
    }
}
