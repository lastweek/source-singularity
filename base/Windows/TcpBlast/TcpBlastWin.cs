////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TcpBlast.cs
//

using System;
using System.Net;
using System.Collections.Generic;
using System.Diagnostics;
using System.Net.Sockets;


static class TcpBlast
{
    public static int Main(string[] args)
    {
        try {
            Dictionary<String, String> namedargs;
            string[] posargs;
            ParseArgs(args, out namedargs, out posargs);

            if (posargs.Length == 0) {
                Usage();
                return 1;
            }

            if (posargs[0] == "accept") {
                return Accept(namedargs);
            }
            else if (posargs[0] == "connect") {
                return Connect(namedargs);
            }
            else {
                Usage();
                return 1;
            }
        }
        catch (Exception ex) {
            ShowException(ex);
            return 1;
        }
    }

    static void Usage()
    {
        Console.WriteLine("This program tests TCP/IP implementations by sending or receiving");
        Console.WriteLine("known sequences of bytes.");
        Console.WriteLine();
        Console.WriteLine("Usage:");
        Console.WriteLine();
        Console.WriteLine("    tcpblast accept [-port:<port>]");
        Console.WriteLine("    tcpblast connect -dest:<ipaddress> [-port:<port>]");

    }

    static void ParseArgs(
        string[] rawargs,
        out Dictionary<String, String> namedargs,
        out string[] posargs)
    {
        Dictionary<String, String> namedlist = new Dictionary<String, String>();
        List<String> poslist = new List<String>();
        foreach (string arg in rawargs) {
            if (String.IsNullOrEmpty(arg)) {
                continue;
            }
            if (arg[0] == '/' || arg[0] == '-') {
                int separator = arg.IndexOf(':', 1);
                if (separator == -1) {
                    separator = arg.IndexOf('=', 1);
                }
                string name;
                string value;
                if (separator != -1) {
                    name = arg.Substring(1, separator - 1);
                    value = arg.Substring(separator + 1);
                }
                else {
                    name = arg.Substring(1);
                    value = "";
                }
                namedlist[name] = value;
            }
            else {
                poslist.Add(arg);
            }
        }
        namedargs = namedlist;
        posargs = poslist.ToArray();
    }

    static void Connect(string[] args)
    {
        for (int i = 1; i < args.Length; i++) {
        }
    }

    const int DefaultPort = 4000;


    static IInt32SequenceFactory GetSequenceFactory(Dictionary<String, String> args)
    {
        string name;
        if (!args.TryGetValue("seq", out name)) {
            return delegate { return new AscendingSequence(0, 1); };
        }
        IInt32SequenceFactory factory = WellKnownSequences.GetWellKnownSequence(name);
        return factory;
    }

    static int Accept(Dictionary<String, String> args)
    {
        IInt32SequenceFactory sequenceFactory = GetSequenceFactory(args);
        if (sequenceFactory == null) {
            Console.WriteLine("Invalid sequence specified.");
            return 1;
        }

        using (Socket listener = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp)) {

            int port = DefaultPort;
            string portString;
            if (args.TryGetValue("port", out portString)) {
                if (!Int32.TryParse(portString, out port)) {
                    Console.WriteLine("Invalid port string.");
                    return 1;
                }
            }

            IPEndPoint any = new IPEndPoint(IPAddress.Any, port);

            try { listener.Bind(any); }
            catch (Exception ex) {
                Console.WriteLine("Bind failed.");
                ShowException(ex);
                return 1;
            }

            try { listener.Listen(5); }
            catch (Exception ex) {
                Console.WriteLine("Listen failed.");
                ShowException(ex);
                return 1;
            }

            for (; ; ) {
                Socket client;

                Console.WriteLine("Waiting for client to connect at port: " + listener.LocalEndPoint);
                try { client = listener.Accept(); }
                catch (Exception ex) {
                    Console.WriteLine("Accept failed.");
                    ShowException(ex);
                    break;
                }

                Console.WriteLine("Accepted client.");

                try {
                    RunClient(args, client, sequenceFactory);
                }
                catch (Exception ex) {
                    ShowException(ex);
                }
                finally {
                    client.Close();
                }

                Console.WriteLine();
            }
        }

        return 0;
    }

    static int Connect(Dictionary<String, String> args)
    {
        IInt32SequenceFactory sequenceFactory = GetSequenceFactory(args);
        if (sequenceFactory == null) {
            Console.WriteLine("Invalid sequence specified.");
            return 1;
        }

        string destText;
        if (!args.TryGetValue("dest", out destText)) {
            Console.WriteLine("Connect requires /dest:[xxx] parameter.");
            return 1;
        }

        int port = DefaultPort;
        string portString;
        if (args.TryGetValue("port", out portString)) {
            if (!Int32.TryParse(portString, out port)) {
                Console.WriteLine("Invalid port string.");
                return 1;
            }
        }

        Socket socket = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);

        try {

            try {
                socket.Connect(destText, port);
            }
            catch (Exception ex) {
                Console.WriteLine("Failed to connect to '{0}' at port {1}.", destText, port);
                ShowException(ex);
                return 1;
            }


            Console.WriteLine("Connected to {0}.", socket.RemoteEndPoint);

            RunClient(args, socket, sequenceFactory);
        }
        finally {
            socket.Close();
        }

        return 0;
    }

    static void RunClient(Dictionary<String, String> args, Socket client, IInt32SequenceFactory sequenceFactory)
    {
        Console.WriteLine("Running tests.");

        bool blast = args.ContainsKey("blast");

        if (blast) {
            RunBlast(args, client, sequenceFactory);
        }
        else {
            RunGulp(args, client, sequenceFactory);
        }
    }


    static void RunBlast(Dictionary<String, String> args, Socket client, IInt32SequenceFactory sequenceFactory)
    {
        Console.WriteLine("Blasting TCP client...");

        IInt32Sequence sequence = sequenceFactory();

        int blockSize = 5112;

        long sequenceNumber = 0;

        byte[] block = new byte[blockSize];

        RateWatcher rate = new RateWatcher();

        for (; ; ) {

            for (int i = 0; i < blockSize; i++) {
                int f = sequence.GetNext();
                block[i] = (byte)(f & 0xff);
                // Debug.WriteLine(String.Format("{0,3} -> 0x{1:x}", i, block[i]));
            }

            int bytesTransferred = client.Send(block, 0, blockSize, SocketFlags.None);
            if (bytesTransferred != blockSize) {
                Console.WriteLine("The send transferred fewer bytes than requested!");
                break;
            }

            sequenceNumber += blockSize;

            rate.AddBytes(blockSize);
        }
    }

    static void RunGulp(Dictionary<String, String> args, Socket client, IInt32SequenceFactory sequenceFactory)
    {
        Console.WriteLine("Running Gulp.");

        IInt32Sequence sequence = sequenceFactory();

        long sequenceNumber = 0;

        int blockSize = 5112;

        byte[] block = new byte[blockSize];

        int ticksAtLastPrint = Environment.TickCount;

        RateWatcher rate = new RateWatcher();

        for (; ; ) {

            int bytesRead = client.Receive(block);
            if (bytesRead == 0) {
                Console.WriteLine("The socket has closed.");
                return;
            }

            // Verify that the contents match the expected sequence.
            for (int i = 0; i < bytesRead; i++) {
                int f = sequence.GetNext();
                byte expected = (byte)(f & 0xff);

                if (block[i] != expected) {
                    Console.WriteLine("Received sequence does not match expected sequence!");
                    Console.WriteLine("At stream offset {0} (0x{0:x}), expected 0x{1:x}, received 0x{2:x}.",
                        sequenceNumber,
                        expected,
                        block[i]);
                    return;
                }
            }

            sequenceNumber += bytesRead;

            rate.AddBytes(bytesRead);

        }
    }

    class RateWatcher
    {
        public void AddBytes(int count)
        {
            _bytesSinceLastReport += count;

            int ticksNow = Environment.TickCount;
            TimeSpan elapsed = TimeSpan.FromMilliseconds(ticksNow - _ticksAtLastReport);

            if (elapsed >= _reportInterval) {
                double bytesPerSecond = _bytesSinceLastReport / elapsed.TotalSeconds;
                Console.WriteLine("Transfer rate: {0}", BytesPerSecondToString(bytesPerSecond));
                _bytesSinceLastReport = 0;
                _ticksAtLastReport = ticksNow;
            }
        }

        int _ticksAtLastReport = Environment.TickCount;

        long _bytesSinceLastReport;

        TimeSpan _reportInterval = TimeSpan.FromSeconds(3);

        public TimeSpan ReportInterval
        {
            get { return _reportInterval; }
            set { _reportInterval = value; }
        }

        public static string BytesPerSecondToString(double bps)
        {
            if (bps < 1000) {
                return String.Format("{0:F3} Bytes/Sec", bps);
            }
            if (bps < 1e6) {
                return String.Format("{0:F3} KBytes/Sec", bps / 1000.0);
            }
            if (bps < 1e9) {
                return String.Format("{0:F3} MBytes/Sec", bps / 1e6);
            }
            return String.Format("{0:F3} GBytes/Sec", bps / 1e9);
        }
    }


    static void ShowException(Exception ex)
    {
        Console.WriteLine("{0}: {1}", ex.GetType().FullName, ex.Message);
        for (Exception inner = ex.InnerException; inner != null; inner = inner.InnerException) {
            Console.WriteLine("{0}: {1}", inner.GetType().FullName, inner.Message);
        }
    }
}

class AFewPrimes : IInt32Sequence
{
    static readonly int[] primes = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31 };

    int index;

    public int GetNext()
    {
        index = (index + 1) % primes.Length;
        return primes[index];
    }
}
