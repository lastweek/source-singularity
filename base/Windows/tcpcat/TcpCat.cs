// Microsoft Research Singularity
// Copyright (c) Microsoft Corporation.  All rights reserved.

// Choose a TCP port and listen for an incoming connection to the port.
// Then read from the connection, dumping the data to stdout.
// Arguments: none
// (Note: the tcp port is chosen by the underlying socket implementation,
// and printed to stderr when this program runs.)

using System;
using System.Net;
using System.Net.Sockets;

class TcpCat
{
    static void Main(string[] args)
    {
        TcpListener listener = new TcpListener(IPAddress.Any, 0);
        listener.Start();
        Console.Error.WriteLine(listener.LocalEndpoint);
        System.IO.Stream o = Console.OpenStandardOutput();
        TcpClient c = listener.AcceptTcpClient();
        NetworkStream stm = c.GetStream();
        for (;;) {
            int i = stm.ReadByte();
            if (i == -1) break;
            o.WriteByte((byte) i);
        }
    }
}
