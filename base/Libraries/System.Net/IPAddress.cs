////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    This file is a wrapper around Singularity's internal networking types
//

using System;
using System.Net.IP; // Singularity networking type space
using System.Net.Sockets;
using Microsoft.Singularity.Io;
using Microsoft.Contracts;

//
// Currently this wrapper is IPv4-specific!
//
public class IPAddress {
    public static readonly IPAddress Any = new IPAddress(IPv4.Any);
    public static readonly  IPAddress Loopback = new IPAddress(IPv4.Loopback);
    public static readonly  IPAddress Broadcast = new IPAddress(IPv4.Broadcast);
    public static readonly  IPAddress None = Broadcast;

    internal IPv4 m_addr; // Our wrapped address

    // newAddress is provided in network order.
    [NotDelayed]
    public IPAddress(long newAddress) {
        SetFromLong(newAddress);
    }

    // address is MST byte first (index 0)
    public IPAddress(byte[]! address) {
        if (address.Length != 4) {
            throw new NotSupportedException("Byte array length must be 4");
        }

        uint addr  = ((uint)address[0]) << 24;
        addr += ((uint)address[1]) << 16;
        addr += ((uint)address[2]) << 8;
        addr += ((uint)address[3]);

        m_addr = new IPv4(addr);
    }

    public IPAddress(IPv4 addr)
    { m_addr = new IPv4(addr); }

    public static IPAddress! Parse(string ipString)
    { return new IPAddress(IPv4.Parse(ipString)); }

    private void SetFromLong(long value)
    {
        if (value < 0 || value > 0x00000000FFFFFFFF) {
            throw new ArgumentOutOfRangeException("value");
        }

        m_addr = new IPv4((uint)NetworkToHostOrder(value));
    }

    // TODO
    [ Obsolete("IPAddress.Address is address family dependant, use " +
               "Equals method for comparison.") ]
    public long Address {
        get {
            return (uint)m_addr;
        }
        set {
            SetFromLong(value);
        }
    }

    public AddressFamily AddressFamily {
        get {
            return AddressFamily.InterNetwork;
        }
    }

    public byte[] GetAddressBytes()
    { return m_addr.GetAddressBytes(); }

    public override string! ToString()
    { return m_addr.ToString(); }

    public static long HostToNetworkOrder(long host) {
        return ByteOrder.HostToBigEndian(host);
    }
    public static int HostToNetworkOrder(int host) {
        return ByteOrder.HostToBigEndian(host);
    }

    public static short HostToNetworkOrder(short host) {
        return ByteOrder.HostToBigEndian(host);
    }

    public static long NetworkToHostOrder(long network) {
        return ByteOrder.HostToBigEndian(network);
    }

    public static int NetworkToHostOrder(int network) {
        return ByteOrder.HostToBigEndian(network);
    }

    public static short NetworkToHostOrder(short network) {
        return ByteOrder.HostToBigEndian(network);
    }

    public static IPAddress operator&(IPAddress! lhs, IPAddress! rhs)
    { return new IPAddress(lhs.m_addr & rhs.m_addr); }

    public static bool IsLoopback(IPAddress! address)
    { return address.m_addr.IsLoopback(); }

    public override bool Equals(object comparand)
    { return m_addr.Equals(comparand); }

    public override int GetHashCode()
    { return m_addr.GetHashCode(); }
} // class IPAddress

