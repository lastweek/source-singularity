///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DhcpFmt.cs
//
//  Note: The key DHCP RFC is 2131.
//

using System;
using System.Collections;

using System.Net.IP;
using Drivers.Net;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.SingSharp;

namespace Microsoft.Singularity.NetStack2
{
    public class InvalidDhcpFormatException : SystemException
    {
        public InvalidDhcpFormatException(String message)
            : base(message)
        {
        }

        public InvalidDhcpFormatException(String message,
                                          Exception innerException)
            : base(message, innerException)
        {
        }

        public InvalidDhcpFormatException(String format, params object [] args)
            : base (String.Format(format, args))
        {
        }
    }

    sealed public class DhcpFormat
    {
#region FormatFields
        internal byte op;          // Message Type
        internal byte htype;       // Hardware Type
        internal byte hlen;        // Hardware Length
        internal byte hops;        // Relay hops
        internal uint xid;         // Transaction ID (host order)
        internal ushort secs;      // Seconds since transaction start (host order)
        internal ushort flags;     // Flags (host order)
        internal uint ciaddr;      // Client IP if known (host order)
        internal uint yiaddr;      // Your IP address (host order)
        internal uint siaddr;      // Next Server address (host order)
        internal uint giaddr;      // Relay agent IP address (host order)
        internal byte []  chaddr;  // Client h/w address (16-bytes)
        internal byte [] sname;   // Optional server name (64-bytes null term)
        internal byte []  file;    // Boot file name (128-bytes null terminated)
        internal uint cookie;      // Mandatory DHCP option
        internal byte []  options; // Variable size
#endregion // FormatFields

        internal int     optionsUsedLength;

        // Constants
        public const int MinLength             = 240; // Min DHCP packet
        public const int HardwareAddressLength = 16;  // chaddr fixed length
        public const int ServerNameLength      = 64;  // sname fixed length
        public const int BootFileLength        = 128; // file length
        public const int MaxOptionsLength      = 512; // Really H/W dependent
        private const byte EndMarker           = 255;
        private const int EndMarkerLength      = 1;

        internal const uint DhcpCookie         = 0x63825363; // DHCP Cookie

        public const int ClientPort = 68;
        public const int ServerPort = 67;

        public enum BootType : byte
        {
            NotSpecified = 0,
            Request  = 1,       // Client to Server Message
            Reply    = 2        // Server to Client Message
        }

        public enum MessageType : byte
        {
            Discover = 1,
            Offer    = 2,
            Request  = 3,
            Decline  = 4,
            Ack      = 5,
            Nak      = 6,
            Release  = 7,
            Inform   = 8
        }

        // http://www.iana.org/assignments/arp-parameters
        public enum HType : byte
        {
            Ethernet             = 1,
            ExperimentalEthernet = 2,
            AX25                 = 3,
            ProNET               = 4,
            Chaos                = 5,
            Serial               = 20,
            IEEE1394_1995        = 24,
            ARPSec               = 30,
            IPSecTunnel          = 31,
            Infiniband           = 32
        }

        public DhcpFormat(BootType bootType)
        {
            op      = (byte)bootType;
            chaddr  = new byte[HardwareAddressLength];
            sname   = new byte[ServerNameLength];
            file    = new byte[BootFileLength];
            cookie  = DhcpCookie;
            options = new byte[MaxOptionsLength];
            flags   = 0x8000;   // Request broadcast responses
            optionsUsedLength = 0;
        }

        public DhcpFormat(MessageType messageType)
            : this(GetBootType(messageType))
        {
            AddOption(DhcpMessageType.Create((byte)messageType));
        }

        public int Size
        {
            get { return MinLength + optionsUsedLength + EndMarkerLength; }
        }

        public BootType BootMessageType
        {
            get { return (BootType)op; }
        }

        public IPv4 ClientIPAddress
        {
            get { return new IPv4(ciaddr); }
            set { ciaddr = (uint)value; }
        }

        public IPv4 YourIPAddress
        {
            get { return new IPv4(yiaddr); }
            set { yiaddr = (uint)value; }
        }

        public IPv4 NextServerIPAddress
        {
            get { return new IPv4(siaddr); }
            set { siaddr = (uint)value; }
        }

        public IPv4 RelayAgentIPAddress
        {
            get { return new IPv4(giaddr); }
            set { giaddr = (uint)value; }
        }

        public byte Hops
        {
            get { return hops; }
            set { hops = value; }
        }

        public uint TransactionID
        {
            get { return xid;  }
            set { xid = value; }
        }

        public ushort TransactionSeconds
        {
            get { return secs; }
            set { secs = value; }
        }

        public ushort Flags
        {
            get { return flags; }
            set { flags = value; }
        }

        public string ServerName
        {
            get { return BytesToString(sname); }
            set { StringToBytes(value, sname); }
        }

        public string BootFile
        {
            get { return BytesToString(file); }
            set { StringToBytes(value, file); }
        }

        public void SetHardwareAddress (EthernetAddress ea)
        {
            hlen   = 6;
            htype  = (byte)HType.Ethernet;
            chaddr = new byte[HardwareAddressLength];
            ea.CopyOut(chaddr, 0);
        }

        public EthernetAddress GetHardwareAddress()
        {
            if (htype != (byte)HType.Ethernet) {
                // XXX Throw some nasty exception
            }
            return EthernetAddress.ParseBytes(chaddr, 0);
        }

        public SortedList GetOptions()
        {
            return DhcpOptionParser.Parse(options, 0, this.optionsUsedLength);
        }

        public void AddOption(IDhcpOption option)
        {
            int newLength = option.PayloadLength + 2 + optionsUsedLength;
            if (newLength > this.options.Length) {
                newLength = (newLength + 64) & ~3;
                byte [] newOptions = new byte [newLength];
                Buffer.MoveMemory(newOptions, this.options, 0, 0, this.options.Length);
                this.options = newOptions;
            }
            option.Pack(this.options, ref optionsUsedLength);
        }

        private static String BytesToString(byte [] bytes)
        {
            // Poorman's StringBuilder
            char[] chars = new char[bytes.Length];
            int i;
            for (i = 0; i < bytes.Length; i++) {
                if (bytes[i] == 0)
                    break;
                chars[i] = (char)bytes[i];
            }
            return new String(chars, 0, i);
        }

        private static void StringToBytes(string from, byte [] to)
        {
            int end = Math.Min(from.Length, to.Length);
            for (int i = 0; i < end; i++) {
                to[i] = (byte)from[i];
            }
            // Zero-terminate
            if (end != to.Length) {
                to[end] = 0;
            }
        }

        public static DhcpFormat Parse(Bytes buffer)
        {
            DhcpFormat p = new DhcpFormat(BootType.NotSpecified);
            p.optionsUsedLength = 0;

            if (buffer.Length < DhcpFormat.MinLength) {
                throw new InvalidDhcpFormatException("Format less than minimum size");
            }
            int offset = 0;
            p.op = buffer[offset++];
            if (p.op != (byte)BootType.Request &&
                p.op != (byte)BootType.Reply)
            {
                throw new InvalidDhcpFormatException("Bad Type (op = {0})", p.op);
            }
            p.htype = buffer[offset++];
            // No check

            p.hlen = buffer[offset++];
            if (p.hlen > HardwareAddressLength) {
                throw new InvalidDhcpFormatException("Bad address length (hlen {0})",
                                            p.hlen);
            }
            p.hops = buffer[offset++];
            // No check

            p.xid = NetworkBitConverter.ToUInt32(buffer, offset);
            offset += 4;

            p.secs = NetworkBitConverter.ToUInt16(buffer, offset);
            offset += 2;

            p.flags = NetworkBitConverter.ToUInt16(buffer, offset);
            offset += 2;

            p.ciaddr = NetworkBitConverter.ToUInt32(buffer, offset);
            offset += 4;

            p.yiaddr = NetworkBitConverter.ToUInt32(buffer, offset);
            offset += 4;

            p.siaddr = NetworkBitConverter.ToUInt32(buffer, offset);
            offset += 4;

            p.giaddr = NetworkBitConverter.ToUInt32(buffer, offset);
            offset += 4;

            Bitter.ToByteArray(buffer, offset, HardwareAddressLength, p.chaddr, 0);
            offset += HardwareAddressLength;
            Bitter.ToByteArray(buffer, offset, ServerNameLength, p.sname, 0);
            offset += ServerNameLength;
            Bitter.ToByteArray(buffer, offset, BootFileLength, p.file, 0);
            offset += BootFileLength;

            p.cookie = NetworkBitConverter.ToUInt32(buffer, offset);
            offset += 4;
            if (p.cookie != DhcpCookie) {
                throw new InvalidDhcpFormatException("Bad cookie (0x{0x:x8})",
                                                     p.cookie);
            }
            int available = buffer.Length - offset;
            if (available > p.options.Length) {
                p.options = new byte [available];
            }
            p.optionsUsedLength = available;
            Bitter.ToByteArray(buffer, offset, available, p.options, 0);

            return p;
        }

        private static void Write(Bytes buffer, ref int offset, byte value)
        {
            buffer[offset++] = value;
        }

        private static void Write(Bytes buffer, ref int offset, ushort value)
        {
            buffer[offset++] = (byte)(value >> 8);
            buffer[offset++] = (byte)(value);
        }

        private static void Write(Bytes buffer, ref int offset, uint value)
        {
            buffer[offset++] = (byte)(value >> 24);
            buffer[offset++] = (byte)(value >> 16);
            buffer[offset++] = (byte)(value >> 8);
            buffer[offset++] = (byte)(value);
        }

        private static void Write(Bytes  buffer,
                                  ref int  offset,
                                  byte[]  values,
                                  int      valuesLength)
        {
            for (int i = 0; i < valuesLength; i++) {
                buffer[offset++] = values[i];
            }
        }

        public int Write(Bytes buffer, int offset)
        {
            Write(buffer, ref offset, this.op);
            Write(buffer, ref offset, this.htype);
            Write(buffer, ref offset, this.hlen);
            Write(buffer, ref offset, this.hops);
            Write(buffer, ref offset, this.xid);
            Write(buffer, ref offset, this.secs);
            Write(buffer, ref offset, this.flags);
            Write(buffer, ref offset, this.ciaddr);
            Write(buffer, ref offset, this.yiaddr);
            Write(buffer, ref offset, this.siaddr);
            Write(buffer, ref offset, this.giaddr);
            Write(buffer, ref offset, this.chaddr, this.chaddr.Length);
            Write(buffer, ref offset, this.sname, this.sname.Length);
            Write(buffer, ref offset, this.file, this.file.Length);
            Write(buffer, ref offset, this.cookie);

            Write(buffer, ref offset, this.options, this.optionsUsedLength);
            Write(buffer, ref offset, EndMarker);
            return offset;
        }


        public static bool IsRequestMessage(MessageType m)
        {
            return (m == MessageType.Discover || m == MessageType.Request  ||
                    m == MessageType.Decline  || m == MessageType.Release  ||
                    m == MessageType.Inform);
        }

        public static bool IsResponseMessage(MessageType m)
        {
            return (m == MessageType.Offer || m == MessageType.Ack ||
                    m == MessageType.Nak);
        }

        public static BootType GetBootType(MessageType m)
        {
            return IsRequestMessage(m) ? BootType.Request : BootType.Reply;
        }
    }
}
