// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
//

using System.Collections;
using System.Diagnostics;
using System;
//using System.Compiler;

using Drivers.Net;

namespace NetStack.Contracts
{
    public enum TcpError
    {
        Unknown = 1,
        AlreadyConnected,       // this connection is already in use
        Refused,                // the receiving host actively refused the connection
        Reset,                  // the connection was reset
        Timeout,                // no response was received
        ProtocolViolation,      // we received a TCP segment that is not acceptable in the current state
        ResourcesExhausted,     // out of memory, etc.
        Closed,                 // remote peer has closed socket
    }
}

namespace Microsoft.Singularity.NetStack
{
/*
    public class HardwareAddress
    {
        public byte b0, b1, b2, b3, b4, b5;

        public void Set(byte bt0, byte bt1, byte bt2, byte bt3, byte bt4, byte bt5)
        {
            b0 = bt0;
            b1 = bt1;
            b2 = bt2;
            b3 = bt3;
            b4 = bt4;
            b5 = bt5;
        }

        public void Set(byte[] bytes)
        {
            if (bytes.Length != 6) {
                throw new ArgumentException("Invalid array length in HardwareAddress()");
            }

            b0 = bytes[0];
            b1 = bytes[1];
            b2 = bytes[2];
            b3 = bytes[3];
            b4 = bytes[4];
            b5 = bytes[5];
        }
    }

    public class Network
    {
        public uint network;
        public uint netmask;
    }
*/

    public class InterfaceIPInfo
    {
        public uint address;
        public uint netmask;
        public uint gateway;
    }

    public class InterfaceInfo
    {
        public String driverName; // Friendly name, not programmatic name
        public String driverVersion;
        public uint linkSpeed;
        public EthernetAddress hardwareAddress;
        public InterfaceIPInfo[] ipConfigs; // Zero or more IP configs
    }
}

namespace Microsoft.Singularity.Io.Net
{
    public enum NicEventType : uint
    {
        NoEvent       = 0,
        ReceiveEvent  = 1u << 0,
        TransmitEvent = 1u << 1,
        LinkEvent     = 1u << 2,
    }

    public interface NicDeviceContract
    {
        // READY messages
        NicDeviceProperties GetDeviceProperties();
        void ConfigureIO();

        // IO_CONFIGURE_X messages
        void RegisterForEvents(NicDeviceEventContract ep);
        void SetChecksumProperties(ChecksumSupport properties);
        void StartIO();

        // IO_RUNNING messages
        PacketFifo GiveTxPacketsToDevice(PacketFifo packetFifo);
        PacketFifo GiveRxPacketsToDevice(PacketFifo packetFifo);
        void StopIO();
    }

    public interface NicDeviceEventContract
    {
        void NicDeviceEvent(NicEventType eventType);
    }

    public enum MacType : uint
    {
        Ethernet = 1,
        // ATM
        // FDDI
    }

    public enum ChecksumSupport : uint
    {
        None           = 0,
        Ip4Receive     = 1u << 0,
        Ip4Transmit    = 1u << 1,
        Udp4Receive    = 1u << 2,
        Udp4Transmit   = 1u << 3,
        Tcp4Receive    = 1u << 4,
        Tcp4Transmit   = 1u << 5,
        AllIp4Receive  = (Ip4Receive | Udp4Receive | Tcp4Receive),
        AllIp4Transmit = (Ip4Transmit | Udp4Transmit | Tcp4Transmit),
        AllIp4         = (AllIp4Receive | AllIp4Transmit),
        Ip6Receive     = 1u << 6,
        Ip6Transmit    = 1u << 7,
        Udp6Receive    = 1u << 8,
        Udp6Transmit   = 1u << 9,
        Tcp6Receive    = 1u << 10,
        Tcp6Transmit   = 1u << 11,
        AllIp6Receive  = (Ip6Receive | Udp6Receive | Tcp6Receive),
        AllIp6Transmit = (Ip6Transmit | Udp6Transmit | Tcp6Transmit),
        AllIp6         = (AllIp6Receive | AllIp6Transmit),
    }

    public class NicDeviceProperties
    {
        public String DriverName;
        public String DriverVersion;

        public MacType           MacType;
        public EthernetAddress MacAddress;

        public ChecksumSupport   ChecksumSupport;

        public int               MtuBytes;
        public int               MaxTxPacketsInDevice;
        public int               MaxTxFragmentsPerPacket;
        public int               MaxRxPacketsInDevice;
        public int               MaxRxFragmentsPerPacket;
    }

    public enum FromDeviceFlags : ushort
    {
        TransmitSuccess  = 0x001,
        TransmitError    = 0x002,
        ReceiveSuccess   = 0x004,
        ReceiveError     = 0x008,
        BadIp4Checksum   = 0x010,
        BadUdp4Checksum  = 0x020,
        BadTcp4Checksum  = 0x040,
        GoodUdp4Checksum = 0x080,
        GoodTcp4Checksum = 0x100,
    };

    public enum ToDeviceFlags : ushort
    {
        RequestIp4Checksum  = 1,
        RequestUdp4Checksum = 2,
        RequestTcp4Checksum = 4,
    };

    public class Packet
    {
        private PacketFragment[] fragments;
        private ToDeviceFlags   toDeviceFlags;
        private FromDeviceFlags fromDeviceFlags;

        public Packet(int fragments)
        {
            this.toDeviceFlags   = 0;
            this.fromDeviceFlags = 0;

            this.fragments = new PacketFragment[fragments];
            for (int i = 0; i < fragments; i++) {
                this.fragments[i] = new PacketFragment();
            }
        }

        public Packet(Bytes packetBytes)
            : this(1)
        {
                this.fragments[0].Set(packetBytes, 0, packetBytes.Length);
        }

        public ToDeviceFlags ToDeviceFlags
        {
            get { return toDeviceFlags; }
            set { toDeviceFlags = value; }
        }

        public FromDeviceFlags FromDeviceFlags
        {
            get { return fromDeviceFlags; }
            set { fromDeviceFlags = value; }
        }

        public int GetLength()
        {
            int total = 0;
                for (int i = 0; i < this.fragments.Length; i++) {
                        total += this.fragments[i].Length;
                }
            return total;
        }

        public byte[] ToByteArray()
        {
            byte[] buffer = new byte[this.GetLength()];
            this.ToByteArray(buffer);
            return buffer;
        }

        public void ToByteArray(byte[] buffer)
        {
                int done = 0;
                for (int i = 0; i < this.FragmentCount; i++) {
                        done += this.fragments[i].Copy(buffer, done);
                }
        }

        public void CopyToBytes(Bytes bytes)
        {
                int done = 0;
                for (int i = 0; i < this.FragmentCount; i++) {
                    VTable.Assert(done + this.fragments[i].Length <= bytes.Length);
                    done += this.fragments[i].Copy(bytes.Array, bytes.Start + done);
                }
        }

        public void Dispose()
        {
        }

        //
        public int FragmentCount
        {
            get {
                    return this.fragments.Length;
            }
        }

/*
        //
        public void GetFragmentRange(int         fragment,
                                     out UIntPtr virtualAddr,
                                     out int     lengthBytes)
        {
                    this.fragments[fragment].GetFragmentRange(out virtualAddr,
                                                              out lengthBytes);
        }

        public UIntPtr GetFragmentVirtualAddress(int fragment)
        {
            UIntPtr virtualAddress;
            int     length;
            GetFragmentRange(fragment, out virtualAddress, out length);
            return virtualAddress;
        }
*/

        public int GetFragmentLength(int fragment)
        {
                    return this.fragments[fragment].Length;
        }

        public void SetFragmentLength(int fragment, int length)
        {
                    this.fragments[fragment].Length = length;
        }

        public void UnsetFragmentLength(int fragment)
        {
                    this.fragments[fragment].Length =
                        this.fragments[fragment].Capacity;
        }

        public void UnsetFragmentLengths()
        {
                for (int i = 0; i < this.FragmentCount; i++) {
                    UnsetFragmentLength(i);
                }
        }

        public void SetFragment(int fragment,
                                Bytes buffer)
        {
            SetFragment(fragment, buffer.Array, buffer.Start, buffer.Length);
        }

        public void SetFragment(int fragment,
                                byte [] buffer)
        {
            SetFragment(fragment, buffer, 0, buffer.Length);
        }

        public Bytes ReleaseFragment(int fragment)
            //requires fragment >=0  && fragment < this.FragmentCount;
        {
                    return this.fragments[fragment].ReleaseFragment();
        }

        public void SetFragment(int      fragment,
                                byte [] buffer,
                                int      offset,
                                int      length)
        {
                    this.fragments[fragment].Set(buffer, offset, length);
        }

/*
        public void SetFragment(int fragment,
                                IoMemory region,
                                UIntPtr offset,
                                UIntPtr length)
        {
                    this.fragments[fragment].Set(region, offset, length);
        }
*/

        public void AppendToFragment(int fragment, byte value)
        {
                    this.fragments[fragment].Append(value);
        }
    }

    public class PacketFifo
    {
        private Packet[] packets;
        private int head;
        private int length;

        public PacketFifo(int capacity)
        {
            this.packets = new Packet [capacity];
            this.head   = 0;
            this.length = 0;
        }

        public int Capacity
        {
            get { { return this.packets.Length; } }
        }

        public int Count
        {
            get { { return this.length; } }
        }

        public void Push(Packet p)
        {
            {
                if (this.length == this.Capacity) {
                    DebugStub.Print("ACK! pushing onto full packetfifo\n");
                    throw new Exception();
                }
                int index = this.head;
                if (this.packets[index] != null) {
                    DebugStub.Print("ACK! non-empty space to push packet?\n");
                    throw new Exception();
                }

                    this.packets[index] = p;
                this.head = (this.head + 1) % this.Capacity;
                this.length++;
            }
        }

        public void Push(PacketFifo donor, int count)
        {
            count = Math.Min(donor.Count, count);
            while (count-- > 0) {
                this.Push(donor.Pop());
            }
        }

        public void Push(PacketFifo donor)
        {
            Push(donor, donor.Count);
        }

        public Packet Pop()
        {
            {
                if (this.length < 1) {
                    DebugStub.Print("ACK! packetfifo empty??\n");
                    throw new Exception();
                }
                Packet packet;
                int index = (this.Capacity + this.head - this.length) % this.Capacity;

                if (index > packets.Length || index < 0) {
                    DebugStub.Print("ACK index {0}\n", packets.Length);
                    DebugStub.Print("ACK plength {0}\n", packets.Length);
                    DebugStub.Print("ACK head {0}\n", this.head);
                    DebugStub.Print("ACK length {0}\n", this.length);
                    DebugStub.Print("ACK capacity {0}\n", this.Capacity);
                    throw new Exception();
                }
                    packet = packets[index];
                    this.packets[index] = null;
                this.length--;
                return packet;
            }
        }
    }

    public class PacketFragment
    {
        Bytes data;
        int  start;  // start position of live data in fragment
        int  length; // end position of live data in fragment

        public void Set(Bytes buffer, int bufferStart, int bufferBytes)
        {
            VTable.Assert(bufferStart + bufferBytes <= buffer.Length);
            Set(buffer.Array, buffer.Start + bufferStart, bufferBytes);
        }

        public void Set(byte[] buffer, int bufferStart, int bufferBytes)
        {
            {
                if (this.data == null || this.data.Length < bufferBytes) {
                    this.data = new Bytes(new byte[bufferBytes]);
                }
                this.start  = 0;
                this.length = bufferBytes;
                Bitter.FromByteArray(this.data, 0, bufferBytes,
                                     buffer, bufferStart);
            }
        }

        public Bytes ReleaseFragment()
        {
                VTable.Assert(this.data != null);
                Bytes result = this.data;
                this.data = null;
                this.start = 0;
                this.length = 0;
                return result;
        }

/*
        public void Set(IoMemory region, UIntPtr offset, UIntPtr length)
        {
            {
                this.start  = 0;
                this.length = (int)length.ToUInt32();
                Bitter.FromIoMemory(this.data, this.start, this.length,
                                    region, (int)offset.ToUInt32());
            }
        }
*/

        public int Length
        {
            get { { return this.length; } }
            set {
                {
                    this.length = value;
                }
            }
        }

        //
        public int Capacity
        {
            get {
                {
                    return this.data == null ? 0 : this.data.Length;
                }
            }
        }

        //
        internal int Start
        {
            get { { return this.start; } }
        }

        //
        public bool HasData
        {
            get { { return this.data != null; } }
        }

        public void TrimHead(int bytesToTrim)
        {
            {
                this.start  += bytesToTrim;
                this.length -= bytesToTrim;
            }
        }

        public void TrimTail(int bytesToTrim)
        {
            {
                this.length -= bytesToTrim;
            }
        }

        public void Untrim()
        {
            {
                this.start = 0;
                this.length = this.Capacity;
            }
        }

/*
        public void GetFragmentRange(out UIntPtr virtualAddr,
                                     out int lengthBytes)
        {
            {
                if (this.data != null) {
                    virtualAddr = Bitter.ToAddress(this.data, this.start);
                    lengthBytes = this.length;
                }
                else {
                    virtualAddr = UIntPtr.Zero;
                    lengthBytes = 0;
                }
            }
        }
*/

        public int Copy(byte[] destination, int offset)
        {
            {
                if (this.data != null) {
                    Bitter.ToByteArray(this.data, this.start, this.length,
                                       destination, offset);
                    return this.length;
                }
                else {
                    return 0;
                }
            }
        }

        public void Append(byte value)
        {
            {
                this.data[this.start + this.length] = value;
                this.length++;
            }
        }

        public void Dispose()
        {
            this.data = null;
        }
    }

}
