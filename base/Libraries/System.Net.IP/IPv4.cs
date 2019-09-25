///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: IPv4.cs
//

using System;

namespace System.Net.IP
{
    /// <summary>
    /// IPv4 Address Structure.
    /// </summary>
    [ CLSCompliant(false) ]
    public struct IPv4 : IComparable
    {
        private uint addr;  // Host order

        /// <summary>
        /// The number of bytes in an IPv4 address.
        /// </summary>
        public const int Length = 4;

        /// <summary>
        /// The number of bits in a IPv4 address.
        /// </summary>
        public const int BitCount = 32;

        /// <summary>
        /// Constructor.
        /// </summary>
        /// <param name="hostOrderAddress">A 32-bit value representing an
        /// IPv4 address in host-order.</param>
        public IPv4(uint hostOrderAddress)
        {
            addr = hostOrderAddress;
        }

        /// <summary>
        /// Copy-constructor
        /// </summary>
        /// <param name="IPv4 other">Another IPv4 instance</param>
        public IPv4(IPv4 other)
        {
            addr = other.addr;
        }

#if HAVE_SYSTEM_NET_IPADDRESS
        /// <summary>
        /// Constructor
        /// </summary>
        /// <param name="ipa">An instance of the
        /// System.Net.IPAddress class.</param>
        /// <exception cref="ArgumentNullException">Thrown when
        /// argument is null.</exception>
        /// <exception cref="ArgumentException">Thrown when
        /// AddressFamily of <c>ipa</c>is other than
        /// InterNetwork</exception>
        public IPv4(IPAddress ipa)
        {
            if (ipa == null) {
                throw new ArgumentNullException();
            }

            byte [] quad = ipa.GetAddressBytes();
            if (quad.Length != Length) {
                throw new ArgumentException();
            }
            addr =(uint)((quad[0] << 24) | (quad[1] << 16) |
                         (quad[2] << 8) | quad[3]);
}
#endif // HAVE_SYSTEM_NET_IPADDRESS

        /// <summary>
        /// Provide a copy of the <c>IPv4</c> address as an array of bytes.
        /// </summary>
        /// <returns>Array of bytes, ordered MSB to LSB.</returns>
        public byte[]! GetAddressBytes()
        {
            return new byte[Length] {
                (byte)(addr >> 24), (byte)(addr >> 16),
                (byte)(addr >>  8), (byte)(addr)
            };
        }

        /// <summary>
        /// Create an IPv4 address representing a netmask.
        /// </summary>
        /// <param name="maskLength"></param>
        /// <returns>An IPv4 instance.</returns>
        /// <exception cref="ArgumentException">Thrown if maskLength is
        /// outside of the range [0,32].</exception>
        public static IPv4 NetMask(int maskLength)
        {
            if ((maskLength > BitCount) || (maskLength < 0)) {
                throw new
                    ArgumentException("Mask length greater than possible.");
            }
            return IPv4.AllOnes << (BitCount - maskLength);
        }

        /// <summary>
        /// Create an IPv4 address from bytes in an array.  The bytes
        /// are assumed to be in the order of MSB to LSB.
        /// </summary>
        /// <param name="data">Byte array to read address from.</param>
        /// <param name="offset">Offset in bytes of starting point.</param>
        /// <exception cref="ArgumentNullException">Thrown if the array
        /// is null.</exception>
        /// <exception cref="ArgumentException">Thrown if there are less
        /// than 4 bytes from the offset to the end of the array.</exception>
        public static IPv4 ParseBytes(byte [] data, int offset)
        {
            if (data == null) {
                throw new ArgumentNullException();
            }
            if (data.Length - offset < Length) {
                throw new ArgumentException("Byte array too short.");
            }
            return new IPv4((uint)((data[offset + 0] << 24) |
                                   (data[offset + 1] << 16) |
                                   (data[offset + 2] << 8)  |
                                   (data[offset + 3]))
                            );
        }

        /// <summary>
        /// Create an IPv4 address from bytes in an array.
        /// </summary>
        /// <exception cref="ArgumentNullException">Thrown if the array
        /// is null.</exception>
        /// <exception cref="ArgumentException">Thrown if there are less
        /// than 4 bytes in the array.</exception>
        public static IPv4 ParseBytes(byte [] data)
        {
            return ParseBytes(data, 0);
        }

        private static bool ParseHexQuad(string! quad, out uint value)
        {
            const string hex = "00112233445566778899aAbBcCdDeEfF";
            value = 0;
            if (quad.Length < 3 || quad.Length > 4)
                return false;
            if ((quad[0] != '0') || (quad[1] != 'x'))
                return false;
            int u = (quad.Length == 4) ? hex.IndexOf(quad[2]) : 0;
            int l = hex.IndexOf(quad[quad.Length - 1]);
            value = (uint)(((u << 3) & 0xf0) | (l >> 1));

            return (u >= 0) && (l >= 0);
        }

        private static bool ParseOctalQuad(string! quad, out uint value)
        {
            value = 0;
            if (quad.Length < 2 || quad.Length > 4)
                return false;

            if (quad[0] != '0')
                return false;

            int result = 0;
            for (int i = 1; i < quad.Length; i++) {
                int tmp = quad[i] - '0';
                if (tmp < 0 || tmp > 7)
                    return false;
                result = result * 8 + tmp;
            }

            value = (uint)result;
            return result <= 255;
        }

        private static bool ParseDecimalQuad(string! quad, out uint value)
        {
            value = 0;

            if (quad.Length == 0 || quad.Length > 3)
                return false;

            int result = 0;
            for (int i = 0; i < quad.Length; i++) {
                int tmp = quad[i] - '0';
                if (tmp < 0 || tmp > 9)
                    return false;
                result = result * 10 + tmp;
            }
            value = (uint)result;

            return result <= 255;
        }

        private static bool ParseQuad(string! quad, out uint value)
        {
            if (ParseHexQuad(quad, out value) == true)
                return true;
            if (ParseOctalQuad(quad, out value) == true)
                return true;
            return ParseDecimalQuad(quad, out value);
        }

        /// <summary>
        /// Converts an IP address string into an IPv4 instance.
        /// </summary>
        /// <exception cref="ArgumentNullException">Thrown if
        /// <c>ipString</c> is null.</exception>
        /// <exception cref="FormatException">Thrown if
        /// <c>ipString</c> is invalid.</exception>
        public static IPv4 Parse(string ipString)
        {
            const string malformed = "Malformed address";

            if (ipString == null) {
                throw new ArgumentNullException("ipString");
            }

            string [] quads = ipString.Split('.');
            if (quads.Length == 0 || quads.Length > 4) {
                throw new FormatException(malformed);
            }

            uint address = 0;
            uint tmp = 0;
            int i;
            for (i = 0; i < quads.Length - 1; i++) {
                if (ParseQuad((!)quads[i], out tmp) == false) {
                    throw new FormatException(malformed);
                }
                address |= (tmp) << (24 - i * 8);
            }
            if (ParseQuad((!)quads[i], out tmp) == false) {
                throw new FormatException(malformed);
            }
            address |= tmp;
            return new IPv4(address);
        }

        /// <summary>
        /// Converts an IP address string into an IPv4 instance.
        /// </summary>
        /// <exception cref="ArgumentNullException">Thrown if
        /// <c>ipString</c> is null.</exception>
        /// <returns> <c>true</c> on success, <c>false</c> on failure.</returns>
        public static bool Parse(string ipString, out IPv4 address)
        {
            try {
                address = Parse(ipString);
            }
            catch (FormatException) {
                address = IPv4.Zero;
                return false;
            }
            return true;
        }

        /// <summary>
        /// Writes network-order byte representation of IPv4 address
        /// into buffer at a specified offset.
        /// </summary>
        /// <exception cref="ArgumentNullException">Thrown if <c>buffer</c>
        /// argument is null. </exception>
        /// <exception cref="ArgumentException">Thrown if there is
        /// insufficient space between <c>outputOffset</c> and the end of
        /// <c>buffer</c> to write out the IP address.</exception>
        public int CopyOut(byte[] buffer, int outputOffset)
        {
            if (buffer == null) {
                throw new ArgumentNullException();
            }
            if (buffer.Length - outputOffset < Length) {
                throw new ArgumentException("Byte array too short.");
            }
            buffer[outputOffset + 0] = (byte)(addr >> 24);
            buffer[outputOffset + 1] = (byte)(addr >> 16);
            buffer[outputOffset + 2] = (byte)(addr >> 8);
            buffer[outputOffset + 3] = (byte)(addr);
            return Length;
        }

        /// <summary>
        /// The less-than operator for two IPv4 addresses.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the 32-bit number representing the <c>lhs</c>
        /// is less than <c>rhs</c>.</returns>
        public static bool operator < (IPv4 lhs, IPv4 rhs)
        {
            return lhs.addr < rhs.addr;
        }

        /// <summary>
        /// The less-than-or-equal-to operator for two IPv4 addresses.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the 32-bit number representing the <c>lhs</c>
        /// is less than or equal to <c>rhs</c>.</returns>
        public static bool operator <= (IPv4 lhs, IPv4 rhs)
        {
            return lhs.addr <= rhs.addr;
        }

        /// <summary>
        /// The greater-than operator for two IPv4 addresses.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the 32-bit number representing the <c>lhs</c>
        /// is greater than <c>rhs</c>.</returns>
        public static bool operator > (IPv4 lhs, IPv4 rhs)
        {
            return lhs.addr > rhs.addr;
        }

        /// <summary>
        /// The greater-than-or-equal-to operator for two IPv4 addresses.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the 32-bit number representing the <c>lhs</c>
        /// is greater than or equal to <c>rhs</c>.</returns>
        public static bool operator >= (IPv4 lhs, IPv4 rhs)
        {
            return lhs.addr >= rhs.addr;
        }

        /// <summary>
        /// Equals operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the addresses represented by <c>lhs</c> and
        /// <c>rhs</c> are the same.</returns>
        public static bool operator == (IPv4 lhs, IPv4 rhs)
        {
            return lhs.addr == rhs.addr;
        }

        /// <summary>
        /// Not-equals operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the addresses represented by <c>lhs</c> and
        /// <c>rhs</c> are different.</returns>
        public static bool operator != (IPv4 lhs, IPv4 rhs)
        {
            return lhs.addr != rhs.addr;
        }

        /// <summary>
        /// Bit-wise AND operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>An IPv4 instance.</returns>
        public static IPv4 operator & (IPv4 lhs, IPv4 rhs)
        {
            return new IPv4(lhs.addr & rhs.addr);
        }

        /// <summary>
        /// Bit-wise OR operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>An IPv4 instance.</returns>
        public static IPv4 operator | (IPv4 lhs, IPv4 rhs)
        {
            return new IPv4(lhs.addr | rhs.addr);
        }

        /// <summary>
        /// Bit-wise XOR operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>An IPv4 instance.</returns>
        public static IPv4 operator ^ (IPv4 lhs, IPv4 rhs)
        {
            return new IPv4(lhs.addr ^ rhs.addr);
        }

        /// <summary>
        /// Bit-wise NOT operator.
        /// </summary>
        /// <param name="ipv4"></param>
        /// <returns>An IPv4 instance.</returns>
        public static IPv4 operator ~ (IPv4 ipv4)
        {
            return new IPv4(~ipv4.addr);
        }

        /// <summary>
        /// Increment IPv4 address.
        /// </summary>
        /// <param name="ipv4"></param>
        /// <returns>An IPv4 instance.</returns>
        public static IPv4 operator ++ (IPv4 ipv4)
        {
            return new IPv4(ipv4.addr + 1);
        }

        /// <summary>
        /// Decrement IPv4 address.
        /// </summary>
        /// <param name="ipv4"></param>
        /// <returns>An IPv4 instance.</returns>
        public static IPv4 operator -- (IPv4 ipv4)
        {
            return new IPv4(ipv4.addr - 1);
        }

        /// <summary>
        /// Right-shift operator.
        /// </summary>
        /// <param name="ipv4">Address to be shifted.</param>
        /// <param name="n">Number of bits to shift-by.</param>
        /// <returns>An IPv4 address.</returns>
        public static IPv4 operator >> (IPv4 ipv4, int n)
        {
            if (n < BitCount) {
                return new IPv4(ipv4.addr >> n);
            }
            return IPv4.Zero;
        }

        /// <summary>
        /// Left-shift operator.
        /// </summary>
        /// <param name="ipv4">Address to be shifted.</param>
        /// <param name="n">Number of bits to shift-by.</param>
        /// <returns>An IPv4 address.</returns>
        public static IPv4 operator << (IPv4 ipv4, int n)
        {
            if (n < BitCount) {
                return new IPv4(ipv4.addr << n);
            }
            return IPv4.Zero;
        }

        /// <summary>
        /// Get a single bit from an IPv4 address.
        /// </summary>
        /// <param name="bitIndex">Index of bit (ordered from msb-to-lsb)
        /// </param>
        /// <returns>Returns <c>true</c> if bit is set, false if
        /// bit is unset or <paramref name="bitIndex" /> is out
        /// of range.
        /// </returns>
        public bool GetBit(int bitIndex)
        {
            if (bitIndex < 0 || bitIndex >= BitCount) {
                return false;
            }
            uint mask = 1u << (31 - bitIndex);
            return (addr & mask) == mask;
        }

        /// <summary>
        /// Get the mask length from an IPv4 address representing a netmask.
        /// </summary>
        /// <param name="netmask"></param>
        public static int GetMaskLength(IPv4 netmask)
        {
            int i = 0;
            while (netmask.GetBit(i) == true) {
                i++;
            }
            return i;
        }

#if HAVE_SYSTEM_NET_IPADDRESS
        /// <summary>
        /// Cast <c>IPv4</c> instance into a <c>System.Net.IPAddress</c>
        /// </summary>
        /// <param name="ipv4"></param>
        /// <returns>An <c>IPAddress</c> instance.</returns>
        public static explicit operator IPAddress(IPv4 ipv4)
        {
            int netOrder = IPAddress.HostToNetworkOrder((int)ipv4.addr);
            return new IPAddress(((long)netOrder) & 0xffffffff);
        }
#endif // HAVE_SYSTEM_NET_IPADDRESS

        /// <summary>
        /// Cast <c>IPv4</c> instance into an unsigned integer.
        /// </summary>
        /// <param name="ipv4"></param>
        /// <returns>An unsigned integer.</returns>
        public static explicit operator uint(IPv4 ipAddress)
        {
            return ipAddress.addr;
        }

        /// <summary>
        /// Determines whether two Object instances are equal.
        /// </summary>
        /// <param name="other">Object to be compared to.</param>
        /// <returns>True if <c>o</c> is an IPv4 address and numerically
        /// the same as instance.</returns>
        public override bool Equals(object other)
        {
            if (other is IPv4) {
                return addr == ((IPv4)other).addr;
            }
            return false;
        }

        /// <summary>
        /// Compute numeric hash of IPv4 instance.  Value is
        /// suitable for use in hashing algorithms and data
        /// structures like a hash table.
        /// </summary>
        public override int GetHashCode()
        {
            return (int)addr;
        }

        /// <summary>
        /// Indicates whether instance represents a loopback address.
        /// </summary>
        /// <returns>True if instance represents a loopback
        /// address.</returns>
        public bool IsLoopback()
        {
            return (addr & 0xff000000) == 0x7f000000;
        }

        /// <summary>
        /// Indicates whether instance represents a multicast address.
        /// </summary>
        /// <returns>True if instance represents a multicast
        /// address.</returns>
        public bool IsMulticast()
        {
            return (addr & 0xf0000000) == 0xe0000000;
        }

        /// <summary>
        /// Returns a string representing IPv4 instance.
        /// </summary>
        public override string! ToString()
        {
            return String.Format("{0}.{1}.{2}.{3}",
                                 addr >> 24, (addr >> 16) & 0xff,
                                 (addr >> 8) & 0xff, addr & 0xff);
        }

        public int CompareTo(object other)
        {
            if (other == null)
                return 1;
            if (other is IPv4) {
                IPv4 value = (IPv4) other;
                if (this < value) return -1;
                if (this > value) return + 1;
                return 0;
            }
            throw new ArgumentException ("Arg_MustBeIPv4");
        }

        /// <summary>
        /// IPv4 address representing an unspecified host.
        /// </summary>
        public static readonly IPv4 Any = new IPv4(0U);

        /// <summary>
        /// IPv4 address with all bits set to zero.
        /// </summary>
        public static readonly IPv4 Zero = new IPv4(0U);

        /// <summary>
        /// IPv4 loopback address.
        /// </summary>
        public static readonly IPv4 Loopback = new IPv4(0x7f000001U);

        /// <summary>
        /// IPv4 broadcast address.
        /// </summary>
        public static readonly IPv4 Broadcast = new IPv4(~0U);

        /// <summary>
        /// IPv4 address with all bits set to one.
        /// </summary>
        public static readonly IPv4 AllOnes = new IPv4(~0U);
    }
} // namespace System.Net.IP
