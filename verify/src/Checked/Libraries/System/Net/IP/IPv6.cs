///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Text;

namespace System.Net.IP
{
    /// <summary>
    /// IPv6 Address Structure.
    /// </summary>
    [ CLSCompliant(false) ]
    public class IPv6 : IComparable
    {
        private uint u0, u1, u2, u3;

        /// <summary>
        /// The number of bytes in an IPv6 address.
        /// </summary>
        public const int Length = 16;

        /// <summary>
        /// The number of bits in an IPv6 address.
        /// </summary>
        public const int BitCount = 128;

        /// <summary>
        /// Constructor.
        /// </summary>
        /// <param name="q0">The most significant 32-bits in
        /// host order.</param>
        /// <param name="q1">The next significant 32-bits in
        /// host order.</param>
        /// <param name="q2">The next significant 32-bits in
        /// host order.</param>
        /// <param name="q3">The least significant 32-bits in
        /// host order.</param>
        public IPv6(uint q0, uint q1, uint q2, uint q3)
        {
            u0 = q0;
            u1 = q1;
            u2 = q2;
            u3 = q3;
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
        /// InterNetwork6</exception>
        public IPv6(IPAddress ipa)
        {
            if (ipa == null) {
                throw new ArgumentNullException();
            }

            byte [] data = ipa.GetAddressBytes();
            if (data.Length != Length) {
                throw new ArgumentException();
            }
            u0 = (uint)((data[0] << 24) | (data[1] << 16) |
                        (data[2] << 8)  | (data[3]));
            u1 = (uint)((data[4] << 24) | (data[5] << 16) |
                        (data[6] << 8)  | (data[7]));
            u2 = (uint)((data[8] << 24) | (data[9] << 16) |
                        (data[10] << 8)  | (data[11]));
            u3 = (uint)((data[12] << 24) | (data[13] << 16) |
                        (data[14] << 8)  | (data[15]));
        }
#endif // HAVE_SYSTEM_NET_IPADDRESS

        /// <summary>
        /// Provide a copy of the <c>IPv6</c> address as an array of bytes.
        /// </summary>
        /// <returns>Array of bytes, ordered MSB to LSB.</returns>
        public byte[] GetAddressBytes()
        {
            return new byte[Length] {
                (byte)(u0 >> 24), (byte)(u0 >> 16),
                (byte)(u0 >>  8), (byte)(u0),
                (byte)(u1 >> 24), (byte)(u1 >> 16),
                (byte)(u1 >>  8), (byte)(u1),
                (byte)(u2 >> 24), (byte)(u2 >> 16),
                (byte)(u2 >>  8), (byte)(u2),
                (byte)(u3 >> 24), (byte)(u3 >> 16),
                (byte)(u3 >>  8), (byte)(u3)
            };
        }

        /// <summary>
        /// Create an IPv6 address representing a netmask.
        /// </summary>
        /// <param name="maskLength"></param>
        /// <returns>An IPv6 instance.</returns>
        /// <exception cref="ArgumentException">Thrown if maskLength is
        /// outside of the range [0,128].</exception>
        public static IPv6 NetMask(int maskLength)
        {
            if ((maskLength > BitCount) || (maskLength < 0)) {
                throw new
                    ArgumentException("Mask length greater than possible.");
            }
            return IPv6.AllOnes << (BitCount - maskLength);
        }

        /// <summary>
        /// Create an IPv6 address representing an IPv4 node that is only
        /// IPv4 capable.
        /// </summary>
        public static IPv6 CreateIPv4OnlyNodeAddress(IPv4 a)
        {
            return new IPv6(0, 0, 0xffff, (uint)a);
        }

        /// <summary>
        /// Create an IPv6 address representing an IPv4 node is IPv4
        /// and IPv6 capable.
        /// </summary>
        public static IPv6 CreateIPv4NodeAddress(IPv4 a)
        {
            return new IPv6(0, 0, 0x0, (uint)a);
        }

        /// <summary>
        /// Create an IPv6 address from bytes in an array.  The bytes
        /// are assumed to be in the order of MSB to LSB.
        /// </summary>
        /// <param name="data">Byte array to read address from.</param>
        /// <param name="offset">Offset in bytes of starting point.</param>
        /// <exception cref="ArgumentNullException">Thrown if the array
        /// is null.</exception>
        /// <exception cref="ArgumentException">Thrown if there are less
        /// than 16 bytes from the offset to the end of the array.</exception>
        public static IPv6 ParseBytes(byte [] data, int offset)
        {
            if (data == null) {
                throw new ArgumentNullException();
            }
            if (data.Length - offset < Length) {
                throw new ArgumentException("Byte array length not 16.");
            }
            return new IPv6((uint)((data[offset + 0] << 24) |
                                   (data[offset + 1] << 16) |
                                   (data[offset + 2] << 8)  |
                                   (data[offset + 3])),
                            (uint)((data[offset + 4] << 24) |
                                   (data[offset + 5] << 16) |
                                   (data[offset + 6] << 8)  |
                                   (data[offset + 7])),
                            (uint)((data[offset + 8] << 24) |
                                   (data[offset + 9] << 16) |
                                   (data[offset + 10] << 8) |
                                   (data[offset + 11])),
                            (uint)((data[offset + 12] << 24) |
                                   (data[offset + 13] << 16) |
                                   (data[offset + 14] << 8)  |
                                   (data[offset + 15]))
                            );
        }

        /// <summary>
        /// Create an IPv6 address from bytes in an array.
        /// </summary>
        /// <exception cref="ArgumentNullException">Thrown if the array
        /// is null.</exception>
        /// <exception cref="ArgumentException">Thrown if there are less
        /// than 16 bytes in the array.</exception>
        public static IPv6 ParseBytes(byte [] data)
        {
            return ParseBytes(data, 0);
        }

        /// <summary>
        /// Converts characters in a range to parts of an IPv6 address.
        /// <param name="ipString">Input string.</param>
        /// <param name="start">Start position in <c>ipString</c></param>
        /// <param name="end">End position in <c>ipString</c></param>
        /// <param name="maxValues">The maximum number of 16bit address
        ///   components to accept.</param>
        /// <param name="values">Array to receive 16bit address components.
        /// </param>
        /// </summary>
        private static int Parse(string ipString, int start, int end,
                                 int maxValues, ref ushort[] values)
        {
            const string hex = "00112233445566778899aAbBcCdDeEfF";

            int valueIndex = 0;
            int digits = 0;

            for (int i = start; i < end; i++) {
                int n = hex.IndexOf(ipString[i]);
                digits ++;
                if (n >= 0) {
                    if (valueIndex == maxValues || digits > 4) {
                        // About to access value beyond specified range
                        throw new FormatException();
                    }
                    uint v = values[valueIndex];
                    v = v * 16 + (uint)(n / 2);
                    if (v > 0xffffu) {
                        throw new FormatException();
                    }
                    values[valueIndex] = (ushort)v;
                }
                else if (ipString[i] == ':') {
                    // Reached Separator or end
                    valueIndex++;
                    digits = 0;
                }
                else {
                    // Invalid Character
                    throw new FormatException();
                }
            }
            return valueIndex + 1;
        }

        /// <summary>
        /// Converts an IP address string into an IPv6 instance.  This string
        /// must be a pure IPv6 representation -- IPv4 representations are not
        /// supported.
        /// </summary>
        /// <exception cref="ArgumentNullException">Thrown if
        /// <c>ipString</c> is null.</exception>
        /// <exception cref="FormatException">Thrown if
        /// <c>ipString</c> is invalid.</exception>
        public static IPv6 Parse(string ipString)
        {
            if (ipString == null)
                throw new ArgumentNullException();

            int zeroSep = ipString.IndexOf("::");

            ushort[] lhs = new ushort [8];
            int nlhs;

            if (zeroSep >= 0) {
                nlhs = Parse(ipString, 0, zeroSep, 8, ref lhs);
                ushort[] rhs = new ushort [8];
                int nrhs = Parse(ipString, zeroSep + 2, ipString.Length,
                                 8 - nlhs, ref rhs);
                if (nrhs + nlhs > 8) {
                    throw new FormatException("Too many address components");
                }
                for (int i = 0; i < nrhs; i++) {
                    lhs[8 - nrhs + i] = rhs[i];
                }
            }
            else {
                nlhs = Parse(ipString, 0, ipString.Length, 8, ref lhs);
            }

            return new IPv6( ((uint)lhs[0] << 16) | ((uint)lhs[1]),
                             ((uint)lhs[2] << 16) | ((uint)lhs[3]),
                             ((uint)lhs[4] << 16) | ((uint)lhs[5]),
                             ((uint)lhs[6] << 16) | ((uint)lhs[7])
                             );
        }

        /// <summary>
        /// Converts an IP address string into an IPv6 instance.
        /// </summary>
        /// <exception cref="ArgumentNullException">Thrown if
        /// <c>ipString</c> is null.</exception>
        /// <returns> <c>true</c> on success, <c>false</c> on failure.</returns>
        public static bool Parse(string ipString, out IPv6 address)
        {
            try {
                address = Parse(ipString);
            }
            catch (FormatException) {
                address = IPv6.Zero;
                return false;
            }
            return true;
        }

        /// <summary>
        /// Writes network-order byte representation of IPv6 address
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
            buffer[outputOffset + 0] = (byte)(u0 >> 24);
            buffer[outputOffset + 1] = (byte)(u0 >> 16);
            buffer[outputOffset + 2] = (byte)(u0 >> 8);
            buffer[outputOffset + 3] = (byte)(u0);

            buffer[outputOffset + 4] = (byte)(u1 >> 24);
            buffer[outputOffset + 5] = (byte)(u1 >> 16);
            buffer[outputOffset + 6] = (byte)(u1 >> 8);
            buffer[outputOffset + 7] = (byte)(u1);

            buffer[outputOffset + 8]  = (byte)(u2 >> 24);
            buffer[outputOffset + 9]  = (byte)(u2 >> 16);
            buffer[outputOffset + 10] = (byte)(u2 >> 8);
            buffer[outputOffset + 11] = (byte)(u2);

            buffer[outputOffset + 12] = (byte)(u3 >> 24);
            buffer[outputOffset + 13] = (byte)(u3 >> 16);
            buffer[outputOffset + 14] = (byte)(u3 >> 8);
            buffer[outputOffset + 15] = (byte)(u3);

            return Length;
        }

        /// <summary>
        /// The less-than operator for two IPv6 addresses.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the 128-bit number representing the <c>lhs</c>
        /// is less than <c>rhs</c>.</returns>
        public static bool operator < (IPv6 lhs, IPv6 rhs)
        {
            if (lhs.u0 != rhs.u0)
                return lhs.u0 < rhs.u0;
            if (lhs.u1 != rhs.u1)
                return lhs.u1 < rhs.u1;
            if (lhs.u2 != rhs.u2)
                return lhs.u2 < rhs.u2;
            return lhs.u3 < rhs.u3;
        }

        /// <summary>
        /// The less-than-or-equal-to operator for two IPv6 addresses.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the 128-bit number representing the <c>lhs</c>
        /// is less than or equal to <c>rhs</c>.</returns>
        public static bool operator <= (IPv6 lhs, IPv6 rhs)
        {
            if (rhs.u0 > lhs.u0 || rhs.u1 > lhs.u1 || rhs.u2 > lhs.u2)
                return false;

            return lhs.u3 <= rhs.u3;
        }

        /// <summary>
        /// The greater-than operator for two IPv6 addresses.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the 128-bit number representing the <c>lhs</c>
        /// is greater than <c>rhs</c>.</returns>
        public static bool operator > (IPv6 lhs, IPv6 rhs)
        {
            if (lhs.u0 != rhs.u0)
                return lhs.u0 > rhs.u0;
            if (lhs.u1 != rhs.u1)
                return lhs.u1 > rhs.u1;
            if (lhs.u2 != rhs.u2)
                return lhs.u2 > rhs.u2;
            return lhs.u3 > rhs.u3;
        }

        /// <summary>
        /// The greater-than-or-equal-to operator for two IPv6 addresses.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the 128-bit number representing the <c>lhs</c>
        /// is greater than or equal to <c>rhs</c>.</returns>
        public static bool operator >= (IPv6 lhs, IPv6 rhs)
        {
            if (lhs.u0 < rhs.u0 || lhs.u1 < rhs.u1 || lhs.u2 < rhs.u2)
                return false;

            return lhs.u3 >= rhs.u3;
        }

        /// <summary>
        /// Equals operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the addresses represented by <c>lhs</c> and
        /// <c>rhs</c> are the same.</returns>
        public static bool operator == (IPv6 lhs, IPv6 rhs)
        {
            return ((lhs.u0 == rhs.u0) && (lhs.u1 == rhs.u1) &&
                    (lhs.u2 == rhs.u2) && (lhs.u3 == rhs.u3));
        }

        /// <summary>
        /// Not-equals operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>True if the addresses represented by <c>lhs</c> and
        /// <c>rhs</c> are different.</returns>
        public static bool operator != (IPv6 lhs, IPv6 rhs)
        {
            return ((lhs.u0 != rhs.u0) || (lhs.u1 != rhs.u1) ||
                    (lhs.u2 != rhs.u2) || (lhs.u3 != rhs.u3));
        }

        /// <summary>
        /// Bit-wise AND operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>An IPv6 instance.</returns>
        public static IPv6 operator & (IPv6 lhs, IPv6 rhs)
        {
            return new IPv6(lhs.u0 & rhs.u0, lhs.u1 & rhs.u1,
                            lhs.u2 & rhs.u2, lhs.u3 & rhs.u3);
        }

        /// <summary>
        /// Bit-wise OR operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>An IPv6 instance.</returns>
        public static IPv6 operator | (IPv6 lhs, IPv6 rhs)
        {
            return new IPv6(lhs.u0 | rhs.u0, lhs.u1 | rhs.u1,
                            lhs.u2 | rhs.u2, lhs.u3 | rhs.u3);
        }

        /// <summary>
        /// Bit-wise XOR operator.
        /// </summary>
        /// <param name="lhs"></param>
        /// <param name="rhs"></param>
        /// <returns>An IPv6 instance.</returns>
        public static IPv6 operator ^ (IPv6 lhs, IPv6 rhs)
        {
            return new IPv6(lhs.u0 ^ rhs.u0, lhs.u1 ^ rhs.u1,
                            lhs.u2 ^ rhs.u2, lhs.u3 ^ rhs.u3);
        }

        /// <summary>
        /// Bit-wise NOT operator.
        /// </summary>
        /// <param name="ipv6"></param>
        /// <returns>An IPv6 instance.</returns>
        public static IPv6 operator ~ (IPv6 ipv6)
        {
            return new IPv6(~ipv6.u0, ~ipv6.u1, ~ipv6.u2, ~ipv6.u3);
        }

        /// <summary>
        /// Increment IPv6 address.
        /// </summary>
        /// <param name="ipv6"></param>
        /// <returns>An IPv6 instance.</returns>
        public static IPv6 operator ++ (IPv6 ipv6)
        {
            uint u3 = ipv6.u3 + 1;
            if (u3 > ipv6.u3)
                return new IPv6(ipv6.u0, ipv6.u1, ipv6.u2, u3);
            uint u2 = ipv6.u2 + 1;
            if (u2 > ipv6.u2)
                return new IPv6(ipv6.u0, ipv6.u1, u2, u3);
            uint u1 = ipv6.u1 + 1;
            if (u1 > ipv6.u1)
                return new IPv6(ipv6.u0, u1, u2, u3);
            uint u0 = ipv6.u0 + 1;
            return new IPv6(u0, u1, u2, u3);
        }

        /// <summary>
        /// Decrement IPv6 address.
        /// </summary>
        /// <param name="ipv6"></param>
        /// <returns>An IPv6 instance.</returns>
        public static IPv6 operator -- (IPv6 ipv6)
        {
            uint u3 = ipv6.u3 - 1;
            if (u3 < ipv6.u3)
                return new IPv6(ipv6.u0, ipv6.u1, ipv6.u2, u3);
            uint u2 = ipv6.u2 - 1;
            if (u2 < ipv6.u2)
                return new IPv6(ipv6.u0, ipv6.u1, u2, u3);
            uint u1 = ipv6.u1 - 1;
            if (u1 < ipv6.u1)
                return new IPv6(ipv6.u0, u1, u2, u3);
            uint u0 = ipv6.u0 - 1;
            return new IPv6(u0, u1, u2, u3);
        }

        /// <summary>
        /// Right-shift operator.
        /// </summary>
        /// <param name="addr">Address to be shifted.</param>
        /// <param name="n">Number of bits to shift-by.</param>
        /// <returns>An IPv6 address.</returns>
        public static IPv6 operator >> (IPv6 addr, int n)
        {
            switch (n >> 5) {
                case 3:
                    addr.u3 = addr.u0;
                    addr.u0 = addr.u1 = addr.u2 = 0;
                    break;
                case 2:
                    addr.u3 = addr.u1;
                    addr.u2 = addr.u0;
                    addr.u0 = addr.u1 = 0;
                    break;
                case 1:
                    addr.u3 = addr.u2;
                    addr.u2 = addr.u1;
                    addr.u1 = addr.u0;
                    addr.u0 = 0;
                    break;
                case 0:
                    break;
                default:
                    if (n < 0)
                        return addr << (-n);
                    return Zero;
            }

            n = n & 0x1f;
            if (n != 0) {
                int m = 32 - n;
                addr.u3 = (addr.u3 >> n) | (addr.u2 << m);
                addr.u2 = (addr.u2 >> n) | (addr.u1 << m);
                addr.u1 = (addr.u1 >> n) | (addr.u0 << m);
                addr.u0 = (addr.u0 >> n);
            }
            return new IPv6(addr.u0, addr.u1, addr.u2, addr.u3);
        }

        /// <summary>
        /// Left-shift operator.
        /// </summary>
        /// <param name="addr">Address to be shifted.</param>
        /// <param name="n">Number of bits to shift-by.</param>
        /// <returns>An IPv6 address.</returns>
        public static IPv6 operator << (IPv6 addr, int n)
        {
            switch (n >> 5) {
                case 3:
                    addr.u0 = addr.u3;
                    addr.u1 = addr.u2 = addr.u3 = 0;
                    break;
                case 2:
                    addr.u0 = addr.u2;
                    addr.u1 = addr.u3;
                    addr.u2 = addr.u3 = 0;
                    break;
                case 1:
                    addr.u0 = addr.u1;
                    addr.u1 = addr.u2;
                    addr.u2 = addr.u3;
                    addr.u3 = 0;
                    break;
                case 0:
                    break;
                default:
                    if (n < 0)
                        return addr >> (-n);
                    return Zero;
            }
            n = n & 0x1f;
            if (n != 0) {
                int m = 32 - n;
                addr.u0 = (addr.u0 << n) | (addr.u1 >> m);
                addr.u1 = (addr.u1 << n) | (addr.u2 >> m);
                addr.u2 = (addr.u2 << n) | (addr.u3 >> m);
                addr.u3 = (addr.u3 << n);
            }
            return new IPv6(addr.u0, addr.u1, addr.u2, addr.u3);
        }

        /// <summary>
        /// Get a single bit from an IPv6 address.
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

            int dwordIndex  = bitIndex / 32;
            uint mask = 1u << (31 - (bitIndex & 31));

            switch (dwordIndex) {
                case 0:
                    return (u0 & mask) == mask;
                case 1:
                    return (u1 & mask) == mask;
                case 2:
                    return (u2 & mask) == mask;
            }
            return (u3 & mask) == mask;
        }

        /// <summary>
        /// Get the mask length from an IPv6 address representing a netmask.
        /// </summary>
        /// <param name="netmask"></param>
        public static int GetMaskLength(IPv6 netmask)
        {
            int i = 0;
            while (netmask.GetBit(i) == true) {
                i++;
            }
            return i;
        }

#if HAVE_SYSTEM_NET_IPADDRESS
        /// <summary>
        /// Cast <c>IPv6</c> instance into a <c>System.Net.IPAddress</c>
        /// </summary>
        /// <param name="ipv6"></param>
        /// <returns>An <c>IPAddress</c> instance.</returns>
        public static explicit operator IPAddress(IPv6 ipv6)
        {
            return new IPAddress(ipv6.GetAddressBytes());
        }
#endif // HAVE_SYSTEM_NET_IPADDRESS

        /// <summary>
        /// Determines whether two Object instances are equal.
        /// </summary>
        /// <param name="o">Object to be compared to.</param>
        /// <returns>True if <c>o</c> is an IPv6 address and numerically
        /// the same as instance.</returns>
        public override bool Equals(object o)
        {
            if (o is IPv6) {
                IPv6 ipo = (IPv6)o;
                return this == ipo;
            }
            return false;
        }

        /// <summary>
        /// Compute numeric hash of IPv6 instance.  Value is
        /// suitable for use in hashing algorithms and data
        /// structures like a hash table.
        /// </summary>
        public override int GetHashCode()
        {
            return (int)(u0 ^ u1 ^ u2 ^ u3);
        }

        /// <summary>
        /// Determine if IPv6 address represents an IPv4 capable node.
        /// </summary>
        public bool RepresentsIPv4Address()
        {
            // RFC1884 Section 2.4.4
            return (u0 == 0) && (u1 == 0) && ((u2 >> 16) == 0) &&
                ((u2 & 0xffff) == 0xffff ||
                 ((u2 & 0xffff) == 0) && (u3 != 0));
        }

        /// <summary>
        /// Determine if IPv6 address represents IPv4 only capable node.
        /// </summary>
        public bool RepresentsIPv4OnlyAddress()
        {
            // RFC1884 Section 2.4.4
            return (u0 == 0) && (u1 == 0) && ((u2 >> 16) == 0) &&
                ((u2 & 0xffff) == 0xffff);
        }

        /// <summary>
        /// Determine if IPv6 address represents a link-local address.
        /// </summary>
        public bool IsLinkLocalAddress()
        {
            return (u0 & 0xffc00000) == 0xfe800000;     // RFC1884 Section 2.3
        }

        /// <summary>
        /// Determine if IPv6 address represents a site-local address.
        /// </summary>
        public bool IsSiteLocalAddress()
        {
            return (u0 & 0xffc00000) == 0xfec00000;     // RFC1884 Section 2.3
        }

        /// <summary>
        /// Indicates whether instance represents a native IPv6
        /// loopback address.
        /// </summary>
        /// <returns>True if instance represents a loopback
        /// address.</returns>
        public bool IsLoopback()
        {
            return (this == IPv6.Loopback);
        }

        /// <summary>
        /// Determine if IPv6 address represents a native IPv6
        /// multicast address.
        /// </summary>
        public bool IsMulticast()
        {
            return ((u0 & 0xff000000) == 0xff000000);
        }

        /// <summary>
        /// Extract embedded IPv4 address.
        /// </summary>
        /// <returns>Returns IPv4 address on success and <c>IPv4.Any</c>
        /// if address does not represent an IPv4 address.</returns>
        public IPv4 GetIPv4Address()
        {
            if (u0 == 0 && u1 == 0 && (u2 == 0 || u2 == 0xffff)) {
                return new IPv4(u3);
            }
            return IPv4.Any;
        }

        private string NativeStringRepresentation()
        {
            // Copy address into array of ushorts to make it easy to find
            // region a region of zeroes per RFC 1884.  We only find the
            // first region rather than attempt to find the longest.
            ushort [] words = new ushort [8] {
                (ushort)(u0 >> 16), (ushort)(u0 & 0xffffU),
                (ushort)(u1 >> 16), (ushort)(u1 & 0xffffU),
                (ushort)(u2 >> 16), (ushort)(u2 & 0xffffU),
                (ushort)(u3 >> 16), (ushort)(u3 & 0xffffU)
            };

            // Find start of the zero block
            int zStart;
            for (zStart = 0; zStart < words.Length; zStart++) {
                if (words[zStart] == 0)
                    break;
            }

            // Find the end of the zero block
            int zEnd;
            for (zEnd = zStart + 1; zEnd < words.Length; zEnd++) {
                if (words[zEnd] != 0)
                    break;
            }

            // Max size is 8 * 4 hexdigits + 7 * 1 digit separator
            StringBuilder sb = new StringBuilder(null, 8 * 4 + 7 * 1);
            for (int i = 0; i < zStart; i++) {
                if (i > 0)
                    sb.AppendFormat(":{0:x}", words[i]);
                else
                    sb.AppendFormat("{0:x}", words[i]);
            }

            if (zStart == words.Length)
                return sb.ToString();

            sb.Append("::");
            for (int i = zEnd; i < words.Length; i++) {
                if (i > zEnd)
                    sb.AppendFormat(":{0:x}", words[i]);
                else
                    sb.AppendFormat("{0:x}", words[i]);
            }

            return sb.ToString();
        }

        /// <summary>
        /// Returns a string representing IPv6 instance.
        /// </summary>
        public override string ToString()
        {
#if NOTYET
            if (RepresentsIPv4OnlyAddress() == true) {
                return String.Format("::ffff:{0}.{1}.{2}.{3}", u3 >> 24,
                                     (u3 >> 16) & 0xff, (u3 >> 8) & 0xff,
                                     u3 & 0xff);
            }
            else if (RepresentsIPv4Address() == true) {
                return String.Format("::{0}.{1}.{2}.{3}", u3 >> 24,
                                     (u3 >> 16) & 0xff, (u3 >> 8) & 0xff,
                                     u3 & 0xff);
            }
#endif // NOTYET
            return NativeStringRepresentation();
        }

        public int CompareTo(object other)
        {
            if (other == null)
                return 1;
            if (other is IPv6) {
                IPv6 value = (IPv6) other;
                if (this < value) return -1;
                if (this > value) return + 1;
                return 0;
            }
            throw new ArgumentException ("Arg_MustBeIPv6");
        }


        /// <summary>
        /// IPv6 address representing unspecified address.
        /// </summary>
        public static readonly IPv6 Any = new IPv6(0U, 0U, 0U, 0U);

        /// <summary>
        /// IPv6 address with all bits set to zero.
        /// </summary>
        public static readonly IPv6 Zero = new IPv6(0U, 0U, 0U, 0U);

        /// <summary>
        /// IPv6 loopback address.
        /// </summary>
        public static readonly IPv6 Loopback = new IPv6(0U, 0U, 0U, 1U);

        /// <summary>
        /// IPv6 address with all bits set to one.
        /// </summary>
        public static readonly IPv6 AllOnes = new IPv6(~0U, ~0U, ~0U, ~0U);
    }
} // namespace System.Net.IP
