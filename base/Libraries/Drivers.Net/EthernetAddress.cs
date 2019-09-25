///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;

namespace Drivers.Net
{
    /// <summary>
    /// Structure representing an Ethernet address.
    /// </summary>
    public struct EthernetAddress : IComparable
    {
        /// <summary>
        /// Length of an Ethernet address in bytes.
        /// </summary>
        public const int Length = 6;

        private uint    u03;    // bytes 0-3
        private ushort  u45;    // bytes 4-5

        /// <summary>
        /// Ethernet broadcast address.
        /// </summary>
        public static readonly EthernetAddress Broadcast =
            new EthernetAddress(0xff, 0xff, 0xff, 0xff, 0xff, 0xff);

        /// <summary>
        /// The all-zeros address.
        /// </summary>
        public static readonly EthernetAddress Zero =
            new EthernetAddress(0, 0, 0, 0, 0, 0);

        /// <summary>
        /// Bridge Group Address.
        ///  Reserved by IEEE 802.1D, Table 7-9, 1998 Edition:
        /// ...-00 is the Bridge Group Address, used for Spanning Tree Protocol
        /// </summary>
        public static readonly EthernetAddress Bridge =
            new EthernetAddress(0x01, 0x80, 0xC2, 0x00, 0x00, 0x00);

        /// <summary>
        /// Full Duplex PAUSE operation address.
        /// </summary>
        public static readonly EthernetAddress PAUSE =
            new EthernetAddress(0x01, 0x80, 0xC2, 0x00, 0x00, 0x01);

        /// <summary>
        /// Constructor.
        /// </summary>
        /// <param name="pa0">Most significant byte</param>
        /// <param name="pa1">Second most significant byte</param>
        /// <param name="pa2"></param>
        /// <param name="pa3"></param>
        /// <param name="pa4"></param>
        /// <param name="pa5">Least significant byte</param>
        public EthernetAddress(byte pa0, byte pa1, byte pa2,
                               byte pa3, byte pa4, byte pa5)
        {
            u03  = ((uint)pa0) << 24;
            u03 |= ((uint)pa1) << 16;
            u03 |= ((uint)pa2) << 8;
            u03 |= ((uint)pa3);
            u45  = (ushort)((int)pa4 << 8);
            u45 |= (ushort)pa5;
        }

        public EthernetAddress(byte [] addressBytes)
        {
            if (addressBytes == null) {
                throw new ArgumentNullException();
            }
            if (addressBytes.Length != Length) {
                throw new ArgumentException();
            }
            u03  = ((uint)addressBytes[0]) << 24;
            u03 |= ((uint)addressBytes[1]) << 16;
            u03 |= ((uint)addressBytes[2]) << 8;
            u03 |= ((uint)addressBytes[3]);
            u45  = (ushort)((int)addressBytes[4] << 8);
            u45 |= (ushort)addressBytes[5];
        }

        private EthernetAddress(uint u03, ushort u45)
        {
            this.u03 = u03;
            this.u45 = u45;
        }

        public EthernetAddress(EthernetAddress other)
        {
            this.u03 = other.u03;
            this.u45 = other.u45;
        }

        public static bool operator < (EthernetAddress lhs,
                                       EthernetAddress rhs)
        {
            if (lhs.u03 != rhs.u03)
                return lhs.u03 < rhs.u03;
            return lhs.u45 < rhs.u45;
        }

        public static bool operator <= (EthernetAddress lhs,
                                        EthernetAddress rhs)
        {
            if (lhs.u03 > rhs.u03)
                return false;
            return lhs.u45 <= rhs.u45;
        }

        public static bool operator > (EthernetAddress lhs,
                                       EthernetAddress rhs)
        {
            if (lhs.u03 != rhs.u03)
                return lhs.u03 > rhs.u03;
            return lhs.u45 > rhs.u45;
        }

        public static bool operator >= (EthernetAddress lhs,
                                        EthernetAddress rhs)
        {
            if (lhs.u03 < rhs.u03)
                return false;
            return lhs.u45 >= rhs.u45;
        }

        public static bool operator == (EthernetAddress lhs,
                                        EthernetAddress rhs)
        {
            return (lhs.u03 == rhs.u03) && (lhs.u45 == rhs.u45);
        }

        public static bool operator != (EthernetAddress lhs,
                                        EthernetAddress rhs)
        {
            return !(lhs == rhs);
        }

        public static EthernetAddress operator & (EthernetAddress lhs,
                                                  EthernetAddress rhs)
        {
            return new EthernetAddress(lhs.u03 & rhs.u03,
                                       (ushort) (lhs.u45 & rhs.u45));
        }

        public static EthernetAddress operator | (EthernetAddress lhs,
                                                  EthernetAddress rhs)
        {
            return new EthernetAddress(lhs.u03 | rhs.u03,
                                       (ushort) (lhs.u45 | rhs.u45));
        }

        public static EthernetAddress operator ^ (EthernetAddress lhs,
                                                  EthernetAddress rhs)
        {
            return new EthernetAddress(lhs.u03 ^ rhs.u03,
                                       (ushort) (lhs.u45 ^ rhs.u45));
        }

        public static EthernetAddress operator ~ (EthernetAddress ea)
        {
            return new EthernetAddress(~ea.u03, (ushort) (~ea.u45));
        }

        public static EthernetAddress operator ++ (EthernetAddress ea)
        {
            ushort u45 = (ushort) (ea.u45 + 1);
            if (u45 > ea.u45)
                return new EthernetAddress(ea.u03, u45);
            uint u03 = ea.u03 + 1;
            return new EthernetAddress(u03, u45);
        }

        public static EthernetAddress operator -- (EthernetAddress ea)
        {
            ushort u45 = (ushort) (ea.u45 - 1);
            if (u45 < ea.u45)
                return new EthernetAddress(ea.u03, u45);
            uint u03 = ea.u03 - 1;
            return new EthernetAddress(u03, u45);
        }

        public override bool Equals(object o)
        {
            if (o is EthernetAddress) {
                return this == (EthernetAddress) o;
            }
            return false;
        }

        public byte[]! GetAddressBytes()
        {
            return new byte[6] {
                (byte)(u03 >> 24), (byte)(u03 >> 16), (byte)(u03 >>  8),
                (byte)(u03),       (byte)(u45 >>  8), (byte)(u45)
            };
        }

        public override int GetHashCode()
        {
            return (int)u03 ^ (int)u45;
        }

        public override string! ToString()
        {
            return String.Format("{0:x2}:{1:x2}:{2:x2}:{3:x2}:{4:x2}:{5:x2}",
                                 (byte)(u03 >> 24), (byte)(u03 >> 16),
                                 (byte)(u03 >>  8), (byte)(u03),
                                 (byte)(u45 >>  8), (byte)(u45));
        }

        // returns the address with custom separator, so it can
        // be used as a filename.
        public string ToString(string separator)
        {
            return String.Format("{0:x2}{6}{1:x2}{6}{2:x2}{6}" +
                                 "{3:x2}{6}{4:x2}{6}{5:x2}",
                                 (byte)(u03 >> 24), (byte)(u03 >> 16),
                                 (byte)(u03 >>  8), (byte)(u03),
                                 (byte)(u45 >>  8), (byte)(u45),
                                 separator);
        }

        // accepts either aa:bb:cc:dd:ee:ff (widely used) or
        // aa-bb-cc-dd-ee-ff (IEEE) formats
        public static EthernetAddress Parse(string raw)
        {
            const string hexdigits = "00112233445566778899aAbBcCdDeEfF";
            char [] separators = {'-', ':'};

            if (raw == null)
                throw new ArgumentNullException();

            byte [] b = new byte[6];
            string [] tokens = raw.Split(separators);
            if (tokens.Length != 6)
                throw new FormatException();

            for (int i = 0; i < 6; i++) {
                string ti = (!)tokens[i];
                if (ti.Length != 2)
                    throw new FormatException();

                int u = hexdigits.IndexOf(ti[0]);
                int l = hexdigits.IndexOf(ti[1]);

                if ((u < 0) || (l < 0))
                    throw new FormatException();
                // Note there are 32 digits in hexdigits so we divide by 2
                u >>= 1;
                l >>= 1;

                b[i] = (byte)(((u << 4) & 0xf0) | l);
            }

            return new EthernetAddress(b);
        }

        /// <summary>
        /// Converts an string into an EthernetAddress instance.
        /// </summary>
        /// <exception cref="ArgumentNullException">Thrown if
        /// <c>macString</c> is null.</exception>
        /// <returns> <c>true</c> on success, <c>false</c> on failure.</returns>
        public static bool Parse(string macString, out EthernetAddress address)
        {
            try {
                address = Parse(macString);
            }
            catch (FormatException) {
                address = EthernetAddress.Zero;
                return false;
            }
            return true;
        }

        public static EthernetAddress ParseBytes(byte[] data, int offset)
        {
            if (data == null) {
                throw new ArgumentNullException();
            }
            if (data.Length - offset < Length) {
                throw new ArgumentException("Byte array too short.");
            }
            return new EthernetAddress(data[offset], data[offset + 1],
                                       data[offset + 2], data[offset + 3],
                                       data[offset + 4], data[offset + 5]);
        }

        public static EthernetAddress ParseBytes(byte[] data)
        {
            return new EthernetAddress(data);
        }

        public int CopyOut(byte []! buffer, int outputOffset)
        {
            buffer[outputOffset + 0] = (byte)(u03 >> 24);
            buffer[outputOffset + 1] = (byte)(u03 >> 16);
            buffer[outputOffset + 2] = (byte)(u03 >>  8);
            buffer[outputOffset + 3] = (byte)(u03);
            buffer[outputOffset + 4] = (byte)(u45 >>  8);
            buffer[outputOffset + 5] = (byte)(u45);
            return Length;
        }

        public int CompareTo(object other)
        {
            if (other == null)
                return 1;
            if (other is EthernetAddress) {
                EthernetAddress value = (EthernetAddress) other;
                if (this < value) return -1;
                if (this > value) return + 1;
                return 0;
            }
            throw new ArgumentException ("Arg_MustBeEthernetAddress");
        }
    }
} // namespace Drivers.Net
