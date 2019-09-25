///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IPAddressUtils.cs
//

using System;

#if !SINGULARITY
using System.Net;
using System.Net.Sockets;
#endif

namespace System.Net.IP
{
    public sealed class IncompatibleAddressFamiliesException : SystemException
    {
        public IncompatibleAddressFamiliesException()
            : base("Attempting operation on addresses from incompatible "
                   + "families.")
        {
        }
    }

    public sealed class IPAddressBitwise
    {
        /// <summary>
        /// Perform the bitwise AND operation on two IPAddress
        /// objects and return a new IPAddress containing the
        /// result.
        ///
        /// <exception cref="IncompatibleAddressFamiliesException"></exception>
        /// </summary>
        public static IPAddress And(IPAddress l, IPAddress r)
        {
            if (l.AddressFamily != r.AddressFamily)
                throw new IncompatibleAddressFamiliesException();

            byte [] bl = l.GetAddressBytes();
            byte [] br = r.GetAddressBytes();

            if (l.AddressFamily == AddressFamily.InterNetwork) {
                bl[0] &= br[0];
                bl[1] &= br[1];
                bl[2] &= br[2];
                bl[3] &= br[3];
                int tmp = (bl[0] << 24) | (bl[1] << 16) | (bl[2] << 8) | bl[3];
                return new IPAddress(((long)tmp) & 0xffffffff);
            }
            bl[0] &= br[0];
            bl[1] &= br[1];
            bl[2] &= br[2];
            bl[3] &= br[3];
            bl[4] &= br[4];
            bl[5] &= br[5];
            bl[6] &= br[6];
            bl[7] &= br[7];
            bl[8] &= br[8];
            bl[9] &= br[9];
            bl[10] &= br[10];
            bl[11] &= br[11];
            bl[12] &= br[12];
            bl[13] &= br[13];
            bl[14] &= br[14];
            bl[15] &= br[15];
            return new IPAddress(bl);
        }

        /// <summary>
        /// Perform the bitwise OR operation on two
        /// IPAddress objects and return a new IPAddress
        /// containing the result.
        ///
        /// <exception cref="IncompatibleAddressFamiliesException"></exception>
        /// </summary>
        public static IPAddress Or(IPAddress l, IPAddress r)
        {
            if (l.AddressFamily != r.AddressFamily)
                throw new IncompatibleAddressFamiliesException();

            byte [] bl = l.GetAddressBytes();
            byte [] br = r.GetAddressBytes();

            if (l.AddressFamily == AddressFamily.InterNetwork) {
                bl[0] |= br[0];
                bl[1] |= br[1];
                bl[2] |= br[2];
                bl[3] |= br[3];
                int tmp = (bl[0] << 24) | (bl[1] << 16) | (bl[2] << 8) | bl[3];
                return new IPAddress(((long)tmp) & 0xffffffff);
            }

            bl[0] |= br[0];
            bl[1] |= br[1];
            bl[2] |= br[2];
            bl[3] |= br[3];
            bl[4] |= br[4];
            bl[5] |= br[5];
            bl[6] |= br[6];
            bl[7] |= br[7];
            bl[8] |= br[8];
            bl[9] |= br[9];
            bl[10] |= br[10];
            bl[11] |= br[11];
            bl[12] |= br[12];
            bl[13] |= br[13];
            bl[14] |= br[14];
            bl[15] |= br[15];
            return new IPAddress(bl);
        }

        /// <summary>
        /// Perform the bitwise eXclusive-OR operation on two
        /// IPAddress objects and return a new IPAddress
        /// containing the result.
        ///
        /// <exception cref="IncompatibleAddressFamiliesException"></exception>
        /// </summary>
        public static IPAddress Xor(IPAddress l, IPAddress r)
        {
            if (l.AddressFamily != r.AddressFamily)
                throw new IncompatibleAddressFamiliesException();

            byte [] bl = l.GetAddressBytes();
            byte [] br = r.GetAddressBytes();

            if (l.AddressFamily == AddressFamily.InterNetwork) {
                bl[0] ^= br[0];
                bl[1] ^= br[1];
                bl[2] ^= br[2];
                bl[3] ^= br[3];
                int tmp = (bl[0] << 24) | (bl[1] << 16) | (bl[2] << 8) | bl[3];
                return new IPAddress(((long)tmp) & 0xffffffff);
            }

            bl[0] ^= br[0];
            bl[1] ^= br[1];
            bl[2] ^= br[2];
            bl[3] ^= br[3];
            bl[4] ^= br[4];
            bl[5] ^= br[5];
            bl[6] ^= br[6];
            bl[7] ^= br[7];
            bl[8] ^= br[8];
            bl[9] ^= br[9];
            bl[10] ^= br[10];
            bl[11] ^= br[11];
            bl[12] ^= br[12];
            bl[13] ^= br[13];
            bl[14] ^= br[14];
            bl[15] ^= br[15];
            return new IPAddress(bl);
        }

        /// <summary>
        /// Perform the bitwise NOT operation on an IPAddress
        /// and return a new IPAddress containing the result.
        ///
        /// <exception cref="IncompatibleAddressFamiliesException"></exception>
        /// </summary>
        public static IPAddress Not(IPAddress l)
        {
            byte [] bl = l.GetAddressBytes();

            if (l.AddressFamily == AddressFamily.InterNetwork) {
                bl[0] = (byte) ~bl[0];
                bl[1] = (byte) ~bl[1];
                bl[2] = (byte) ~bl[2];
                bl[3] = (byte) ~bl[3];
                int tmp = (bl[0] << 24) | (bl[1] << 16) | (bl[2] << 8) | bl[3];
                return new IPAddress(((long)tmp) & 0xffffffff);
            }

            bl[0] = (byte) ~bl[0];
            bl[1] = (byte) ~bl[1];
            bl[2] = (byte) ~bl[2];
            bl[3] = (byte) ~bl[3];
            bl[4] = (byte) ~bl[4];
            bl[5] = (byte) ~bl[5];
            bl[6] = (byte) ~bl[6];
            bl[7] = (byte) ~bl[7];
            bl[8] = (byte) ~bl[8];
            bl[9] = (byte) ~bl[9];
            bl[10] = (byte) ~bl[10];
            bl[11] = (byte) ~bl[11];
            bl[12] = (byte) ~bl[12];
            bl[13] = (byte) ~bl[13];
            bl[14] = (byte) ~bl[14];
            bl[15] = (byte) ~bl[15];
            return new IPAddress(bl);
        }

        static IPAddressBitwise()
        {
        }

        private IPAddressBitwise()
        {
        }
    }

    public sealed class IPAddressCompare
    {
        public static bool LessThan(IPAddress l, IPAddress r)
        {
            if (l.AddressFamily != r.AddressFamily)
                throw new IncompatibleAddressFamiliesException();

            byte [] bl = l.GetAddressBytes();
            byte [] br = r.GetAddressBytes();

            uint ul = 0;
            uint ur = 0;

            for (int i = 0; i < bl.Length; i += 4) {
                ul = (uint)((bl[i + 0] << 24) | (bl[i + 1] << 16) |
                            (bl[i + 2] <<  8) | (bl[i + 3]));
                ur = (uint)((br[i + 0] << 24) | (br[i + 1] << 16) |
                            (br[i + 2] <<  8) | (br[i + 3]));
                if (ul > ur)
                    return false;
            }
            return ul < ur;
        }

        public static bool LessThanEqualTo(IPAddress l, IPAddress r)
        {
            if (l.AddressFamily != r.AddressFamily)
                throw new IncompatibleAddressFamiliesException();

            byte [] bl = l.GetAddressBytes();
            byte [] br = r.GetAddressBytes();

            uint ul = 0;
            uint ur = 0;

            for (int i = 0; i < bl.Length; i += 4) {
                ul = (uint)((bl[i + 0] << 24) | (bl[i + 1] << 16) |
                            (bl[i + 2] <<  8) | (bl[i + 3]));
                ur = (uint)((br[i + 0] << 24) | (br[i + 1] << 16) |
                            (br[i + 2] <<  8) | (br[i + 3]));
                if (ul > ur)
                    return false;
            }
            return ul <= ur;
        }

        public static bool GreaterThan(IPAddress l, IPAddress r)
        {
            return !LessThanEqualTo(l, r);
        }

        public static bool GreaterThanEqualTo(IPAddress l, IPAddress r)
        {
            return !LessThan(l, r);
        }

        private IPAddressCompare()
        {
        }
    }

#if TEST_IPADDRESS_UTILS
    public class Test
    {
        static void Output(string format, params object[] args)
        {
            Console.Write(format, args);
        }

        static void Main()
        {
            IPAddress a = IPAddress.Parse("10.0.0.1");
            IPAddress b = IPAddress.Parse("192.168.0.1");
            IPAddress c = IPAddress.Parse("170.170.170.170");
            IPAddress d = IPAddress.Parse("255.255.255.255");
            IPAddress e = IPAddress.Parse("85.85.85.85");

            IPAddress x = new IPAddress(IPAddress.IPv6Any.GetAddressBytes());

            Output("Expect: a < b  {0}\n",
                   IPAddressCompare.LessThan(a, b));
            Output("Expect: a <= a {0}\n",
                   IPAddressCompare.LessThanEqualTo(a, a));

            Output("c AND d == d {0}\n", IPAddressBitwise.And(c, d).Equals(c));
            Output("c AND e == d {0}\n", IPAddressBitwise.Or(c, e).Equals(d));
            Output("c XOR d == e {0}\n", IPAddressBitwise.Xor(c, e).Equals(d));
            Output("c XOR d == 0 {0}\n", IPAddressBitwise.Xor(c, c).Equals(IPAddress.Any));
            Output("NOT c == e {0}\n", IPAddressBitwise.Not(c).Equals(e));
        }
    }
#endif
} // namespace System.Net.IP
