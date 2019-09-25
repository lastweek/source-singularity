///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TestIPv6.cs
//

using System;

#if !SINGULARITY
using System.Net;
#endif // !SINGULARITY

namespace System.Net.IP
{
    internal class TestFailedException : Exception
    {
        internal TestFailedException(string msg)
            : base(String.Format("TestFailedException \"{0}\"", msg))
        {
        }
    }

    public class TestIPv6
    {
        private static void TestBasics()
        {
            // Create an IPv6 address from a set of uints
            IPv6 a = new IPv6(0xf0e1d2c3, 0xb4a59687, 0x78695a4b, 0x3c2d1e0f);

            // Then check it against equivalent array of Bytes
            byte[] xBytes = { 0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5, 0x96, 0x87,
                              0x78, 0x69, 0x5a, 0x4b, 0x3c, 0x2d, 0x1e, 0x0f };
            byte[] aBytes = a.GetAddressBytes();
            if (aBytes.Length != 16)
                throw new TestFailedException("GetAddressBytes Length");

            for (int i = 0; i < aBytes.Length; i++) {
                if (aBytes[i] != xBytes[i])
                    throw new TestFailedException("GetAddressBytes Values");
            }

            // Instantiate from array of bytes and then check
            a = IPv6.ParseBytes(xBytes);
            aBytes = a.GetAddressBytes();

            if (aBytes.Length != 16)
                throw new TestFailedException("GetAddressBytes Length");

            for (int i = 0; i < aBytes.Length; i++) {
                if (aBytes[i] != xBytes[i])
                    throw new TestFailedException("GetAddressBytes Values");
            }

            // Test System.Net.IPAddress Constructor
            IPAddress ipa = new IPAddress(aBytes);
            if (new IPv6(ipa) != a) {
                throw new TestFailedException("IPv6(IPAddress) Constructor");
            }

            // Test basic string parsing
            a = IPv6.Parse("f0e1:d2c3:b4a5:9687:7869:5a4b:3c2d:1e0f");
            aBytes = a.GetAddressBytes();

            if (aBytes.Length != 16)
                throw new TestFailedException("GetAddressBytes Length");

            for (int i = 0; i < aBytes.Length; i++) {
                if (aBytes[i] != xBytes[i])
                    throw new TestFailedException("GetAddressBytes Values");
            }
        }

        private static void TestCompare()
        {
            IPv6 a = new IPv6(0x11111111, 0x22222222, 0x33333333, 0x44444444);
            IPv6 b = new IPv6(0x11111111, 0x22222222, 0x33333333, 0x44444443);

            if ((a == a) == false) {
                throw new TestFailedException("a == a");
            }

            if ((a != b) == false) {
                throw new TestFailedException("a == b");
            }

            if ((a > b) == false) {
                throw new TestFailedException("a > b");
            }

            if ((a >= b) == false) {
                throw new TestFailedException("a >= b");
            }

            if ((a >= a) == false) {
                throw new TestFailedException("a >= a");
            }

            if ((a > a) == true) {
                throw new TestFailedException("a > a");
            }

            if ((a < b) == true) {
                throw new TestFailedException("a < b");
            }

            if ((a <= b) == true) {
                throw new TestFailedException("a <= b");
            }

            if ((a <= a) != true) {
                throw new TestFailedException("a <= a");
            }

            if ((a < a) == true) {
                throw new TestFailedException("a < a");
            }
        }

        private static void TestRoll()
        {
            IPv6 a = new IPv6(0x01234567, 0x89abcdef, 0x02461357, 0x8ace9bdf);

            if ((a << 4) !=
                new IPv6(0x12345678, 0x9abcdef0, 0x24613578, 0xace9bdf0))
            {
                throw new TestFailedException("a << 4");
            }

            if ((a << 36) != new IPv6(0x9abcdef0, 0x24613578, 0xace9bdf0, 0)) {
                throw new TestFailedException("a << 36");
            }

            if ((a << 68) != new IPv6(0x24613578, 0xace9bdf0, 0, 0)) {
                throw new TestFailedException("a << 68");
            }

            if ((a << 100) != new IPv6(0xace9bdf0, 0, 0, 0)) {
                throw new TestFailedException("a << 100");
            }

            if ((a << 128) != new IPv6(0, 0, 0, 0)) {
                throw new TestFailedException("a << 128");
            }

            if ((a >> 4) !=
                new IPv6(0x00123456, 0x789abcde, 0xf0246135, 0x78ace9bd))
            {
                throw new TestFailedException("a >> 4");
            }

            if ((a >> 36) != new IPv6(0, 0x00123456, 0x789abcde, 0xf0246135)) {
                throw new TestFailedException("a >> 36");
            }

            if ((a >> 68) != new IPv6(0, 0, 0x00123456, 0x789abcde)) {
                throw new TestFailedException("a >> 68");
            }

            if ((a >> 100) != new IPv6(0, 0, 0, 0x00123456)) {
                throw new TestFailedException("a >> 100");
            }

            if ((a >> 128) != new IPv6(0, 0, 0, 0)) {
                throw new TestFailedException("a >> 128");
            }
        }

        private static void TestBits()
        {
            IPv6 a = new IPv6(0x7f7f7f7f, 0x7f7f7f7f, 0x7f7f7f7f, 0x7f7f7f7f);
            IPv6 b = new IPv6(0xc1c1c1c1, 0xc1c1c1c1, 0xc1c1c1c1, 0xc1c1c1c1);
            IPv6 goal;

            goal = new IPv6(~0U, ~0U, ~0U, ~0U);
            if ((a | b) != goal) {
                throw new TestFailedException("OR");
            }

            goal = new IPv6(0x41414141, 0x41414141, 0x41414141, 0x41414141);
            if ((a & b) != goal) {
                throw new TestFailedException("AND");
            }

            goal = new IPv6(0xbebebebe, 0xbebebebe, 0xbebebebe, 0xbebebebe);
            if ((a ^ b) != goal) {
                throw new TestFailedException("XOR");
            }

            goal = new IPv6(0x80808080, 0x80808080, 0x80808080, 0x80808080);
            if (~a != goal) {
                throw new TestFailedException("NOT");
            }

            // Test netmask
            for (int i = 0; i < 128; i++) {
                IPv6 mask = IPv6.NetMask(i);
                goal = IPv6.AllOnes << (128 - i);
                if (mask != goal) {
                    Console.WriteLine("{0} {1} {2}", i, mask, goal);
                    throw new TestFailedException("NetMask");
                }

                goal = ~(IPv6.AllOnes >> i);
                if (mask != goal) {
                    Console.WriteLine("{0} {1} {2}", i, mask, goal);
                    throw new TestFailedException("NetMask2");
                }
            }

            try {
                IPv6 n = IPv6.NetMask(129);
                throw new TestFailedException("Bad Netmask +");
            }
            catch (ArgumentException) {
            }

            try {
                IPv6 n = IPv6.NetMask(-1);
                throw new TestFailedException("Bad Netmask -");
            }
            catch (ArgumentException) {
            }
        }

        private struct SrepV6Pair
        {
            public string srep;
            public IPv6   v6rep;

            public SrepV6Pair(string s, IPv6 a)
            {
                srep = s;
                v6rep = a;
            }
        };

        private static void TestParse()
        {
            //
            // grumble, grumble, no clean struct array initializer syntax !?!
            //
            // Okay, these are pairs of Valid IPv6 string representations
            // and their manually parsed IPv6 representations.
            //
            SrepV6Pair [] pairs = new SrepV6Pair[] {
                new SrepV6Pair (
                    "FfEe:DdCc:BbAa:9876:5432:1001:2345:6789",
                    new IPv6(0xffeeddcc, 0xbbaa9876, 0x54321001, 0x23456789)
                    ),
                new SrepV6Pair (
                    "ffe8:c181::192:101",
                    new IPv6(0xffe8c181U, 0x0U, 0x0U, 0x01920101U)
                    ),
                new SrepV6Pair (
                    "::",
                    IPv6.Zero
                    ),
                new SrepV6Pair (
                    "0:0:0:0:0:0:0:0",
                    IPv6.Zero
                    ),
                new SrepV6Pair (
                    "1::",
                    new IPv6(0x00010000U, 0x0U, 0x0U, 0x0U)
                    ),
                new SrepV6Pair (
                    "12::",
                    new IPv6(0x00120000U, 0x0U, 0x0U, 0x0U)
                    ),
                new SrepV6Pair (
                    "123::",
                    new IPv6(0x01230000U, 0x0U, 0x0U, 0x0U)
                    ),
                new SrepV6Pair (
                    "1234::",
                    new IPv6(0x12340000U, 0x0U, 0x0U, 0x0U)
                    ),
                new SrepV6Pair (
                    "1234:5678:9abc:def0::",
                    new IPv6(0x12345678U, 0x9abcdef0U, 0x0U, 0x0U)
                    ),
                new SrepV6Pair (
                    "::1",
                    new IPv6(0x0U, 0x0U, 0x0U, 0x1U)
                    ),
                new SrepV6Pair (
                    "::12",
                    new IPv6(0x0U, 0x0U, 0x0U, 0x12U)
                    ),
                new SrepV6Pair (
                    "::123",
                    new IPv6(0x0U, 0x0U, 0x0U, 0x123U)
                    ),
                new SrepV6Pair (
                    "::1234",
                    new IPv6(0x0U, 0x0U, 0x0U, 0x1234U)
                    ),
                new SrepV6Pair (
                    "::1234:5678:9abc:def0",
                    new IPv6(0x0U, 0x0U, 0x12345678U, 0x9abcdef0U)
                    ),
            };

            for (int i = 0; i < pairs.Length; i++) {
                IPv6 a = IPv6.Parse(pairs[i].srep);
                if (a != pairs[i].v6rep) {
                    Console.WriteLine("{0} {1}", a, pairs[i].v6rep);
                    throw new TestFailedException(
                        String.Format("Parse {0}", i)
                        );
                }

                IPv6 dup = IPv6.Parse(a.ToString());
                if (dup != a) {
                    throw new TestFailedException(
                        String.Format("ToString {0}", i)
                        );
                }
            }

            //
            // Test bogus strings
            //
            string [] badSreps = new string [] {
                "Frank",
                "00000::",
                "0:1:2:3:4:5:6:7:8",
                "0.1.2.3.4::0.1.2.3.4.",
                "0:1:2:3:4:5:6:7:trailing junk",
            };

            for (int i = 0; i < badSreps.Length; i++) {
                try {
                    IPv6 bad = IPv6.Parse(badSreps[i]);
                    throw new TestFailedException(badSreps[i]);
                }
                catch (FormatException) {
                }
            }
        }

        private static void TestMath()
        {
            IPv6 a = IPv6.Zero;

            if (--a != IPv6.AllOnes) {
                throw new TestFailedException("--");
            }
            if (++a != IPv6.Zero) {
                throw new TestFailedException("++");
            }
        }

        public static void TestCount()
        {
            for (int i = 0; i < IPv6.BitCount; i++) {
                IPv6 addr = IPv6.NetMask(i);
                if (IPv6.GetMaskLength(addr) != i) {
                    throw new TestFailedException(
                        String.Format("TestCount {0}", i)
                        );
                }

                IPv6 addrDup = IPv6.Parse(addr.ToString());
                if (addrDup != addr) {
                    throw new TestFailedException(
                        String.Format("TestCountDup {0}", i)
                        );
                }
            }
        }

        public static int Main()
        {
            try {
                TestBasics();
                TestCompare();
                TestRoll();
                TestBits();
                TestParse();
                TestMath();
                TestCount();
            }
            catch (Exception e) {
                Console.WriteLine("FAILED\nException {0}\nStack:\n{1}",
                                  e.Message, e.StackTrace);
                return 1;
            }
            Console.WriteLine("Passed.");
            return 0;
        }
    }
} // namespace System.Net.IP
