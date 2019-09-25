///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

/*
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

    public class TestIPv4
    {
        private static void TestBasics()
        {
            IPv4 a = new IPv4(0x1a2b3c4d);
            IPv4 b = IPv4.Parse("0x1a.0x2b.0x3c.0x4d");
            byte [] ipv4Bytes = new byte [4] { 0x1a, 0x2b, 0x3c, 0x4d };
            IPv4 c = IPv4.ParseBytes(ipv4Bytes);

            if ((uint)a != 0x1a2b3c4d)
                throw new TestFailedException("a");

            if ((uint)b != 0x1a2b3c4d)
                throw new TestFailedException("b");

            if ((uint)c != 0x1a2b3c4d)
                throw new TestFailedException("c");

            if (a.Equals(b) == false)
                throw new TestFailedException("a Equals b");

            if ((a == c) == false || (a != c))
                throw new TestFailedException("a c == !=");

            for (int i = 0; i < ipv4Bytes.Length; i++) {
                if (ipv4Bytes[i] != c.GetAddressBytes()[i])
                    throw new TestFailedException("GetAddressBytes");
            }

            byte [] ipAddrBytes = ((IPAddress)c).GetAddressBytes();
            for (int i = 0; i < ipv4Bytes.Length; i++) {
                if (ipv4Bytes[i] != ipAddrBytes[i])
                    throw new TestFailedException("IPAddress");
            }

            IPAddress ipa = IPAddress.Parse(c.ToString());
            if (new IPv4(ipa) != c) {
                throw new TestFailedException("IPv4(IPAddress) Constructor");
            }
        }

        private static void TestCompare()
        {
            IPv4 a = new IPv4(0x0a000001);
            IPv4 b = new IPv4(0x0a000000);

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
            IPv4 a = new IPv4(0x80808080);

            if ((uint)(a << 1) != 0x01010100) {
                throw new TestFailedException("<< 1");
            }

            if ((uint)(a << 2) != 0x02020200) {
                throw new TestFailedException("<< 2");
            }

            if ((uint)(a << 32) != 0) {
                throw new TestFailedException("<< 32");
            }

            if ((uint)(a >> 1) != 0x40404040) {
                throw new TestFailedException(">> 1");
            }

            if ((uint)(a >> 2) != 0x20202020) {
                throw new TestFailedException(">> 2");
            }

            if ((uint)(a >> 32) != 0) {
                throw new TestFailedException(">> 32");
            }
        }

        private static void TestBits()
        {
            IPv4 a = new IPv4(0x7f7f7f7f);
            IPv4 b = new IPv4(0xc1c1c1c1);

            if ((uint)(a | b) != ~0U) {
                throw new TestFailedException("OR");
            }

            if ((uint)(a & b) != 0x41414141) {
                throw new TestFailedException("AND");
            }

            if ((uint)(a ^ b) != 0xbebebebe) {
                throw new TestFailedException("XOR");
            }

            if ((uint)(~a) != 0x80808080) {
                throw new TestFailedException("NOT");
            }

            if ((uint)IPv4.NetMask(0) != 0) {
                throw new TestFailedException("NetMask(0)");
            }

            if ((uint)IPv4.NetMask(17) != 0xffff8000) {
                throw new TestFailedException("NetMask(17)");
            }

            if ((uint)IPv4.NetMask(32) != 0xffffffffu) {
                throw new TestFailedException("NetMask(32)");
            }

            try {
                IPv4 n = IPv4.NetMask(66);
                throw new TestFailedException("Bad Netmask +");
            }
            catch (ArgumentException) {
            }
            try {
                IPv4 n = IPv4.NetMask(-1);
                throw new TestFailedException("Bad Netmask -");
            }
            catch (ArgumentException) {
            }
        }

        private static void TestParseOne(string ipString,
                                         IPv4 expectedIP,
                                         bool expectedSuccess)
        {
            bool success = false;
            IPv4 testIP  = IPv4.Zero;

            try {
                testIP = IPv4.Parse(ipString);
                success = (testIP == expectedIP);
            }
            catch (FormatException) {
            }
            if (success != expectedSuccess) {
                throw new TestFailedException(ipString);
            }

            IPv4 dup = IPv4.Parse(testIP.ToString());
            if (testIP != dup) {
                throw new TestFailedException(
                    String.Format("ToString {0}", testIP)
                    );
            }
        }

        private static void TestParse()
        {
            // Decimal Quads
            TestParseOne("1000.0.0.1",  IPv4.Zero, false);
            TestParseOne("0.1000.0.1",  IPv4.Zero, false);
            TestParseOne("0.0.1000.1",   IPv4.Zero, false);
            TestParseOne("0.0.00.1000", IPv4.Zero, false);
            TestParseOne("0.0.trailing.junk", IPv4.Zero, false);
            TestParseOne("100.0.0.1", new IPv4(0x64000001), true);
            TestParseOne("0.100.0.1", new IPv4(0x00640001), true);
            TestParseOne("0.0.100.1", new IPv4(0x00006401), true);
            TestParseOne("0.0.0.100", new IPv4(0x00000064), true);
            TestParseOne("1", new IPv4(0x00000001), true);
            TestParseOne("1.1", new IPv4(0x01000001), true);
            TestParseOne("1.1.1", new IPv4(0x01010001), true);
            TestParseOne("1.1.1.1", new IPv4(0x01010101), true);

            // Hex Quads
            TestParseOne("0xfff.0x0.0x0.0x1", IPv4.Zero, false);
            TestParseOne("0x0.0xg0.0x0.0x1", IPv4.Zero, false);
            TestParseOne("0x0.0.0x1000.1", IPv4.Zero, false);
            TestParseOne("0x0.0x0.0x0.0x1000", IPv4.Zero, false);
            TestParseOne("0x0.0x0.0xtrailing.0xjunk", IPv4.Zero, false);
            TestParseOne("0xaA.0xbB.0xcC.0xdD", new IPv4(0xaabbccdd), true);
            TestParseOne("0xeE.0xfF.0x01.0x02", new IPv4(0xeeff0102), true);
            TestParseOne("0x1", new IPv4(0x00000001), true);
            TestParseOne("0x1.0x1", new IPv4(0x01000001), true);
            TestParseOne("0x1.0x1.0x1", new IPv4(0x01010001), true);
            TestParseOne("0x1.0x1.0x1.0x1", new IPv4(0x01010101), true);

            // Octal Quads
            TestParseOne("0378.00.00.00", IPv4.Zero, false);
            TestParseOne("0477.00.00.00", IPv4.Zero, false);
            TestParseOne("0378.00.00.00", IPv4.Zero, false);
            TestParseOne("0477.00.00.00", IPv4.Zero, false);
            TestParseOne("01.02.0trailing.0junk", IPv4.Zero, false);

            TestParseOne("0377.0376.0375.0374", new IPv4(0xfffefdfc), true);
            TestParseOne("01", new IPv4(0x00000001), true);
            TestParseOne("01.01", new IPv4(0x01000001), true);
            TestParseOne("01.01.01", new IPv4(0x01010001), true);
            TestParseOne("01.01.01.01", new IPv4(0x01010101), true);
        }

        private static void TestMath()
        {
            IPv4 a = new IPv4(0x0a000001);

            if ((uint)++a != 0x0a000002)
                throw new TestFailedException("Increment");

            if ((uint) --a != 0x0a000001)
                throw new TestFailedException("Decrement 1");

            if ((uint) --a != 0x0a000000)
                throw new TestFailedException("Decrement 2");

            if ((uint) --a != 0x09ffffff)
                throw new TestFailedException("Decrement 3");
        }

        public static void TestCount()
        {
            for (int i = IPv4.BitCount; i >= 0; i--) {
                IPv4 addr = IPv4.NetMask(i);
                if (IPv4.GetMaskLength(addr) != i) {
                    throw new TestFailedException(
                        String.Format("TestCount {0}", i)
                        );
                }

                IPv4 addrDup = IPv4.Parse(addr.ToString());
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
*/
