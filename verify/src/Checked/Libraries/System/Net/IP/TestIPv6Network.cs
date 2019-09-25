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

    public class TestIPv6Network
    {
        private static void TestBasics()
        {
            IPv6 address = IPv6.Parse("ab1e:d00d::1057:d05");
            IPv6 mask    = IPv6.Parse("ffff:fffe::");
            int  masklen = 31;

            if (new IPv6Network(address, masklen) !=
                new IPv6Network(address, mask))
            {
                throw new TestFailedException("Constructors");
            }

            if (IPv6Network.Parse("10::/24") !=
                new IPv6Network(new IPv6(0x00100000, 0x0, 0x0, 0x0), 24))
            {
                Console.WriteLine(IPv6Network.Parse("10::/24"));
                Console.WriteLine(new IPv6Network(new IPv6(0x00100000, 0x0, 0x0, 0x0), 24));
                throw new TestFailedException("10::/24");
            }

            if (IPv6Network.Parse("10::/32") !=
                new IPv6Network(new IPv6(0x00100000, 0x0, 0x0, 0x0), 32))
            {
                throw new TestFailedException("10::/32");
            }

            if (IPv6Network.Parse("10::/1") !=
                new IPv6Network(new IPv6(0x00100000,0x0, 0x0, 0x0), 1))
            {
                throw new TestFailedException("10::/1");
            }

            try {
                IPv6Network.Parse("10:://12");
                throw new TestFailedException("double slash");
            }
            catch (FormatException) {
            }

            try {
                IPv6Network.Parse("10::/129");
                throw new TestFailedException("netmask length");
            }
            catch (ArgumentException) {
            }

            try {
                IPv6Network.Parse("10::/xx");
                throw new TestFailedException("netmask content");
            }
            catch (FormatException) {
            }

            try {
                IPv6Network.Parse("10::x/10");
                throw new TestFailedException("network content");
            }
            catch (FormatException) {
            }

            try {
                IPv6Network.Parse("10::/3333333333333333333333333333");
                throw new TestFailedException("netmask overflow");
            }
            catch (OverflowException) {
            }
        }

        public static void TestCompare()
        {
            IPv6 address = IPv6.Parse("dead:beef:cafe:babe:5ca1:ab1e:b01d:face");
            IPv6Network outer = new IPv6Network(address, 124);
            IPv6Network inner = new IPv6Network(address, 126);

            if (outer.Contains(outer) == false) {
                throw new TestFailedException("outer.Contains(outer)");
            }

            if (outer.Contains(inner) == false) {
                throw new TestFailedException("outer.Contains(inner)");
            }

            if (inner.Contains(outer) == true) {
                throw new TestFailedException("inner.Contains(outer)");
            }

            if (outer.Contains(address) == false) {
                throw new TestFailedException("outer.Contains(address)");
            }

            if (inner.Contains(address) == false) {
                throw new TestFailedException("inner.Contains(address)");
            }

            if (outer.IsMoreSpecificThan(inner) == true) {
                throw new TestFailedException("outer.IsMoreSpecificThan(inner)");
            }

            if (outer.IsLessSpecificThan(inner) == false) {
                throw new TestFailedException("outer.IsLessSpecificThan(inner)");
            }

            if ((outer == outer) == false) {
                throw new TestFailedException("operator==");
            }

            if ((outer != inner) == false) {
                throw new TestFailedException("operator!=");
            }

            if (outer.Contains(outer.UpperBound) == false) {
                throw new TestFailedException("outer.Contains(outer.UpperBound)");
            }

            if (outer.Contains(outer.LowerBound) == false) {
                throw new TestFailedException("outer.Contains(outer.LowerBound)");
            }
        }

        public static int Main()
        {
            try {
                TestBasics();
                TestCompare();
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
