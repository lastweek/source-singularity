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

    public class TestIPv4Network
    {
        private static void TestBasics()
        {
            IPv4 address = IPv4.Parse("192.168.0.100");
            IPv4 mask    = IPv4.Parse("255.255.255.254");
            int  masklen = 31;

            if (new IPv4Network(address, masklen) !=
                new IPv4Network(address, mask))
            {
                throw new TestFailedException("Constructors");
            }

            if (IPv4Network.Parse("10.0.0.0/24") !=
                new IPv4Network(new IPv4(0x0a000000), 24))
            {
                throw new TestFailedException("10/24");
            }

            if (IPv4Network.Parse("10.0.0.0/32") !=
                new IPv4Network(new IPv4(0x0a000000), 32))
            {
                throw new TestFailedException("10/32");
            }

            if (IPv4Network.Parse("10.0.0.0/1") !=
                new IPv4Network(new IPv4(0x0a000000), 1))
            {
                throw new TestFailedException("10/1");
            }

            try {
                IPv4Network.Parse("10.0.0.1//2");
                throw new TestFailedException("double slash");
            }
            catch (FormatException) {
            }

            try {
                IPv4Network.Parse("10.0.0.0/33");
                throw new TestFailedException("netmask length");
            }
            catch (ArgumentException) {
            }

            try {
                IPv4Network.Parse("10.0.0.0/xx");
                throw new TestFailedException("netmask content");
            }
            catch (FormatException) {
            }

            try {
                IPv4Network.Parse("10.x.0.0/10");
                throw new TestFailedException("network content");
            }
            catch (FormatException) {
            }

            try {
                IPv4Network.Parse("10.0.0.0/3333333333333333333333333333");
                throw new TestFailedException("netmask overflow");
            }
            catch (OverflowException) {
            }
        }

        public static void TestCompare()
        {
            IPv4 address = IPv4.Parse("10.1.1.0");
            IPv4Network outer = new IPv4Network(address, 24);
            IPv4Network inner = new IPv4Network(address, 26);

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
