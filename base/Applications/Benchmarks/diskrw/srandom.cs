// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using Microsoft.Contracts;

namespace Microsoft.Singularity.Applications.Benchmarks.DiskRW
{
    /// <summary>
    /// Low-cost Integer random number generator.  The
    /// implementation is based on the description of Park and
    /// Miller's RNG on page 278 of Numerical Recipes in C, 2nd
    /// Edition, by Press, Teukolsky, Vetterling, and Flannery.
    ///
    /// The same random number generator is used for our disk
    /// benchmarks on other platforms.
    /// </summary>
    public class SRandom
    {
        public const uint Maximum = 0x7fffffffu;

        const ulong m = 2147483647;
        const ulong a = 16807;
        const uint  initialValue = 0x23456789;
        uint last;

        public SRandom()
        {
            Reset();
        }

        [Delayed]
        public void Reset()
        {
            last = initialValue;
        }

        public int Next()
        {
            // Use 64-bit multiplication to preserve high bits.
            ulong tmp = (a * last) % m;
            last = (uint) tmp;
            return (int)(last & Maximum);
        }

        public static void Check()
        {
            const int test_iterations = 10000000;
            SRandom r    = new SRandom();
            int     hash = 0;
            for (int i = 0; i < test_iterations; i++) {
                int n = r.Next();
                System.Diagnostics.Debug.Assert(n != 0);
                hash ^= n;
            }
            Console.Write("xor sum 1...{0} = {1}\n", test_iterations, hash);
            System.Diagnostics.Debug.Assert(hash == 1080076236);
        }
    }
}
