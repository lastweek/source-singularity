// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;

namespace Microsoft.Singularity.AdjustTest
{
    public struct Holder : IDisposable
    {
        int handle;
        public Holder(int i)
        {
            handle = i;
        }
        public void Dispose()
        {
            Console.WriteLine("Disposed {0}", handle);
        }
    }

    public class Test
    {
        public static Holder Hold(int i)
        {
            return new Holder(i);
        }

        //[ShellCommand("adjusttest", "Test code rewriting.")]
        public static void Main()
        {
            Console.WriteLine("starting");
            using (Hold(3)) {
                Console.WriteLine("using");
            }
            Console.WriteLine("used");
        }
    }
}
