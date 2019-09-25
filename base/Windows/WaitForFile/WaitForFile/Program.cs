// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using System.Threading;

namespace MS.Internal
{
    class WaitForFile
    {
        static int Main(string[] args)
        {
            if (args.Length != 1) {
                Console.WriteLine("WaitForFile <file>");
                return 1;
            }

            while (true) {
                try {
                    using (File.Open(args[0], FileMode.Open, FileAccess.Read)) {
                        // If we managed to open the file, we're done.  Exit with success.
                        return 0;
                    }
                }
                catch (Exception e) {
                    Console.WriteLine("WaitForFile: {0} (Retry in 1 second).", e.Message);
                    Thread.Sleep(1000);
                }
            }
        }
    }
}
