////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program.
//
using System;
using System.Threading;

using Microsoft.Singularity.Channels;
using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal Parameters();

        internal int AppMain() {
            return Hog.AppMain(this);
        }
    }

    public class Hog
    {
        public static void HogFunction()
        {
            int i = 0;
            while (true) {
                if ((i % 10000000) == 0) {
                    Console.Write(".");
                }
                i++;
            }
        }

        //[ShellCommand("hog", "Run processor hog")]
        internal static int AppMain(Parameters! config)
        {
            Console.WriteLine("Starting a hog...");

            Thread hog = new Thread(new ThreadStart(HogFunction));
            hog.Start();
            return 0;
        }
    }
}
