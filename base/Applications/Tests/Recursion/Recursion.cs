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
            return Recursion.AppMain(this);
        }
    }
    public class Recursion
    {
        public static void RecursiveMethod(int i)
        {
            if (i > 0) {
                if ((i % 10) == 0) {
                    Console.WriteLine("Down: {0}", i);
                }

                RecursiveMethod(i - 1);

                if ((i % 10) == 0) {
                    Console.WriteLine("Up:   {0}", i);
                }
            }
        }

        public static void RecursiveThreadMethod()
        {
            RecursiveMethod(500);
        }

        //[ShellCommand("recur", "Run recursive thread demo")]
        internal static int AppMain(Parameters! config)
        {
            Thread t1 = new Thread(new ThreadStart(RecursiveThreadMethod));
            t1.Start();
            return 0;
        }
    }
}
