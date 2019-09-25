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
using Microsoft.Singularity.V1.Services;

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
            return ThreadTest.AppMain(this);
        }
    }
    
    public class ThreadTest
    {
        public static void FirstThreadMethod()
        {
            Console.WriteLine("First thread!");
            DebugStub.Print("First thread!\n");

            for (int i = 0; i < 10; i++) {
                Console.WriteLine("[0] ...    ");
                Thread.Yield();
            }

            Console.WriteLine("First thread done!");
            DebugStub.Print("First thread done!\n");
        }

        public static void SecondThreadMethod()
        {
            Console.WriteLine("Second thread!");
            DebugStub.Print("Second thread!\n");

            for (int i = 0; i < 10; i++) {
                Console.WriteLine("    ... [1]");
                Thread.Yield();
            }

            Console.WriteLine("Second thread done!");
            DebugStub.Print("Second thread done!\n");
        }

        internal static int AppMain(Parameters! config)
        {
            Thread t1 = new Thread(new ThreadStart(FirstThreadMethod));
            Thread t2 = new Thread(new ThreadStart(SecondThreadMethod));

            Console.WriteLine("Starting first thread.");
            t1.Start();
            Console.WriteLine("Started first thread.");

            Console.WriteLine("Starting second thread.");
            t2.Start();
            Console.WriteLine("Started second thread.");

            for (int i = 0; i < 30; i++) {
                Thread.Yield();
            }
            return 0;
        }
    }
}
