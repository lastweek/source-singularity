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
            return WaitTest.AppMain(this);
        }
    }
    
    public class WaitTest
    {
        //[ShellCommand("waittest", "Execute demo for non-infinite waiting")]
        internal static int AppMain(Parameters! config) {
            Console.WriteLine("Testing float and threads.");
            Console.Write("Still testing float and threads.");
            Console.WriteLine();
            TestFloat();
            Thread t1 = new Thread(new ThreadStart(WaitThreadOne));
            Thread t2 = new Thread(new ThreadStart(WaitThreadTwo));

            t1.Start();
            t2.Start();

            Console.WriteLine("Main Thread sleeping 6 seconds for test completion");
#if DEBUG_SLEEP
            ulong u1 = Processor.CycleCount;
#endif
            Thread.Sleep(TimeSpan.FromMilliseconds(6000));
#if DEBUG_SLEEP
            ulong u2 = Processor.CycleCount;
#endif
            Console.WriteLine("Main Thread waking and exiting");
#if DEBUG_SLEEP
            Console.WriteLine("  u1    = {0,14}", u1);
            Console.WriteLine("  u2    = {0,14}", u2);
            Console.WriteLine("  u2-u1 = {0,14}", u2 - u1);
            Console.WriteLine("  u2-u1 = {0,14} ms", ((u2 - u1) * 1000) / Processor.CyclesPerSecond);
#endif

            return 0;
        }

        public static void TestFloat()
        {
            ulong v;
            float f = (float)2.0;
            v = BitConverter.SingleToUInt32Bits((float)1.0);
            Console.WriteLine("   1.0 {0:x16}", v);
            v = BitConverter.SingleToUInt32Bits(f);
            Console.WriteLine("   2.0 {0:x16}", v);
            v = BitConverter.SingleToUInt32Bits((float)10.0);
            Console.WriteLine("  10.0 {0:x16}", v);
            v = BitConverter.DoubleToUInt64Bits(1.0);
            Console.WriteLine("   1.0 {0:x16}", v);
            v = BitConverter.DoubleToUInt64Bits(f);
            Console.WriteLine("   2.0 {0:x16}", v);
            v = BitConverter.DoubleToUInt64Bits(10.0);
            Console.WriteLine("  10.0 {0:x16}", v);

            if (f >= 1.0) {
                Console.WriteLine("  f >= 1.0");
            }
            if (f <= 10.0) {
                Console.WriteLine("  f <= 10.0");
            }
        }

        public static void WaitThreadOne() {
            Console.WriteLine("Starting Wait Thread One");
            TestFloat();

#if DONT
            Queue q = new Queue();
            Console.WriteLine("Queue: {0}\n", q);
#endif

            for (int i = 0; i < 5; i++) {
                Console.WriteLine("Thread One About To Sleep " + ProcessService.GetUpTime().Ticks);
                Thread.Sleep(TimeSpan.FromMilliseconds(1000));
                Console.WriteLine("Thread One Waking Up " + ProcessService.GetUpTime().Ticks);

            }
            Console.WriteLine("Wait Thread One Exiting");
        }
        public static void WaitThreadTwo() {
            Console.WriteLine("Starting Wait Thread Two");
            for (int i = 0; i < 10; i++) {
                Console.WriteLine("Thread Two About To Sleep " + ProcessService.GetUpTime().Ticks);
                Thread.Sleep(TimeSpan.FromMilliseconds(30));
                Console.WriteLine("Thread Two Waking Up " + ProcessService.GetUpTime().Ticks);

            }
            Console.WriteLine("Wait Thread Two Exiting");
        }
    }
}
