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
            return Sync.AppMain(this);
        }
    }

    public class Sync
    {
        private static Mutex! mutex;
        private static AutoResetEvent! autoResetEvent;
        private static ManualResetEvent! manualResetEvent;
        private static AutoResetEvent! syncEvent;

        public static void SyncThread()
        {
            Console.WriteLine("[2] Acquiring mutex...");
            mutex.WaitOne();
            Console.WriteLine("[2] Mutex acquired!");
            mutex.ReleaseMutex();
            Console.WriteLine("[2] Mutex released.");

            Thread.Yield();
            Thread.Yield();
            Thread.Yield();
            Thread.Yield();
            Thread.Yield();

            Console.WriteLine("[2] Setting event.");
            autoResetEvent.Set();

            Thread.Yield();
            Thread.Yield();
            Thread.Yield();
            Thread.Yield();
            Thread.Yield();

            Console.WriteLine("[2] Waiting for notification...");
            syncEvent.WaitOne();

            Console.WriteLine("[2] Setting event.");
            autoResetEvent.Set();

            Console.WriteLine("[2] Waiting for notification...");
            syncEvent.WaitOne();

            Console.WriteLine("[2] Setting manual event.");
            manualResetEvent.Set();
        }

        //[ShellCommand("sync", "Run synchronization test")]
        internal static int AppMain(Parameters! config)
        {
            mutex = new Mutex();
            autoResetEvent = new AutoResetEvent(false);
            manualResetEvent = new ManualResetEvent(true);
            syncEvent = new AutoResetEvent(false);

            Thread t1 = new Thread(new ThreadStart(SyncThread));
            t1.Start();

            Console.WriteLine("[1] Acquiring mutex...");
            mutex.WaitOne();
            Console.WriteLine("[1] Mutex acquired!");
            Console.WriteLine("[1] Releasing mutex...");
            mutex.ReleaseMutex();
            Console.WriteLine("[1] Mutex released.");

            Console.WriteLine("[1] Acquiring mutex...");
            mutex.WaitOne();
            Console.WriteLine("[1] Mutex acquired!");
            Console.WriteLine("[1] Yielding (1/3).");
            Thread.Yield();
            Console.WriteLine("[1] Yielding (2/3).");
            Thread.Yield();
            Console.WriteLine("[1] Yielding (3/3).");
            Thread.Yield();
            Console.WriteLine("[1] Releasing mutex...");
            mutex.ReleaseMutex();
            Console.WriteLine("[1] Mutex released.");

            Console.WriteLine("[1] Waiting on event.");
            autoResetEvent.WaitOne();
            Console.WriteLine("[1] Event set!");

            Console.WriteLine("[1] Setting sync event.");
            syncEvent.Set();

            Console.WriteLine("[1] Waiting on event.");
            autoResetEvent.WaitOne();
            Console.WriteLine("[1] Event set!");

            Console.WriteLine("[1] Waiting on manual event.");
            manualResetEvent.WaitOne();
            Console.WriteLine("[1] Event set!");

            Console.WriteLine("[1] Resetting manual event.");
            manualResetEvent.Reset();

            Console.WriteLine("[1] Setting sync event.");
            syncEvent.Set();

            Console.WriteLine("[1] Waiting on manual event.");
            manualResetEvent.WaitOne();
            Console.WriteLine("[1] Event set!");

            Console.WriteLine("[1] Waiting on manual event.");
            manualResetEvent.WaitOne();
            Console.WriteLine("[1] Event set!");

            return 0;
        }
    }
}
