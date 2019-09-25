///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Threading;
using Microsoft.Singularity.UnitTest;

namespace Microsoft.Singularity.Applications
{
    internal sealed class TestSynchronize
    {
        private static Mutex! mutex;
        private static AutoResetEvent! autoResetEvent;
        private static ManualResetEvent! manualResetEvent;
        private static AutoResetEvent! syncEvent;
        private static Mutex! consoleLock;

        private static void SyncThread()
        {
            Write("[2] Acquiring mutex...");
            mutex.WaitOne();
            Write("[2] Mutex acquired!");
            mutex.ReleaseMutex();
            Write("[2] Mutex released.");

            Thread.Yield();
            Thread.Yield();
            Thread.Yield();
            Thread.Yield();
            Thread.Yield();

            Write("[2] Setting event.");
            autoResetEvent.Set();

            Thread.Yield();
            Thread.Yield();
            Thread.Yield();
            Thread.Yield();
            Thread.Yield();

            Write("[2] Waiting for notification...");
            syncEvent.WaitOne();

            Write("[2] Setting event.");
            autoResetEvent.Set();

            Write("[2] Waiting for notification...");
            syncEvent.WaitOne();

            Write("[2] Setting manual event.");
            manualResetEvent.Set();
        }

        internal static void Run()
        {
            mutex = new Mutex();
            autoResetEvent = new AutoResetEvent(false);
            manualResetEvent = new ManualResetEvent(true);
            syncEvent = new AutoResetEvent(false);
            consoleLock = new Mutex();

            Thread t1 = new Thread(new ThreadStart(SyncThread));
            t1.Start();

            Write("[1] Acquiring mutex...");
            mutex.WaitOne();
            Write("[1] Mutex acquired!");
            Write("[1] Releasing mutex...");
            mutex.ReleaseMutex();
            Write("[1] Mutex released.");

            Write("[1] Acquiring mutex...");
            mutex.WaitOne();
            Write("[1] Mutex acquired!");
            Write("[1] Yielding (1/3).");
            Thread.Yield();
            Write("[1] Yielding (2/3).");
            Thread.Yield();
            Write("[1] Yielding (3/3).");
            Thread.Yield();
            Write("[1] Releasing mutex...");
            mutex.ReleaseMutex();
            Write("[1] Mutex released.");

            Write("[1] Waiting on event.");
            autoResetEvent.WaitOne();
            Write("[1] Event set!");

            Write("[1] Setting sync event.");
            syncEvent.Set();

            Write("[1] Waiting on event.");
            autoResetEvent.WaitOne();
            Write("[1] Event set!");

            Write("[1] Waiting on manual event.");
            manualResetEvent.WaitOne();
            Write("[1] Event set!");

            Write("[1] Resetting manual event.");
            manualResetEvent.Reset();

            Write("[1] Setting sync event.");
            syncEvent.Set();

            Write("[1] Waiting on manual event.");
            manualResetEvent.WaitOne();
            Write("[1] Event set!");

            Write("[1] Waiting on manual event.");
            manualResetEvent.WaitOne();
            Write("[1] Event set!");
        }

        private static void Write(string text)
        {
            consoleLock.WaitOne();
            Console.Write("    " + text);
            consoleLock.ReleaseMutex();
        }
    }
}
