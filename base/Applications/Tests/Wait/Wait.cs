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
            return Wait.AppMain(this);
        }
    }
    
    public class Wait
    {
        private static WaitHandle[]! handles;
        private static AutoResetEvent! syncEvent1;
        private static AutoResetEvent! syncEvent2;

        public static void WaitThread()
        {
            Console.WriteLine("[2] Waiting for [1].");
            syncEvent1.WaitOne();

            syncEvent2.Set();

            Console.WriteLine("[2] Acquiring mutex.");
            ((!)handles[2]).WaitOne();

            Console.WriteLine("[2] Releasing mutex.");
            ((Mutex!) handles[2]).ReleaseMutex();

            syncEvent2.Set();

            Console.WriteLine("[2] Waiting for [1].");
            syncEvent1.WaitOne();

            Console.WriteLine("[2] Setting 0.");
            ((AutoResetEvent!) handles[0]).Set();

            Console.WriteLine("[2] Waiting for [1].");
            syncEvent1.WaitOne();

            Console.WriteLine("[2] Setting 1.");
            ((ManualResetEvent!) handles[1]).Set();

            Console.WriteLine("[2] Waiting for [1].");
            syncEvent1.WaitOne();

            Console.WriteLine("[2] Setting 0.");
            ((AutoResetEvent!) handles[0]).Set();

            Console.WriteLine("[2] Yielding.");

            Console.WriteLine("[2] Setting 1.");
            ((ManualResetEvent!) handles[1]).Set();

            Console.WriteLine("[2] Done.");
        }

        //[ShellCommand("wait", "Run wait any/all test")]
        internal static int AppMain(Parameters! config)
        {
            AutoResetEvent auto = new AutoResetEvent(false);
            ManualResetEvent manual = new ManualResetEvent(false);
            Mutex mutex = new Mutex();

            handles = new WaitHandle [3] { auto, manual, mutex };
            syncEvent1 = new AutoResetEvent(false);
            syncEvent2 = new AutoResetEvent(false);

            Thread t1 = new Thread(new ThreadStart(WaitThread));
            t1.Start();

            Console.WriteLine("[1] Waiting...");
            int i1 = WaitHandle.WaitAny(handles);
            Console.WriteLine("[1] Got {0}!  (Expected 2.)", i1);

            syncEvent1.Set();

            Console.WriteLine("[1] Waiting for [2].");
            syncEvent2.WaitOne();

            Console.WriteLine("[1] Releasing mutex.");
            mutex.ReleaseMutex();

            Console.WriteLine("[1] Waiting for [2].");
            syncEvent2.WaitOne();

            handles = new WaitHandle [2] { auto, manual };

            syncEvent1.Set();

            Console.WriteLine("[1] Wait any...");
            int i2 = WaitHandle.WaitAny(handles);
            Console.WriteLine("[1] Got {0}!  (Expected 0.)", i2);

            syncEvent1.Set();

            Console.WriteLine("[1] Wait any...");
            int i3 = WaitHandle.WaitAny(handles);
            Console.WriteLine("[1] Got {0}!  (Expected 1.)", i3);

            syncEvent1.Set();

            Console.WriteLine("[1] Wait all...");
            foreach (WaitHandle! handle in handles) {
                handle.WaitOne();
            }
            Console.WriteLine("[1] Got all!");

            Console.WriteLine("[1] Done!");
            return 0;

        }
    }
}
