///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

using System;
using System.Threading;

using Microsoft.Singularity.UnitTest;

namespace Microsoft.Singularity.Applications
{
    /// <remarks>
    /// A test of Monitor.PulseAll.  A collection of threads waits on
    /// a single monitor for a pulse all.
    /// </remarks>
    internal sealed class PulseAllTest
    {
        int waiterCount    = 50;
        int timeoutSeconds = 2;

        int  passedBarrier = 0;
        bool waiterRunning = false;
        volatile bool timedOut      = false;
        volatile bool stop          = false;
        volatile int  generation    = 0;

        ManualResetEvent controllerReady = new ManualResetEvent(false);
        ManualResetEvent finishedEvent   = new ManualResetEvent(false);
        AutoResetEvent   barrierEvent    = new AutoResetEvent(false);
        object           monitor         = new object();
        bool []          visited;

        private static void Yield()
        {
#if SINGULARITY
            Thread.Yield();
#else
            Thread.Sleep(0);
#endif
        }

        public void WatchdogThreadMain()
        {
            TimeSpan delta = TimeSpan.FromSeconds(timeoutSeconds);

            int now  = this.generation;
            int last = 0;
            do {
                last = now;
                if (finishedEvent.WaitOne(delta)) {
                    return;
                }
                Yield();
                now = this.generation;
                if (last == now)
                    DebugStub.Break();      // break if we made no progress
            } while (true);
        }

        public void ControllerThreadMain()
        {
            const int iterations = 1000;

            const int YieldFudge = 50;

            // Signal worker threads to start
            controllerReady.Set();
            Yield();

            for (int i = 1; i <= iterations; i++) {
                barrierEvent.WaitOne();
                // There is a potential
                // race between the last thread reaching the barrier
                // setting the barrierEvent and reaching the Monitor.Wait
                // call.  By yielding a few times we should give the
                // thread enough time to get there.
                for (int n = 0; n < YieldFudge; n++)
                    Yield();
                lock (this.monitor) {
                    // Reset check state
                    this.passedBarrier = 0;
                    for (int j = 0; j < visited.Length; j++) {
                        visited[j] = false;
                    }

                    // Set stop flag if end is reached
                    this.stop = (i == iterations);

                    // Wake up waiters
                    Monitor.PulseAll(this.monitor);
                }
            }
            finishedEvent.Set();
        }

        public void WaiterThreadMain()
        {
            while (!stop) {
                Monitor.Enter(this.monitor);
                try {
                    Assert.True(waiterRunning == false,
                                "Two waiters have monitor.");
                    waiterRunning = true;

                    Assert.False(this.visited[this.passedBarrier],
                                 "Thread already reached barrier.");
                    this.visited[this.passedBarrier] = true;

                    this.passedBarrier++;
                    this.generation++;

                    Assert.LessOrEqual(this.passedBarrier, waiterCount,
                                       "More waiters passed barrier than expected.");

                    if (this.passedBarrier == this.waiterCount) {
                        barrierEvent.Set();
                    }

                    this.waiterRunning = false;
                    Monitor.Wait(this.monitor);
                    this.waiterRunning = true;
                }
                finally {
                    this.waiterRunning = false;
                    Monitor.Exit(this.monitor);
                }
            }
        }

        public void RunTest()
        {
            Thread watchdog =
                new Thread(new ThreadStart(WatchdogThreadMain));
            Thread controller =
                new Thread(new ThreadStart(ControllerThreadMain));

            watchdog.Start();
            controller.Start();

            controllerReady.WaitOne();
            for (int i = 0; i < waiterCount; i++) {
                Thread t = new Thread(new ThreadStart(WaiterThreadMain));
                t.Start();
            }

            while (!controller.Join(TimeSpan.FromMilliseconds(100))) {
                Assert.False(this.timedOut, "Timed out!");
            }
            watchdog.Join();
        }

        public PulseAllTest(int threadCount, int timeoutSeconds)
        {
            this.waiterCount    = threadCount;
            this.timeoutSeconds = timeoutSeconds;
            this.visited        = new bool [threadCount];
        }

        public static void FewThreadsTest()
        {
            (new PulseAllTest(8, 500)).RunTest();
        }

        public static void ManyThreadsTest()
        {
            (new PulseAllTest(50, 500)).RunTest();
        }
    }
}
