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

using Microsoft.Singularity;
using Microsoft.Singularity.UnitTest;

namespace Microsoft.Singularity.Applications
{
    /// <remarks>
    /// A test of Monitor.PulseAll.  A collection of threads waits on
    /// a single monitor for a pulse all.
    /// </remarks>
    [TestClass]
    public class PulseAllTest : TestClass
    {
        [TestMethod]
        public void FewThreadsTest()
        {
            (new Pulser(8, 2, Expect)).RunTest();
        }

        [TestMethod]
        public void ManyThreadsTest()
        {
            (new Pulser(50, 2, Expect)).RunTest();
        }
    }

    internal sealed class Pulser
    {
        TestLog Expect;

        int waiterCount    = 50;
        int timeoutSeconds = 2;

        int  passedBarrier = 0;
        bool waiterRunning = false;
        volatile bool timedOut      = false;
        volatile bool stop          = false;
        volatile int  generation    = 0;

        ManualResetEvent! controllerReady = new ManualResetEvent(false);
        ManualResetEvent! finishedEvent   = new ManualResetEvent(false);
        AutoResetEvent!   barrierEvent    = new AutoResetEvent(false);
        object!           monitor         = new object();
        bool []!          visited;


        public Pulser(int threadCount, int timeoutSeconds, TestLog expect)
        {
            this.waiterCount    = threadCount;
            this.visited        = new bool [threadCount];
            this.timeoutSeconds = timeoutSeconds;
            this.Expect = expect;
        }

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
            TimeSpan delta = TimeSpan.FromMilliseconds(500);

            int now  = this.generation;
            int last = 0;
            do {
                last = now;
                if (finishedEvent.WaitOne(delta)) {
                    return;
                }
                Yield();
                now = this.generation;
                Expect.NotEqual(last, now, "progress was made in the last cycle");
            } while (true);
        }

        public void ControllerThreadMain()
        {
            const int iterations = 1000;

            const int YieldFudge = 150;

            // Signal worker threads to start
            controllerReady.Set();
            Yield();

            for (int i = 1; i <= iterations; i++) {
                barrierEvent.WaitOne();
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
                    Expect.False(waiterRunning, "Only one waiter is in the monitor");
                    waiterRunning = true;

                    Expect.False(this.visited[this.passedBarrier],
                                 "Thread is before the barrier");
                    this.visited[this.passedBarrier] = true;

                    this.passedBarrier++;
                    this.generation++;

                    Expect.LessOrEqual(this.passedBarrier, waiterCount,
                                       "Not too many waiters passed the barrier");

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
                Expect.False(this.timedOut, "Completed before timeout");
            }
            watchdog.Join();
        }
    }
}
