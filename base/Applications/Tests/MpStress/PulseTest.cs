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
    /// A class for testing Monitor.Pulse.
    ///
    /// <para> This class creates a group of monitors (Node class) that
    /// a collection of threads then enters, spins, pulses, and exits.
    /// </para>
    /// </remarks>
    internal sealed class PulseTest
    {
        internal class Node
        {
            volatile bool inVisit = false;

            internal void BeginVisit()
            {
                Monitor.Enter(this);
                Assert.False(inVisit, "Node is visited by two threads");
                inVisit = true;
            }

            internal void EndVisit()
            {
                Assert.True(inVisit, "Unpaired visit ending");
                Monitor.Pulse(this);
                inVisit = false;
                Monitor.Exit(this);
            }
        }

        internal sealed class VisitPath
        {
            int [] path;
            int    remainLength;
            int    cycles;

            internal VisitPath(int pathLength)
            {
                this.path         = new int[pathLength];
                this.remainLength = pathLength;
                this.cycles       = 0;
            }

            internal void Initialize()
            {
                // This is a separate method so
                // we can compile compatibly on Win32.  SGC wants
                // the Sing# specific NonDelayed attribute otherwise.
                for (int i = 0; i < this.remainLength; i++) {
                    this.path[i] = i;
                }
            }

            internal int Pick(int randomNumber)
            {
                int n = randomNumber % this.remainLength;
                int r = this.path[n];

                this.remainLength--;
                this.path[n] = this.path[this.remainLength];
                this.path[this.remainLength] = r;

                if (this.remainLength == 0) {
                    this.cycles++;
                    this.remainLength = this.path.Length;
                }
                return r;
            }

            internal int Cycles { get { return this.cycles; } }
        }

        private Node[] nodes;
        private readonly int threadCount;
        private readonly int maxCycles;
        private volatile int startedCount;
        private volatile int finishedCount;
        private volatile int generation;
        private ManualResetEvent finishedEvent;

        private static void Yield()
        {
#if SINGULARITY
            Thread.Yield();
#else
            Thread.Sleep(0);
#endif
        }

        internal void VisitorThreadMain()
        {
            // Wait until all other threads have started
            int threadNumber;
            lock (this) {
                threadNumber = startedCount++;
            }
            while (startedCount != this.threadCount) {
                Yield();
            }

            Random rng     = new Random(threadNumber);
            VisitPath path = new VisitPath(this.nodes.Length);
            path.Initialize();

            while (path.Cycles != this.maxCycles) {
                // Select a node previously unvisited in this cycle
                Node/*!*/ n =  /*^(!)^*/ nodes[path.Pick(rng.Next())];
                n.BeginVisit();

                // Yield up to number of threads to give other
                // threads a chance to run
                int yieldCount = rng.Next(this.threadCount);
                while (yieldCount-- > 0)
                    Yield();

                n.EndVisit();
                // Console.Write("[{0}]", threadNumber);
                this.generation++;
            }

            lock (this) {
                this.finishedCount++;
                if (this.finishedCount == this.threadCount) {
                    this.finishedEvent.Set();
                }
            }
        }

        private void WatchdogThreadMain()
        {
            int last = this.generation;
            for (;;) {
                Thread.Sleep(TimeSpan.FromSeconds(500));
                if (this.finishedCount == this.threadCount) {
                    return;
                }
                int now = this.generation;
                if (last == now)
                    DebugStub.Break();
                last = now;
            }
        }

        internal PulseTest(int numberOfNodes, int numberOfThreads, int iterations)
        {
            this.nodes = new Node[numberOfNodes];
            this.threadCount   = numberOfThreads;
            this.maxCycles     = iterations;
            this.startedCount  = 0;
            this.finishedCount = 0;
            this.finishedEvent = new ManualResetEvent(false);
        }

        private void Initialize()
        {
            for (int i = 0; i < nodes.Length; i++) {
                nodes[i] = new Node();
            }
        }

        internal void RunTest()
        {
            for (int i = 0; i < this.threadCount; i++) {
                (new Thread(new ThreadStart(VisitorThreadMain))).Start();
            }
            Thread watchdog = new Thread(new ThreadStart(WatchdogThreadMain));
            watchdog.Start();

            finishedEvent.WaitOne();
            watchdog.Join();
            Assert.True(Assert.Failures == 0, "Failures within threads.");
        }

        internal static void LowDensityTest()
        {
            PulseTest p = new PulseTest(128, 17, 20);
            p.Initialize();
            p.RunTest();
        }

        internal static void MediumDensityTest()
        {
            PulseTest p = new PulseTest(32, 32, 20);
            p.Initialize();
            p.RunTest();
        }

        internal static void HighDensityTest()
        {
            PulseTest p = new PulseTest(4, 128, 20);
            p.Initialize();
            p.RunTest();
        }
    }
}
