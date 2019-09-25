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
    /// <summary>
    ///     Test cases for manual reset event class
    /// </summary>
    internal sealed class TestManualResetEvent
    {
        internal static TestLog Expect;
        private const int MaxWaiters = 16;
        private static ManualResetEvent evt, evt1, evt2, evt3, evt4;
        private static readonly TimeSpan trivialTestWaitTime = TimeSpan.FromMilliseconds(100);
        private static int counter;
        private static int readyCount;

        internal static void Run()
        {
            TestTrivialReset();
            TestTrivialSet();
            TestThreadSet();
            TestThreadReset();
            TestMultipleWaitOneWithInitialSet();
            TestMultipleWaitOneWithInitialReset();
            TestDeadlock();

            ///TODO: harden kernel code so it doesn't crash on this test, then enable the test
            //TestDispose();
        }

        /// <summary>
        ///     After the event is reset, test to make sure WaitOne timeout in the same thread
        /// </summary>
        private static void TestTrivialReset()
        {
            Console.Write("    test trivial reset");

            //
            // reset by constructor
            //
            evt = new ManualResetEvent(false);
            Console.Write('.');
            bool ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout again");
                return;
            }
            evt.Close();

            //
            // reset by constructor and Reset()
            //
            evt = new ManualResetEvent(false);
            evt.Reset();
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout again");
                return;
            }
            evt.Close();

            //
            // set by constructor and then explicitly Reset()
            //
            evt = new ManualResetEvent(true);
            evt.Reset();
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout again");
                return;
            }
            evt.Close();

            //
            // Set() and Reset() several times
            //
            evt = new ManualResetEvent(true);
            evt.Set();
            evt.Reset();
            evt.Set();
            evt.Reset();
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout again");
                return;
            }
            evt.Close();

            evt = null;
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     After the event is set, test to make sure WaitOne succeed in the same thread
        /// </summary>
        private static void TestTrivialSet()
        {
            Console.Write("    test Trivial set ");

            //
            // set by constructor
            //
            evt = new ManualResetEvent(true);
            Console.Write('.');
            bool ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed again");
                return;
            }
            evt.Close();

            //
            // set by constructor then explicitly Set()
            //
            evt = new ManualResetEvent(true);
            evt.Set();
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed again");
                return;
            }
            evt.Close();

            //
            // reset by constructor then explicitly Set()
            //
            evt = new ManualResetEvent(false);
            evt.Set();
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed again");
                return;
            }
            evt.Close();

            //
            // reset and set several times
            //
            evt = new ManualResetEvent(false);
            evt.Set();
            evt.Reset();
            evt.Set();
            evt.Reset();
            evt.Set();
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed again");
                return;
            }
            evt.Close();

            evt = null;
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Set the event, and then WaitOne from different thread. The wait should succeed.
        /// </summary>
        private static void TestThreadSet()
        {
            Console.Write("    test thread set ");
            evt = new ManualResetEvent(true);

            Thread t = new Thread(new ThreadStart(WaiterMain));
            t.Start();
            t.Join();

            Console.Write('.');
            evt.WaitOne();
            evt.Reset();

            Console.Write('.');
            bool ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout");
                return;
            }

            evt.Close();
            evt = null;
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Reset the event and then WaitOne from different thread. The wait should timeout
        /// </summary>
        private static void TestThreadReset()
        {
            Console.Write("    test thread reset ");
            evt = new ManualResetEvent(false);
            counter = 0;

            Thread t = new Thread(new ThreadStart(NoSignalWaiterMain));
            t.Start();
            Console.Write('.');
            t.Join();

            // wait should timeout and therefore the counter should be 1
            if (Thread.VolatileRead(ref counter) != 1) {
                Expect.Fail("wait should timeout");
                return;
            }

            Console.Write('.');
            evt.Set();
            evt.WaitOne();

            evt.Close();
            evt = null;
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     test multiple threads WaitOne() on the same event which is initially set
        /// </summary>
        private static void TestMultipleWaitOneWithInitialSet()
        {
            Console.Write("    test multiple wait one with initial set ");
            evt = new ManualResetEvent(true);

            for (int n = 1; n < MaxWaiters; n++) {
                Console.Write('.');
                Thread[] threads = new Thread[n];
                for (int i = 0; i < n; i++) {
                    threads[i] = new Thread(new ThreadStart(WaiterMain));
                    ((!)threads[i]).Start();
                }
                for (int i = 0; i < n; i++) {
                    ((!)threads[i]).Join();
                }
            }

            evt.Close();
            evt = null;
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     test multiple threads WaitOne() on the same event which is initially reset
        ///     the master thread then 
        /// </summary>
        private static void TestMultipleWaitOneWithInitialReset()
        {
            Console.Write("    test multiple wait one with initial reset ");
            evt = new ManualResetEvent(false);

            for (int n = 1; n < MaxWaiters; n++) {
                // reset counter
                counter = 0;
                readyCount = 0;
                // reset event
                evt.Reset();

                Console.Write('.');
                Thread[] threads = new Thread[n];
                for (int i = 0; i < n; i++) {
                    threads[i] = new Thread(new ThreadStart(WaiterMain));
                    ((!)threads[i]).Start();
                    Thread.Yield();
                }

                // wait for all threads to be ready
                while (true) {
                    if (Thread.VolatileRead(ref readyCount) == n) {
                        break;
                    }
                    Thread.Yield();
                }

                // make sure no wait leaking
                Expect.Equal(Thread.VolatileRead(ref counter), 0,
                    "Detected event wait leaking!");

                evt.Set();
                for (int i = 0; i < n; i++) {
                    ((!)threads[i]).Join();
                }
            }

            evt.Close();
            evt = null;
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Test dead lock situation where two threads each waits the other to set an event 
        /// </summary>
        private static void TestDeadlock()
        {
            Console.Write("    test deadlock ...");
            evt = new ManualResetEvent(false);
            evt3 = new ManualResetEvent(false);
            evt4 = new ManualResetEvent(false);
            counter = 0;
            Thread t1 = new Thread(new ThreadStart(DeadlockMain1));
            Thread t2 = new Thread(new ThreadStart(DeadlockMain2));
            t1.Start();
            t2.Start();

            evt3.WaitOne();
            evt4.WaitOne();
            evt.Set();

            t1.Join();
            t2.Join();

            // wait in both thread should timeout, therefore the counter should be 2
            if (Thread.VolatileRead(ref counter) != 2) {
                Expect.Fail("expecting deadlock");
                return;
            }

            evt.Close();
            evt = null;
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Test the scenario where we dispose an event object then wait on it.
        /// </summary>
        private static void TestDispose()
        {
            Console.Write("    test dispose ");
            evt = new ManualResetEvent(false);
            evt.Close();
            try {
                evt.WaitOne();
            }
            catch (Exception ex) {
                Console.WriteLine(ex.ToString());
                return;
            }
            Expect.Fail("expecting exception on disposed object");
        }

        /// <summary>
        ///     Thread entry point to test waiting on an event.
        ///     increment the counter only if the wait timeout
        /// </summary>
        private static void NoSignalWaiterMain()
        {
            bool ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                // increment counter if the wait timeout
                Interlocked.Increment(ref counter);
            }
        }

        /// <summary>
        ///     Thread entry point to test waiting on an event.
        ///     increment readyCount before wait begins and increment counter after wait succeeds
        /// </summary>
        private static void WaiterMain()
        {
            Interlocked.Increment(ref readyCount);
            evt.WaitOne();
            Interlocked.Increment(ref counter);
        }

        /// <summary>
        ///     Thread entry point to test dead lock
        ///     increment counter if wait timeout
        /// </summary>
        private static void DeadlockMain1()
        {
            evt1 = new ManualResetEvent(false);
            evt3.Set();
            evt.WaitOne();
            bool ret = evt2.WaitOne(TimeSpan.FromSeconds(1));
            if (!ret) {
                // increment counter if the wait timeout
                Interlocked.Increment(ref counter);
            }
        }

        /// <summary>
        ///     Thread entry point to test dead lock
        ///     increment counter if wait timeout
        /// </summary>
        private static void DeadlockMain2()
        {
            evt2 = new ManualResetEvent(false);
            evt4.Set();
            evt.WaitOne();
            bool ret = evt1.WaitOne(TimeSpan.FromSeconds(1));
            if (!ret) {
                // increment counter if the wait timeout
                Interlocked.Increment(ref counter);
            }
        }
    }
}
