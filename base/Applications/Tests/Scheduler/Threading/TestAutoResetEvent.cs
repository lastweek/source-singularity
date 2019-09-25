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
    ///     Test cases for auto reset event class
    /// </summary>
    internal sealed class TestAutoResetEvent
    {
        internal static TestLog Expect;
        private const int MaxWaiters = 16;
        private static AutoResetEvent evt, evt1, evt2, evt3, evt4;
        private static ManualResetEvent evtGate;
        private static readonly TimeSpan trivialTestWaitTime = TimeSpan.FromMilliseconds(100);
        private static int counter;
        private static int readyCount;

        internal static void Run()
        {
            TestTrivialReset();
            TestTrivialSet();
            TestThreadSet();
            TestThreadReset();
            TestMultipleWaitOne();
            TestSetAll();
            TestDeadlock();

            ///TODO: harden kernel code so it doesn't crash on this test, then enable the test
            //TestDispose();
        }

        /// <summary>
        ///     After the event is reset, test to make sure WaitOne timeout in the same thread
        /// </summary>
        private static void TestTrivialReset()
        {
            Console.Write("    test trivial reset ");

            //
            // reset by constructor
            //
            evt = new AutoResetEvent(false);
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
            evt = new AutoResetEvent(false);
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
            evt = new AutoResetEvent(true);
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
            evt = new AutoResetEvent(true);
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
            evt = new AutoResetEvent(true);
            Console.Write('.');
            bool ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout");
                return;
            }
            evt.Close();

            //
            // set by constructor then explicitly Set()
            //
            evt = new AutoResetEvent(true);
            evt.Set();
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout");
                return;
            }
            evt.Close();

            //
            // reset by constructor then explicitly Set()
            //
            evt = new AutoResetEvent(false);
            evt.Set();
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (!ret) {
                Expect.Fail("wait should succeed");
                return;
            }
            Console.Write('.');
            ret = evt.WaitOne(trivialTestWaitTime);
            if (ret) {
                Expect.Fail("wait should timeout");
                return;
            }
            evt.Close();

            //
            // reset and set several times
            //
            evt = new AutoResetEvent(false);
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
            if (ret) {
                Expect.Fail("wait should timeout");
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
            evt = new AutoResetEvent(true);

            Thread t = new Thread(new ThreadStart(WaiterMain));
            t.Start();
            t.Join();

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
            evt = new AutoResetEvent(false);
            counter = 0;

            Thread t = new Thread(new ThreadStart(NoSignalWaiterMain));
            t.Start();
            Console.Write('.');
            t.Join();
            
            // wait should timeout and therefore counter should be 1
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
        ///     multiple threads WaitOne on a reset auto reset event and master thread
        ///     calls SetAll. all waiters should be unblocked by it.
        /// </summary>
        private static void TestSetAll()
        {
            Console.Write("    test set all ");
            readyCount = 0;
            counter = 0;

            //
            // multiple threads WaitOne on a reset auto reset event and master thread
            // calls SetAll. all waiters should be unblocked by it.
            //
            Console.Write('.');
            evt = new AutoResetEvent(false);
            Thread[] threads = new Thread[MaxWaiters];
            for (int i = 0; i < threads.Length; i++) {
                threads[i] = new Thread(new ThreadStart(WaiterMain));
                ((!)threads[i]).Start();
                Thread.Yield();
            }

            // wait for all threads to be ready
            for (int t = 0; t < 50; t++) {
                if (Thread.VolatileRead(ref readyCount) == MaxWaiters) {
                    break;
                }
                Thread.Sleep(100);
            }
            evt.SetAll();

            for (int i = 0; i < threads.Length; i++) {
                ((!)threads[i]).Join();
            }
            if (Thread.VolatileRead(ref counter) != MaxWaiters) {
                Expect.Fail("unexpected counter");
                return;
            }
            evt.Close();

            //
            // now multiple threads wait on the same event after SetAll, they should 
            // all timeout except one
            //
            Console.Write('.');
            counter = 0;
            evt = new AutoResetEvent(false);
            evt.SetAll();
            threads = new Thread[MaxWaiters];
            for (int i = 0; i < threads.Length; i++) {
                threads[i] = new Thread(new ThreadStart(NoSignalWaiterMain));
                ((!)threads[i]).Start();
                Thread.Yield();
            }
            for (int i = 0; i < threads.Length; i++) {
                ((!)threads[i]).Join();
            }

            // all waiter except one should timeout, therefore counter should be
            // number of waiters minus one
            if (Thread.VolatileRead(ref counter) != (MaxWaiters - 1)) {
                Expect.Fail("unexpected counter");
                return;
            }
            evt.Close();

            Console.WriteLine("OK");
        }

        /// <summary>
        ///     test multiple threads WaitOne() on the same event while the master
        ///     thread call Set one at a time.
        /// </summary>
        private static void TestMultipleWaitOne()
        {
            Console.Write("    test multiple wait one ");
            evt = new AutoResetEvent(true);

            for (int n = 1; n < MaxWaiters; n++) {
                // reset counter
                counter = 0;
                int previousCounter = 0;
                int numSet = 0;
                bool timeout = true;
                evt.Set();

                for (int i = 0; i < n; i++) {
                    new Thread(new ThreadStart(WaiterMain)).Start();
                }

                // Call Set() one at a time after observing a change in the counter
                for (int t = 0; t < 50; t++) {
                    int currentCounter = Thread.VolatileRead(ref counter);
                    if (currentCounter == n) {
                        if (numSet != n - 1) {
                            Expect.Fail(string.Format(
                                "unexpected number of Set() with {0} threads", n));
                            return;
                        }
                        timeout = false;
                        Console.Write('.');
                        break;
                    }
                    else if (previousCounter != currentCounter) {
                        previousCounter = currentCounter;
                        evt.Set();
                        numSet++;
                        Thread.Yield();
                    }
                    else {
                        Thread.Sleep(100);
                    }
                }

                if (timeout) {
                    Expect.Fail(string.Format("timed out with {0} threads", n));
                    return;
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
            evtGate = new ManualResetEvent(false);
            evt3 = new AutoResetEvent(false);
            evt4 = new AutoResetEvent(false);
            counter = 0;
            Thread t1 = new Thread(new ThreadStart(DeadlockMain1));
            Thread t2 = new Thread(new ThreadStart(DeadlockMain2));
            t1.Start();
            t2.Start();

            evt3.WaitOne();
            evt4.WaitOne();
            evtGate.Set();

            t1.Join();
            t2.Join();

            // wait in both thread should timeout, therefore the counter should be 2
            if (Thread.VolatileRead(ref counter) != 2) {
                Expect.Fail("expecting deadlock");
                return;
            }

            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Test the scenario where we dispose an event object then wait on it.
        /// </summary>
        private static void TestDispose()
        {
            Console.Write("    test dispose ");
            evt = new AutoResetEvent(false);
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
            evt1 = new AutoResetEvent(false);
            evt3.Set();
            evtGate.WaitOne();
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
            evt2 = new AutoResetEvent(false);
            evt4.Set();
            evtGate.WaitOne();
            bool ret = evt1.WaitOne(TimeSpan.FromSeconds(1));
            if (!ret) {
                // increment counter if the wait timeout
                Interlocked.Increment(ref counter);
            }
        }
    }
}
