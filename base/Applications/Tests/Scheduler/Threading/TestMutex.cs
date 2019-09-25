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
	internal sealed class TestMutex
	{
        internal static TestLog Expect;
        private static readonly TimeSpan waitTimeout = TimeSpan.FromMilliseconds(100);
        private static Mutex mutex;
        private static ManualResetEvent evtGate;
        private const int numRoundsInContention = 65536;
        private static int counter;
        private static volatile int sum;

        internal static void Run()
        {
            ///TODO: harden kernel code so it doesn't crash on this then enable the test
            //TestIncorrectRelease();

            TestCtor();

            ///TODO: currently mutex supports recursion in kernel but not in applications, 
            ///  add support then enable this test case
            //TestRecursion();
            
            TestContention();

            // there are other mutex related test cases e.g. Tests\MonitorTest that provide more
            // test coverage.
        }

        /// <summary>
        ///     Test two threads both running busy loops grabbing and releasing the same mutex
        /// </summary>
        private static void TestContention()
        {
            Console.Write("    test contention ");

            mutex = new Mutex();
            evtGate = new ManualResetEvent(false);
            Thread t1 = new Thread(new ThreadStart(ContentionThreadMain));
            Thread t2 = new Thread(new ThreadStart(ContentionThreadMain));
            t1.Start();
            Thread.Yield();
            t2.Start();
            Thread.Yield();

            evtGate.Set();
            t1.Join();
            t2.Join();

            Cleanup();
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Thread entry point for contention test. Run a tight loop which acquires the mutex,
        ///     does a little work, then releases it
        /// </summary>
        private static void ContentionThreadMain()
        {
            evtGate.WaitOne();
            for (int i = 0; i < numRoundsInContention; i++) {
                mutex.AcquireMutex();
                Thread.Yield();
                for (int j = 0; j < 1000; j++) {
                    // sum is volatile so this won't be optimized away
                    sum = unchecked(sum + i * j * j / 23);
                }
                if (i % 10000 == 0) {
                    Console.Write('.');
                }
                Thread.Yield();
                mutex.ReleaseMutex();
                Thread.Yield();
            }
        }

        /// <summary>
        ///     Test the situation where we release the mutex without acquiring it first
        /// </summary>
        private static void TestIncorrectRelease()
        {
            Console.Write("    test incorrect release ");
            mutex = new Mutex();
            try {
                mutex.ReleaseMutex();
            }
            catch (InvalidOperationException) {
                Cleanup();
                Console.WriteLine("OK");
                return;
            }
            Expect.Fail("expecting exception");
        }

        /// <summary>
        ///     Test the constructor of Mutex
        /// </summary>
        private static void TestCtor()
        {
            Console.Write("    test constructor ");

            //
            // default ctor: initially owned = false
            //
            Cleanup();
            Console.Write('.');
            mutex = new Mutex();
            Thread thread = new Thread(new ThreadStart(TimeoutWaitMain));
            thread.Start();
            thread.Join();
            if (Thread.VolatileRead(ref counter) != 1) {
                Expect.Fail("expecting wait to succeed");
                return;
            }

            //
            // explicit ctor: initially owned = false
            //
            Cleanup();
            Console.Write('.');
            mutex = new Mutex(false);
            thread = new Thread(new ThreadStart(TimeoutWaitMain));
            thread.Start();
            thread.Join();
            if (Thread.VolatileRead(ref counter) != 1) {
                Expect.Fail("expecting wait to succeed");
                return;
            }

            //
            // explicit ctor: initially owned = true
            //
            Cleanup();
            Console.Write('.');
            mutex = new Mutex(true);
            thread = new Thread(new ThreadStart(TimeoutWaitMain));
            thread.Start();
            thread.Join();
            if (Thread.VolatileRead(ref counter) != 0) {
                Expect.Fail("expecting wait to timeout");
                return;
            }

            //
            // explicit ctor: initially owned = true, then explicitly release
            //
            Cleanup();
            Console.Write('.');
            mutex = new Mutex(true);
            mutex.ReleaseMutex();
            thread = new Thread(new ThreadStart(TimeoutWaitMain));
            thread.Start();
            thread.Join();
            if (Thread.VolatileRead(ref counter) != 1) {
                Expect.Fail("expecting wait to succeed");
                return;
            }

            //
            // explicit ctor: initially owned = false, then explicitly acquire
            //
            Cleanup();
            Console.Write('.');
            mutex = new Mutex(false);
            mutex.WaitOne();
            thread = new Thread(new ThreadStart(TimeoutWaitMain));
            thread.Start();
            thread.Join();
            if (Thread.VolatileRead(ref counter) != 0) {
                Expect.Fail("expecting wait to timeout");
                return;
            }

            Cleanup();
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Mutex supports recursion: the same thread can Acquire the same mutex
        ///     multiple times successfully
        /// </summary>
        private static void TestRecursion()
        {
            Console.Write("    test recursion ");

            //
            // same number of acquire and release
            //
            Cleanup();
            Console.Write('.');
            mutex = new Mutex();
            mutex.AcquireMutex();
            mutex.AcquireMutex();
            mutex.AcquireMutex();
            mutex.ReleaseMutex();
            mutex.ReleaseMutex();
            mutex.ReleaseMutex();
            Thread thread = new Thread(new ThreadStart(TimeoutWaitMain));
            thread.Start();
            thread.Join();
            if (Thread.VolatileRead(ref counter) != 1) {
                Expect.Fail("expecting wait to succeed");
                return;
            }

            //
            // same number of acquire and release, with the explicit ctor count as 1
            //
            Cleanup();
            Console.Write('.');
            mutex = new Mutex(true);
            mutex.AcquireMutex();
            mutex.AcquireMutex();
            mutex.ReleaseMutex();
            mutex.ReleaseMutex();
            mutex.ReleaseMutex();
            thread = new Thread(new ThreadStart(TimeoutWaitMain));
            thread.Start();
            thread.Join();
            if (Thread.VolatileRead(ref counter) != 1) {
                Expect.Fail("expecting wait to succeed");
                return;
            }

            //
            // acquire without release, the other thread will wait and timeout
            //
            Cleanup();
            Console.Write('.');
            mutex = new Mutex();
            mutex.AcquireMutex();
            mutex.AcquireMutex();
            mutex.AcquireMutex();
            thread = new Thread(new ThreadStart(TimeoutWaitMain));
            thread.Start();
            thread.Join();
            if (Thread.VolatileRead(ref counter) != 0) {
                Expect.Fail("expecting wait to timeout");
                return;
            }

            //
            // less release than acquire, the other thread will wait and timeout
            //
            Cleanup();
            Console.Write('.');
            mutex = new Mutex();
            mutex.AcquireMutex();
            mutex.AcquireMutex();
            mutex.AcquireMutex();
            mutex.ReleaseMutex();
            mutex.ReleaseMutex();
            thread = new Thread(new ThreadStart(TimeoutWaitMain));
            thread.Start();
            thread.Join();
            if (Thread.VolatileRead(ref counter) != 0) {
                Expect.Fail("expecting wait to timeout");
                return;
            }

            Cleanup();
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     The thread entry point for the waiter.
        ///     increment counter only if the wait is successful
        /// </summary>
        private static void TimeoutWaitMain()
        {
            bool ret = mutex.WaitOne(waitTimeout);
            if (ret) {
                Interlocked.Increment(ref counter);
            }
        }

        /// <summary>
        ///     Dispose the mutex, reset the counter
        /// </summary>
        private static void Cleanup()
        {
            if (mutex != null) {
                mutex.Close();
                mutex = null;
            }
            counter = 0;
        }
    }
}
