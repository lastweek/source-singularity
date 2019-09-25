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
    ///     Test cases for WaitHandle.WaitAny()
    /// </summary>
    internal sealed class TestWaitAny
	{
        internal static TestLog Expect;
        private const int numHandles = 7;
        private const int numHandlesStress = 72;
        private static readonly TimeSpan waitTimeout = TimeSpan.FromMilliseconds(100);
        private static WaitHandle[] handles;
        private static ManualResetEvent evtGate;
        private static int counter;
        private static int readyCount;

        internal static void Run()
        {
            ///TODO: harden code path and then enable this test case
            //TestNullArray();

            TestTrivialTimeout();
            TestTrivialSameHandleArray();
            TestTrivialEachPosition();
            TestThreadTimeout();
            TestThreadEachPosition();
            TestThreadMultipleWaitAny();
            TestThreadMixtureSyncObjects();
        }

        /// <summary>
        ///     WaitAny on a mixture of AutoResetEvent, ManualResetEvent, and Mutex
        /// </summary>
        private static void TestThreadMixtureSyncObjects()
        {
            Console.Write("    test thread mixture of sync objects ");

            Cleanup();
            Console.Write('.');
            evtGate = new ManualResetEvent(false);
            handles = new WaitHandle[numHandlesStress];
            for (int i = 0; i < handles.Length; i++) {
                switch(i % 3) {
                    case 0: 
                        // auto reset events, half set and half reset
                        handles[i] = new AutoResetEvent(i % 6 == 0);
                        break;
                    case 1:
                        // mutexes, half initially owned and half not initially owned
                        handles[i] = new Mutex(i % 6 != 1);
                        break;
                    case 2:
                        // manual reset events, all reset
                        handles[i] = new ManualResetEvent(false);
                        break;
                }
            }

            Thread[] threads = new Thread[numHandlesStress];
            for (int i = 0; i < threads.Length; i++) {
                threads[i] = new Thread(new ThreadStart(TimeoutWaitMain));
                ((!)threads[i]).Start();
                Thread.Yield();
            }
            
            // wait for all waiter threads to be ready
            while (true) {
                if (Thread.VolatileRead(ref readyCount) == numHandlesStress) {
                    break;
                }
                Thread.Yield();
            }

            // let the waiter threads go
            evtGate.Set();
            for (int i = 0; i < threads.Length; i++) {
                ((!)threads[i]).Join();
            }

            // half of the mutexes, half of the auto reset events, and all manual reset events 
            // should timeout. therefore the counter is 
            //      numHandlesStress - (numHandlesStress + 3) / 6 * 2
            if (Thread.VolatileRead(ref counter) != 
                    numHandlesStress - (numHandlesStress + 3) / 6 * 2) {
                Expect.Fail(string.Format("unexpected counter {0}", counter));
                return;
            }
            Cleanup();

            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Multiple threads call WaitAny() on an array of wait handles of the same type
        /// </summary>
        private static void TestThreadMultipleWaitAny()
        {
            Console.Write("    test thread multiple wait any ");
            
            //
            // wait on multiple mutexes
            //
            Cleanup();
            Console.Write('.');
            evtGate = new ManualResetEvent(false);
            handles = new WaitHandle[numHandlesStress];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new Mutex();
            }
            Thread[] threads = new Thread[numHandlesStress];
            for (int i = 0; i < threads.Length; i++) {
                threads[i] = new Thread(new ThreadStart(TimeoutWaitMain));
                ((!)threads[i]).Start();
                Thread.Yield();
            }
            // wait for all waiter threads to be ready
            while (true) {
                if (Thread.VolatileRead(ref readyCount) == numHandlesStress) {
                    break;
                }
                Thread.Yield();
            }
            evtGate.Set();
            for (int i = 0; i < threads.Length; i++) {
                ((!)threads[i]).Join();
            }

            if (Thread.VolatileRead(ref counter) != 0) {
                Expect.Fail("unexpected counter");
                return;
            }

            //
            // wait on multiple auto reset events
            //
            Cleanup();
            Console.Write('.');
            evtGate.Reset();
            handles = new WaitHandle[numHandlesStress];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new AutoResetEvent(false);
            }
            threads = new Thread[numHandlesStress];
            for (int i = 0; i < threads.Length; i++) {
                threads[i] = new Thread(new ThreadStart(TimeoutWaitMain));
                ((!)threads[i]).Start();
                Thread.Yield();
            }
            // set half of the events
            for (int i = 0; i < handles.Length; i += 2) {
                ((AutoResetEvent!)handles[i]).Set();
            }

            // wait for all waiter threads to be ready
            while (true) {
                if (Thread.VolatileRead(ref readyCount) == numHandlesStress) {
                    break;
                }
                Thread.Yield();
            }
            evtGate.Set();
            for (int i = 0; i < threads.Length; i++) {
                ((!)threads[i]).Join();
            }

            // half of the events are set, the rest should timeout, therefore the counter
            // should be    numHandlesStress - numHandlesStress / 2
            if (Thread.VolatileRead(ref counter) != numHandlesStress - numHandlesStress / 2) {
                Expect.Fail("unexpected counter");
                return;
            }
            Cleanup();

            Console.WriteLine("OK");
        }

        /// <summary>
        ///     poke each position of WaitAny handles to make sure we don't have blind spot.
        /// </summary>
        private static void TestTrivialEachPosition()
        {
            Console.Write("    test trivial each position ");
            int ret;

            //
            // initialize an array of auto reset events, all set, and call WaitAny
            // multiple times, it should cycle through the array, after the array is
            // thoroughly walked, the next WaitAny should timeout
            //
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new AutoResetEvent(true);
            }
            for (int i = 0; i < handles.Length; i++) {
                Console.Write('.');
                ret = WaitHandle.WaitAny(handles);
                if (ret != i) {
                    Expect.Fail(string.Format("expect wait succeed on handles[{0}]", i));
                    return;
                } 
            }
            Console.Write('.');
            ret = WaitHandle.WaitAny(handles, waitTimeout);
            if (ret != -1) {
                Expect.Fail("wait should timeout");
                return;
            }
            Cleanup();

            //
            // now start with an array of auto reset events all reset,
            // then poke each position at a time, WaitAny should success on that position
            //
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new AutoResetEvent(false);
            }
            for (int i = handles.Length-1; i >= 0; i--) {
                ((AutoResetEvent!)handles[i]).Set();
                Console.Write('.');
                ret = WaitHandle.WaitAny(handles);
                if (ret != i) {
                    Expect.Fail(string.Format("expect wait succeed on handles[{0}]", i));
                    return;
                }
            }
            Console.Write('.');
            ret = WaitHandle.WaitAny(handles, waitTimeout);
            if (ret != -1) {
                Expect.Fail("wait should timeout");
                return;
            }
            Cleanup();

            Console.WriteLine("OK");
        }

        /// <summary>
        ///     poke each position of WaitAny handles and call WaitAny on a different thread
        /// </summary>
        private static void TestThreadEachPosition()
        {
            Console.Write("    test thread each position ");
            Cleanup();

            //
            // initialize an array of auto reset events, all set, and call WaitAny
            // on multiple threads, they should cycle through the array, after the array is
            // thoroughly walked, the next WaitAny should timeout
            //
            Console.Write('.');
            evtGate = new ManualResetEvent(false);
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new AutoResetEvent(true);
            }
            Thread[] threads = new Thread[numHandles];
            for (int i = 0; i < threads.Length; i++) {
                threads[i] = new Thread(new ThreadStart(WaitMain));
                ((!)threads[i]).Start();
            }
            evtGate.Set();
            for (int i = 0; i < threads.Length; i++) {
                ((!)threads[i]).Join();
            }

            // all wait should be successful, therefore counter is 1+2+...+numHandles
            if (Thread.VolatileRead(ref counter) != numHandles * (numHandles + 1) / 2) {
                Expect.Fail("unexpected counter");
                return;
            }
            Console.Write('.');
            int ret = WaitHandle.WaitAny(handles, waitTimeout);
            if (ret != -1) {
                Expect.Fail("wait should timeout");
                return;
            }
            Cleanup();

            //
            // now start with an array of auto reset events all reset,
            // then poke each position at a time, WaitAny should success on that position
            //
            Console.Write('.');
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new AutoResetEvent(false);
            }
            threads = new Thread[numHandles];
            for (int i = 0; i < threads.Length; i++) {
                threads[i] = new Thread(new ThreadStart(WaitMain));
                ((!)threads[i]).Start();
            }
            evtGate.Set();

            for (int i = handles.Length-1; i >= 0; i--) {
                ((AutoResetEvent!)handles[i]).Set();
                Thread.Yield();
            }
            for (int i = 0; i < threads.Length; i++) {
                ((!)threads[i]).Join();
            }
            // all wait should be successful, therefore counter is 1+2+...+numHandles
            if (Thread.VolatileRead(ref counter) != numHandles * (numHandles + 1) / 2) {
                Expect.Fail("unexpected counter");
                return;
            }

            Console.Write('.');
            ret = WaitHandle.WaitAny(handles, waitTimeout);
            if (ret != -1) {
                Expect.Fail("wait should timeout");
                return;
            }
            Cleanup();

            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Thread entry point of the waiter thread.
        ///     Counter is incremented by the successful wait position plus one
        /// </summary>
        private static void WaitMain()
        {
            evtGate.WaitOne();
            int ret = WaitHandle.WaitAny(handles);

            // there is no Interlocked.Add on int :( Do it the hard way
            int oldValue, newValue;
            do {
                oldValue = Thread.VolatileRead(ref counter);
                newValue = oldValue + (ret + 1);
            }
            while (oldValue != Interlocked.CompareExchange(ref counter, newValue, oldValue));
        }

        /// <summary>
        ///     WaitAny on an array of handles where all elements are referening the same instance
        /// </summary>
        private static void TestTrivialSameHandleArray()
        {
            Console.Write("    test trivial same handle array ");

            //
            // same instance of manual reset event
            //
            Console.Write('.');
            ManualResetEvent mevt = new ManualResetEvent(true);
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = mevt;
            }
            int ret = WaitHandle.WaitAny(handles);
            if (ret != 0) {
                Expect.Fail("expect wait succeed on handles[0]");
                return;
            }
            ret = WaitHandle.WaitAny(handles);
            if (ret != 0) {
                Expect.Fail("expect wait succeed on handles[0] again");
                return;
            } 
            Cleanup();

            //
            // same instance of auto reset event
            //
            Console.Write('.');
            AutoResetEvent aevt = new AutoResetEvent(true);
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = aevt;
            }
            ret = WaitHandle.WaitAny(handles);
            if (ret != 0) {
                Expect.Fail("expect wait succeed on handles[0]");
                return;
            }
            ret = WaitHandle.WaitAny(handles, waitTimeout);
            if (ret != -1) {
                Expect.Fail("wait should timeout");
                return;
            }
            Cleanup();


            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Test WaitAny on an array with is null or contains null elements
        /// </summary>
        private static void TestNullArray()
        {
            Console.Write("    test null array ");

            Console.Write('.');
            handles = null;
            bool exception = false;
            try {
                WaitHandle.WaitAny(handles);
            }
            catch (ArgumentNullException) {
                exception = true;
            }
            if (!exception) {
                Expect.Fail("expecting exception");
                return;
            }

            Console.Write('.');
            handles = new WaitHandle[3] { null, null, null };
            exception = false;
            try {
                WaitHandle.WaitAny(handles);
            }
            catch (ArgumentNullException) {
                exception = true;
            }
            if (!exception) {
                Expect.Fail("expecting exception");
                return;
            }

            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Test WaitAny() on an array of unsignaled handles and timeout
        /// </summary>
        private static void TestThreadTimeout()
        {
            Console.Write("    test thread timeout ");

            //
            // timeout on unsignaled auto reset events
            //
            Cleanup();
            Console.Write('.');
            evtGate = new ManualResetEvent(false);
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new AutoResetEvent(false);
            }
            TestThreadTimeoutWorker();

            //
            // timeout on unsignaled manual reset events
            //
            Cleanup();
            Console.Write('.');
            evtGate = new ManualResetEvent(false);
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new ManualResetEvent(false);
            }
            TestThreadTimeoutWorker();
            
            //
            // timeout on owned mutexes
            //
            Cleanup();
            Console.Write('.');
            evtGate.Reset();
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new Mutex();
                ((!)handles[i]).WaitOne();
            }
            TestThreadTimeoutWorker();

            //
            // timeout on owned
            //
            Cleanup();
            Console.Write('.');
            evtGate.Reset();
            handles = new WaitHandle[numHandles];
            for (int i = 0; i < handles.Length; i++) {
                handles[i] = new Mutex(true);
            }
            TestThreadTimeoutWorker();
            
            Cleanup();
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     create threads WaitAny on an array of unsignaled handles, 
        ///     they should all timeout
        /// </summary>
        private static void TestThreadTimeoutWorker()
        {
            Thread[] threads = new Thread[numHandles];
            for (int i = 0; i < threads.Length; i++) {
                threads[i] = new Thread(new ThreadStart(TimeoutWaitMain));
                ((!)threads[i]).Start();
            }
            evtGate.Set();

            for (int i = 0; i < threads.Length; i++) {
                ((!)threads[i]).Join();
            }
            // all wait should timeout, therefore counter == numHandles
            if (Thread.VolatileRead(ref counter) != numHandles) {
                Expect.Fail("unexpected number of timeouts");
            }
        }

        /// <summary>
        ///     Thread entry point for waiter. 
        ///     Increment readyCount before waiting on the gate, then performs
        ///     WaitAny, and increment the counter if wait timeout
        /// </summary>
        private static void TimeoutWaitMain()
        {
            Interlocked.Increment(ref readyCount);
            evtGate.WaitOne();
            int ret = WaitHandle.WaitAny(handles, waitTimeout);
            if (ret == -1) {
                // increment counter only if wait timeout
                Interlocked.Increment(ref counter);
            }
        }

        /// <summary>
        ///     Test WaitAny on an array of unsignaled handles and the wait should timeout
        /// </summary>
        private static void TestTrivialTimeout()
        {
            Console.Write("    test trivial timeout ");

            //
            // wait on unsignaled manual reset event
            //
            Console.Write('.');
            handles = new WaitHandle[3] {
                new ManualResetEvent(false),
                new ManualResetEvent(false),
                new ManualResetEvent(false)
            };
            int ret = WaitHandle.WaitAny(handles, waitTimeout);
            if (ret != -1) {
                Expect.Fail("wait should timeout");
                return;
            }
            Cleanup();

            //
            // wait on unsignaled auto reset event
            //
            Console.Write('.');
            handles = new WaitHandle[3] {
                new AutoResetEvent(false),
                new AutoResetEvent(false),
                new AutoResetEvent(false)
            };
            ret = WaitHandle.WaitAny(handles, waitTimeout);
            if (ret != -1) {
                Expect.Fail("wait should timeout");
                return;
            }
            Cleanup();

            //
            // wait on mixture of unsignaled events
            //
            Console.Write('.');
            handles = new WaitHandle[4] {
                new AutoResetEvent(false),
                new ManualResetEvent(false),
                new AutoResetEvent(false),
                new ManualResetEvent(false)
            };
            ret = WaitHandle.WaitAny(handles, waitTimeout);
            if (ret != -1) {
                Expect.Fail("wait should timeout");
                return;
            }
            Cleanup();

            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Release all wait handles, reset counters
        /// </summary>
        private static void Cleanup()
        {
            if (handles != null) {
                for (int i = 0; i < handles.Length; i++) {
                    if (handles[i] != null) {
                        ((!)handles[i]).Close();
                    }
                }
                handles = null;
            }
            readyCount = 0;
            counter = 0;
        }
    }
}
