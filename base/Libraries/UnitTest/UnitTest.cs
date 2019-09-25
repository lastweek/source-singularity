///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   UnitTest.cs
//
//  Note:
//

using System;
using System.Collections;
using System.Threading;

namespace Microsoft.Singularity.UnitTest
{
    public sealed class UnitTest
    {
        public enum Result
        {
            Passed = 0,
            Failed = 1
        }

        public delegate void TestDelegate();

        internal sealed class TestCommand
        {
            private string /*!*/       description;
            private TestDelegate /*!*/ testDelegate;

            internal TestCommand(string /*!*/       description,
                                 TestDelegate /*!*/ testDelegate)
            {
                this.description  = description;
                this.testDelegate = testDelegate;
            }

            internal string Description { get { return description; } }
            internal void Execute()     { testDelegate(); }
        }

        private static ArrayList! tests    = new ArrayList();
        private static object    classLock = new object();

        private static int runThreadId;
        private static volatile int  otherThreadExceptions  = 0;
        private static volatile bool expectAssertionFailure = false;

        public static void Add(string /*!*/       description,
                               TestDelegate /*!*/ test)
        {
            tests.Add(new TestCommand(description, test));
        }

        public static void Clear()
        {
            tests.Clear();
        }

        public static void ExpectNextAssertionFails()
        {
            lock (classLock) {
                UnitTest.expectAssertionFailure = true;
            }
        }

        public static void ExpectNextAssertionPasses()
        {
            lock (classLock) {
                UnitTest.expectAssertionFailure = false;
            }
        }

        public static Result Run(bool stopOnFailure)
        {
            runThreadId = GetCurrentThreadId();

            int failures = 0;

            foreach (TestCommand! tc in tests) {
                Result r = Result.Passed;
                try {
                    Console.Write("Running test {0}...", tc.Description);
                    lock (classLock) {
                        UnitTest.otherThreadExceptions = 0;
                    }
                    tc.Execute();
                    lock (classLock) {
                        if (UnitTest.otherThreadExceptions == 0) {
                            Console.WriteLine("Passed.");
                        }
                        else {
                            Console.WriteLine("Failed.");
                            r = Result.Failed;
                        }
                    }
                }
                catch (FailedAssertionException fae) {
                    Console.WriteLine("Failed.");
                    Console.WriteLine(fae);
                    r = Result.Failed;
                }
                catch (Exception e) {
                    Console.WriteLine("Failed: Unexpected exception caught.");
                    Console.WriteLine(e);
                    r = Result.Failed;
                }
                if (r == Result.Failed) {
                    failures++;
                    if (stopOnFailure) {
                        break;
                    }
                }
            }
            return (failures == 0) ? Result.Passed : Result.Failed;
        }

        private static int GetCurrentThreadId()
        {
#if SINGULARITY
            return Thread.CurrentThread.GetThreadId();
#else
            return AppDomain.GetCurrentThreadId();
#endif
        }

        internal static void Throw(FailedAssertionException /*!*/ e)
        {
            lock (classLock) {

                if (UnitTest.expectAssertionFailure == true) {
                    UnitTest.expectAssertionFailure = false;
                    return;
                }

                int threadId = GetCurrentThreadId();
                if (threadId != runThreadId) {
                    UnitTest.otherThreadExceptions++;
                    Console.WriteLine("Tester Failure on thread {0}: {1}",
                                      threadId, e);
                }
            }
            throw e;
        }
    }
}
