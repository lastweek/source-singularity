///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   A test of the Unit testing code.
//

using System;
using System.Collections;
using System.Threading;
using Microsoft.Singularity.UnitTest;

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
            return Test.AppMain(this);
        }
    }
    public class Test
    {
        private static void SimpleChecks()
        {
            Assert.True(true, "Expected true");
            Assert.False(false, "Expected false");
            Assert.Null(null, "Expected null");

            object low  = (object)0;
            object high = (object)1;
            Assert.NonNull(low, "Expected non-null value");
            Assert.SameObject(low, low, "Expected same object");
            Assert.NotSameObject(low, new object(),
                                 "Expected different objects");
            Assert.Equal(low, low,
                         "Expected equal objects");
            Assert.NotEqual(low, high, "Expected unequal objects.");

        }

        // -------------------------------------------------------------------
        // Byte tests
        //
        // Generics would be handy here,
        // but are not crucial as the overloads for binary
        // operators are script generated so we expect them to work
        // irrespective of type.

        internal delegate void BinaryOp(byte a, byte b, string msg);

        internal class WrappedBinaryOp
        {
            byte first;
            byte second;
            string! message;
            BinaryOp! op;

            internal WrappedBinaryOp(byte      first,
                                     byte      second,
                                     string!   message,
                                     BinaryOp! op)
            {
                this.first   = first;
                this.second  = second;
                this.message = message;
                this.op      = op;
            }

            public void Dispatch()
            {
                op(first, second, message);
            }
        }

        private static void TestBadByteOperations()
        {
            ArrayList ops = new ArrayList();

            int oldPasses = Assert.Passes;
            int oldFailures = Assert.Failures;

            ops.Add(new WrappedBinaryOp(0, 1, "Equal",
                                     new BinaryOp(Assert.Equal)));
            ops.Add(new WrappedBinaryOp(0, 1, "Greater",
                                     new BinaryOp(Assert.Greater)));
            ops.Add(new WrappedBinaryOp(0, 0, "Greater",
                                     new BinaryOp(Assert.Greater)));
            ops.Add(new WrappedBinaryOp(0, 1, "GreaterOrEqual",
                                     new BinaryOp(Assert.GreaterOrEqual)));
            ops.Add(new WrappedBinaryOp(1, 0, "Less",
                                     new BinaryOp(Assert.Less)));
            ops.Add(new WrappedBinaryOp(0, 0, "Less",
                                     new BinaryOp(Assert.Less)));
            ops.Add(new WrappedBinaryOp(1, 0, "LessOrEqual",
                                     new BinaryOp(Assert.LessOrEqual)));

            foreach (WrappedBinaryOp! op in ops) {
                bool missedException = false;
                try {
                    op.Dispatch();
                    missedException = true;
                }
                catch (FailedAssertionException) {
                    missedException = false;
                }
                if (missedException) {
                    throw new
                        FailedAssertionException("Unexpected test pass.");
                }
            }
            Assert.Equal(oldPasses, Assert.Passes, "Assert Passes");
            Assert.Equal(oldFailures + 7, Assert.Failures, "Assert Failures");
        }

        private static void TestByteOperations()
        {
            int oldPasses = Assert.Passes;
            Assert.Equal((byte)0, (byte)0, "byte Equal Test");
            Assert.Greater((byte)1, (byte)0, "byte Greater Test");
            Assert.GreaterOrEqual((byte)1, (byte)0,
                                  "byte GreaterOrEqual Test");
            Assert.GreaterOrEqual((byte)0, (byte)0,
                                  "byte GreaterOrEqual Test 2");
            Assert.Less((byte)0, (byte)1, "byte Less Test");
            Assert.LessOrEqual((byte)0, (byte)1,
                                  "byte LessOrEqual Test");
            Assert.LessOrEqual((byte)0, (byte)0,
                               "byte LessOrEqual Test 2");
            Assert.Equal(oldPasses + 7, Assert.Passes, "Assert Passes");
        }

        private static void TestWatchDog()
        {
            const int deferrals       = 20;
            TimeSpan  deferPeriod     = TimeSpan.FromMilliseconds(250);
            TimeSpan  halfDeferPeriod =
                TimeSpan.FromTicks(deferPeriod.Ticks / 2);

            WatchDogTimer wd = new WatchDogTimer(deferPeriod);

            wd.Start();
            Assert.True(wd.Running, "Watch dog failed to start");

            wd.Stop();
            Assert.False(wd.Running, "Watch dog failed to stop");

            wd.Start();
            Assert.True(wd.Running, "Watch dog failed to restart");

            Thread.Sleep(halfDeferPeriod);

            for (int i = 0; i < deferrals; i++) {
                wd.Defer();
                Thread.Sleep(halfDeferPeriod);
                Assert.True(wd.Running,
                            "Watch dog timer stopped unexpectedly.");
            }

            // About to deliberately timeout watchdog
            // so announce upcoming assertion failure from watchdog.
            UnitTest.ExpectNextAssertionFails();
            Thread.Sleep(deferPeriod);
            Thread.Sleep(deferPeriod);
            UnitTest.ExpectNextAssertionPasses();

            Assert.False(wd.Running, "Watch dog timer did not timeout.");

            wd.Start();
            wd.Start();
            wd.Start();
            wd.Stop();
            wd.Stop();
        }

        internal static int AppMain(Parameters! config)
        {
            UnitTest.Add("SimpleChecks",
                         new UnitTest.TestDelegate(SimpleChecks));
            UnitTest.Add("TestByteOperations",
                         new UnitTest.TestDelegate(TestByteOperations));
            UnitTest.Add("TestBadByteOperations",
                         new UnitTest.TestDelegate(TestBadByteOperations));
            if (UnitTest.Run(true) != UnitTest.Result.Passed)
                return -1;

            UnitTest.Clear();

            // The following test "fails" because
            // it needs to see the watchdog timeout.
            UnitTest.Add("TestWatchDog",
                         new UnitTest.TestDelegate(TestWatchDog));
            UnitTest.Run(true);

            return 0;
        }
    }
}
