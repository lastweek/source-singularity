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
    /// <remarks>
    ///     Test synchronization objects.
    /// </remarks>
    [TestClass]
    public class ThreadingTest : TestClass
    {
        [TestMethod]
        public void ManualResetEventTest()
        {
            TestManualResetEvent.Expect = Expect;
            TestManualResetEvent.Run();
        }

        [TestMethod]
        public void AutoResetEventTest()
        {
            TestAutoResetEvent.Expect = Expect;
            TestAutoResetEvent.Run();
        }

        [TestMethod]
        public void MutexTest()
        {
            TestMutex.Expect = Expect;
            TestMutex.Run();
        }

        [TestMethod]
        public void WaitAnyTest()
        {
            TestWaitAny.Expect = Expect;
            TestWaitAny.Run();
        }

        [TestMethod]
        public void SyncTest()
        {
            Console.WriteLine("    synchronization between 2 threads...");
            TestSynchronize.Run();
            Console.WriteLine("    ...OK");
        }
    }
}
