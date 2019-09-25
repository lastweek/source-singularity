///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Perform short (bvt) and long running stress of multiprocessor
//          sensitive areas of the system. Used MonitorTest.cs as an
//          application template
//

using System;
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

        [LongParameter("cpucount", Default=2, HelpMessage="CPU Count for test")]
        internal long cpuCount;

        [LongParameter("passcount", Default=10, HelpMessage="Pass Count for test")]
        internal long passCount;

        reflective internal Parameters();

        internal int AppMain() {
            return MpStress.AppMain(this);
        }
    }

    public class MpStress
    {
        internal static int AppMain(Parameters! config)
        {
            int result;

            Console.WriteLine("Running MpStress for CPU Count {0}", config.cpuCount);

            ThreadTest tt = new ThreadTest();

            result = tt.RunTest(config.cpuCount, config.passCount);
            if (result != 0) {
                return result;
            }

            return 0;
        }
    }

    public class ThreadTest
    {

        public int RunTest(long cpuCount, long passCount) {

            // Start the thread create/destroy test
            //ThreadTestsThread threadTests = new ThreadTestsThread(cpuCount);

            // Run pulse tests
            PulseTestsThread pulseTests = new PulseTestsThread(cpuCount, passCount);
            pulseTests.RunThread();

            // Start the background threads
            //threadTests.RunThread();

            // Wait for pulse tests to complete
            ((!)pulseTests.Thread).Join();

            return 0;
        }
    }

    //
    // Implementation classes represent different thread creation
    // parameters, and actions
    //

    public class PrintThread : ThreadRunner
    {
         private long argValue;

         public PrintThread(long arg) : base() {
             argValue = arg;
         }

         public override void ThreadMain() {

              //System.Console.WriteLine("PrintThread: Thread {0}, ThreadIndex {1}\n", Thread.CurrentThread.GetThreadId(), argValue);

              // Call some additional "interesting" system calls here in order to disturb
              // the system state, cause lock contention, flesh out races and unprotected code
              // regions, etc.
              //

              // This exits the thread
              //Console.Write("-");
              return;
         }
    }

    public class ThreadTestsThread : ThreadRunner
    {
        private long cpuCount;

        public ThreadTestsThread(long cpuCount) : base() {
            this.cpuCount = cpuCount;
        }

        public override void ThreadMain() {

            const long Timeout = 1000 * 10; // 10 seconds
            long threadCount = 0;
            PrintThread[] threads;

            threadCount = cpuCount * 2;

            //
            // Run forever, process will exit when the ApMain thread
            // is done with the test sequence
            //
            for (;;) {

                 //Console.Write(".");

                 threads = new PrintThread[threadCount];
                 if (threads == null) {
                     System.Console.WriteLine("Error allocating Thread[]");
                     return;
                 }

                 for (int i = 0; i < threadCount; i++) {
                     threads[i] = new PrintThread(i);
                     if (threads[i] == null) {
                         System.Console.WriteLine("Error creating thread");
                         return;
                     }
                 }

                 // Start them running
                 for (int i = 0; i < threadCount; i++) {
                     ((!)threads[i]).RunThread();
                 }

                 TimeSpan timeout = TimeSpan.FromMilliseconds(Timeout);

                 for (int i = 0; i < threadCount; i++) {
                     if (!((!)(((!)threads[i]).Thread)).Join(timeout)) {
                         Console.WriteLine("Timeout waiting for thread exit");
                         return;
                     }
                     //Console.Write("+");
                 }
            }
        }
    }

    public class PulseTestsThread : ThreadRunner
    {
         private long cpuCount;
         private long passes;
         private int  threadCount;
         private int  maxThreadCount;
         private const int threadsPerCpu = 64;

         public PulseTestsThread(long cpuCount, long passes) : base() {
             this.cpuCount = cpuCount;
             this.passes = passes;
             maxThreadCount = threadsPerCpu * (int)cpuCount;

             // Limit max threads, otherwise we will overflow the kernel's thread table
             if (maxThreadCount > 512) {
                 maxThreadCount = 512;
             }
         }

         public override void ThreadMain() {

            System.Console.WriteLine("Running PulseTests: Thread {0}\n", Thread.CurrentThread.GetThreadId());
            Console.Write("passes={0}", passes);
            Console.WriteLine(" cpuCount={0}", cpuCount);

            for (int pass = 0; pass < passes; pass++) {

                Console.WriteLine("pass={0}", pass);

                UnitTest.Clear();
                threadCount = 0;

                for (int i = 0; i < cpuCount; i++) {

                     // 50 threads
                     if (!CheckMaxThreads(50)) {
                         UnitTest.Add("Many Threads PulseAll",
                                       new UnitTest.TestDelegate(PulseAllTest.ManyThreadsTest));
                     }

                     // 8 threads
                     if (!CheckMaxThreads(8)) {
                         UnitTest.Add("Few Threads PulseAll",
                                       new UnitTest.TestDelegate(PulseAllTest.FewThreadsTest));
                     }

                     // 17 threads
                     if (!CheckMaxThreads(17)) {
                         UnitTest.Add("Low-density Pulse",
                                       new UnitTest.TestDelegate(PulseTest.LowDensityTest));
                     }

                     // 32 threads
                     if (!CheckMaxThreads(32)) {
                         UnitTest.Add("Medium-density Pulse",
                                       new UnitTest.TestDelegate(PulseTest.MediumDensityTest));
                     }

                     // 128 threads
                     if (!CheckMaxThreads(128)) {
                         UnitTest.Add("High-density Pulse",
                                       new UnitTest.TestDelegate(PulseTest.HighDensityTest));
                     }
                 }

                 Console.WriteLine("{0} PulseThreads", threadCount);

                 // Wait for the sub-threads to run
                 if (UnitTest.Run(true) != UnitTest.Result.Passed) {
                     Console.WriteLine("PulseTest failed!\n");
                 }
            }

            // This exits the thread
            return;
         }

         // We must keep total thread count at a reasonable level
         // otherwise we overflow the kernel thread table that is
         // hardcoded at 1024. We will set 512 max threads for now.
         private bool CheckMaxThreads(int count)
         {
             if ((count + threadCount) <= maxThreadCount) {
                 threadCount += count;
                 return false;
             }

             return true;
         }
    }

    // Generic class that creates the thread
    public class ThreadRunner
    {
         private Thread thread;

         public ThreadRunner() {
         }

         public Thread Thread {
              get {
                  return thread;
              }
          }

         // Creates thread, returns with it running
         public Thread RunThread() {

             thread = new Thread(new ThreadStart(ThreadMain));

             thread.Start();

             return thread;
         }

         public virtual void ThreadMain() {

             // This exits the thread
             return;
         }
    }
}
