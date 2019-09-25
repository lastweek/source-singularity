///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Perform short (bvt) and long running stress of OutOfMemory
//          behavior of the system.
//

//
// Tests to support:
//
// - Overcommit of heap memory within a SIP
//
//   Create lots of managed array objects until the OS can no
//   longer satisfy the request and terminates the SIP.
//
//
// - Overcommit of stack memory within a SIP
//
//   Implement a recursive function that results in stack overflow
//   and termination of the SIP.
//
// - Overcommit of heap memory within the kernel
//
//    Since we can't directly allocate kernel heap memory,
//    we do this by creating lots of kernel objects that occupy
//    the heap (such as new threads)
//
// - Overcommit kernel heap memory from within the kernel in multiple
//   threads to find races in any resource reservation strategies that
//   may be timing dependent.
//

using System;
using System.Threading;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.UnitTest;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
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

        [Endpoint]
        public readonly TRef<DirectoryServiceContract.Imp:Start> nsRef;

        [BoolParameter( "sip_so", Default=false, HelpMessage="Create Stack Overflow in SIP")]
        internal bool sipSo;

        [BoolParameter( "sip_oom", Default=false, HelpMessage="Create Out Of Memory in SIP")]
        internal bool sipOom;

        [BoolParameter( "kernel_oom", Default=false, HelpMessage="Create Kernel Out Of Memory")]
        internal bool kernelOom;

        [BoolParameter( "kernel_oom_stress", Default=false, HelpMessage="Create Kernel Out Of Memory Stress")]
        internal bool kernelOomStress;

        //
        // The noProcess parameter runs the test without creating a sub-process.
        //
        // Since success for this test is running out of memory and having the SIP
        // die, there is no way to return a success status to a top level test script.
        // The script thinks that the SIP failure due to OOM is a failure of the test.
        //
        // So by default, the tests are run in a sub-process which we can then monitor
        // and return a proper result to the top level test script.
        //
        // This parameter allows the same executable to be used for both parts
        // of the test.
        //
        [BoolParameter( "noprocess", Default=false, HelpMessage="Run directly without a sub-process")]
        internal bool noProcess;

        reflective internal Parameters();

        internal int AppMain() {
            return MemStress.AppMain(this);
        }
    }

    public class MemStress
    {
        internal static int AppMain(Parameters! config)
        {

#if PAGING
            if (true) {
                Console.WriteLine("MemStress does not work on PAGING builds");
                return -1;
            }
#endif
            DumpMemInfo();

            SipMemoryStresser sipms = new SipMemoryStresser();

            if (!config.noProcess) {
                 if (config.sipSo) {
                     sipms.RunTestAsProcess(config, "-sip_so");
                 }
                 else if (config.sipOom) {
                     sipms.RunTestAsProcess(config, "-sip_oom");
                 }
                 else if (config.kernelOom) {
                     sipms.RunTestAsProcess(config, "-kernel_oom");
                 }
                 else if (config.kernelOomStress) {
                     sipms.RunTestAsProcess(config, "-kernel_oom_stress");
                 }
                 else {
                     Console.WriteLine("Usage: MemStress [-sip_oom] [-sip_so] [-kernel_oom] [-kernel_oom_stress]");
                     Console.WriteLine("Must pick one option");
                 }
            }
            else {
                  if (config.sipSo) {
                      sipms.RunSOTest();
                  }
                  else if (config.sipOom) {
                      sipms.RunOOMTest();
                  }
                  else if (config.kernelOom) {
                      sipms.KernelOOMTest();
                  }
                  else if (config.kernelOomStress) {
                      sipms.KernelOOMStress();
                  }
                  else {
                      Console.WriteLine("Usage: MemStress [-sip_oom] [-sip_so] [-kernel_oom] [-kernel_oom_stress]");
                      Console.WriteLine("Must pick one option");
                  }
            }

            return 0;
        }

        public static void DumpMemInfo()
        {
            int result;

            ulong totalMemoryFree = 0;
            ulong totalMemoryInUse = 0;
            ulong kernelHeapInUse = 0;
            ulong kernelStackInUse = 0;
            ulong totalSIPHeapInUse = 0;
            ulong totalSIPStackInUse = 0;
            ulong kernelStackReservation = 0;
            ulong kernelHeapReservation = 0;

            result = MemoryInfoService.MemoryUsageInfo(
                out totalMemoryFree,
                out totalMemoryInUse,
                out kernelHeapInUse,
                out kernelStackInUse,
                out totalSIPHeapInUse,
                out totalSIPStackInUse,
                out kernelStackReservation,
                out kernelHeapReservation
                );

            // TODO: Use standard ErrorCode's
            if (result != 0) {
                Console.WriteLine("Error {0} retrieving MemoryUsageInfo");
            }
            else {
                Console.WriteLine("TotalMemoryFree 0x{0:x8}, TotalMemoryInUse {1:x8}", totalMemoryFree, totalMemoryInUse);
                Console.WriteLine("KernelHeapInUse {0:x8}, KernelStackInUse {1:x8}", kernelHeapInUse, kernelStackInUse);
                Console.WriteLine("TotalSIPHeapInUse {0:x8}, TotalSIPStackInUse {1:x8}", totalSIPHeapInUse, totalSIPStackInUse);
                Console.WriteLine("KernelStackReservation {0:x8}, KernelHeapReservation {1:x8}", kernelStackReservation, kernelHeapReservation);
                Console.WriteLine("");
            }
        }
    }

    public class SipMemoryStresser
    {
        //
        // Run out of memory test, eventually terminates the SIP due
        // to fail fast.
        //
        internal void RunTestAsProcess(Parameters! config, string test) {

            Process p = null;

            //
            // Create a subprocess run of "memstress -testparameter"
            //
            string[] args = new string[3];
            args[0] = "memstress";
            args[1] = test;
            args[2] = "-noprocess";

            Console.WriteLine("Creating subprocess memstress {0} -noprocess", test);

            try {
                p = ProcessLauncher.CreateSubProcess(config, args);
            }
            catch (Exception e) {
                Console.WriteLine("Exception from CreateSubProcess: " + e.Message);
                return;
            }

            if (p == null) {
                Console.WriteLine("Error creating process");
                return;
            }

            Console.WriteLine("Process returned with ExitCode={0}", p.ExitCode);
        }

        public void RunOOMTest() {

            object[] TopLevel;
            object[] tmp;

            TopLevel = new Object[1];

            //
            // Currrently the test handles the OOM exception showing
            // that this works. Additional testing should create multiple
            // threads and have OOM failures at random places in the runtime
            // without try/except handlers so we can test the case when
            // the exception bubbles up to the top of the stack.
            //
            try {
                for (int count = 65535;; count *= 2) {

                      tmp = new object[count];

                      tmp[0] = TopLevel;
                      TopLevel = tmp;

                      for (int i = 1; i < count; i++) {
                          TopLevel[i] = new object[count];
                      }

                      MemStress.DumpMemInfo();
                 }
            }
            catch (OutOfMemoryException e) {
                e=e;
                //Thread.CurrentProcess.Stop(1);
                return;
            }
        }

        // Run stack overflow test, terminates the SIP
        public void RunSOTest() {

            // Test the fail fast path directly
            //Microsoft.Singularity.V1.Services.StackService.StackOverflow();

            RunSOTest();
        }

        //
        // Invoke a kernel heap out of memory condition by creating
        // lots of kernel objects
        //
        public void KernelOOMTest() {

            IdleThread[] threads;

            int threadCount = 1000;

            while (true) {

                System.Console.WriteLine("Creating {0} threads", threadCount);

                threads = new IdleThread[threadCount];
                 if (threads == null) {
                     System.Console.WriteLine("Error allocating Thread[]");
                     return;
                 }

                 for (int i = 0; i < threadCount; i++) {
                     threads[i] = new IdleThread(i);
                     if (threads[i] == null) {
                         System.Console.WriteLine("Error creating thread");
                         return;
                     }
                 }

                 // Start them running
                 for (int i = 0; i < threadCount; i++) {
                     ((!)threads[i]).RunThread();
                 }
            }
        }

        //
        // Use multiple threads to stress the system and induce
        // kernel heap OOM to test the ability for the system
        // to remain running.
        //
        public void KernelOOMStress() {
            Console.WriteLine("Not implemented yet");
            return;
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

    //
    // Implementation classes represent different thread creation
    // parameters, and actions
    //

    //
    // This creates an idle thread that just waits.
    //
    // The goal is to create lots of kernel objects and use up
    // memory, not jam the system with many threads until
    // it stalls.
    //
    public class IdleThread : ThreadRunner
    {
        private long argValue;

        public IdleThread(long arg) : base() {
            argValue = arg;
        }

        public override void ThreadMain() {

            // Wait for ever
            while (true) {
                Thread.Sleep(60*60*1000);
            }

            // This exits the thread
            return;
        }
    }
}


