///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Singularity micro-benchmark program.
//
using Microsoft.Singularity;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.V1.Threads;
using System;
using System.Runtime.CompilerServices;
using System.Diagnostics;
using System.Threading;

using Microsoft.Singularity.Channels;
using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(HelpMessage="Show attributes associated with a file", DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [BoolParameter( "q", Default=false, HelpMessage="Quiet Mode.")]
        internal bool quietMode;

        [LongParameter( "r", Default=1, HelpMessage="Repetition count.")]
        internal long repetitions;

        reflective internal Parameters();

        internal int AppMain() {
            return SharedHeapBench.AppMain(this);
        }
    }
    //
    // The goal of this test is to time how long it takes to
    // create a process.
    //
    public class SharedHeapBench
    {
        internal static int AppMain(Parameters! config)
        {
            int iterations = 10000;

            Console.Write("\nTime alloc/free ops in the shared heap\n\n");

            TimeCycle(10, iterations);

            Thread.Sleep(1000);

            TimeCycle(100, iterations);

            Thread.Sleep(1000);

            TimeCycle(1000, iterations);

            Thread.Sleep(1000);

            TimeCycle(10000, iterations);

            return 0;
        }

        //
        // The goal of this routine is to focus on the shared heap operations
        // themselves.  So we allocate and then free the same amount of memory
        // repeatedly, which (for small region allocations) won't cause us to
        // go to the Page manager in steady state.
        //
        public static void TimeCycle(int bytes, int iterations)
        {

            ulong before = Processor.CycleCount;

            for (int loop = 0; loop < iterations; loop++) {
                    SharedHeapService.Allocation *mem;

                    mem = (SharedHeapService.Allocation *)
                        SharedHeapService.Allocate((UIntPtr)bytes, typeof(byte).GetSystemType(), 0);
                    SharedHeapService.Free(mem);
            }

            ulong after = Processor.CycleCount;

            //
            // Tell the world.
            //
            Console.Write("\nTested {0} alloc/free iterations of {1} bytes\n",
                          iterations, bytes);
            Console.Write("Total cycles: {0}\n", after - before);
            Console.Write("\n\n");
        }
    }
}
