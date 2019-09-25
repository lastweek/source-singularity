////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program.
//
using System;
using Microsoft.Singularity.V1.Services;

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
            return ClockTest.AppMain(this);
        }
    }

    public class ClockTest
    {
        //[ShellCommand("clocktest", "Run clock test")]
        internal static int AppMain(Parameters! config)
        {
            Console.WriteLine("CPU TSC as reference for delay yields:");

            for (uint divisor = 512; divisor > 0; divisor >>= 1) {
                ulong deltaTSC = (ulong) (ProcessService.GetCyclesPerSecond() / divisor);

                long  endKernelTicks = 0;
                ulong endTSC;

                long  startKernelTicks = ProcessService.GetUpTime().Ticks;
                ulong startTSC = (ulong) (ProcessService.GetCycleCount());

                ulong finalTSC = startTSC + deltaTSC;

                do {
                    endKernelTicks = ProcessService.GetUpTime().Ticks;
                    endTSC = (ulong) (ProcessService.GetCycleCount());
                } while (endTSC < finalTSC);

                long usKernel = (endKernelTicks - startKernelTicks) / 10;
                ulong usTSC   = 1000000u * (endTSC - startTSC) / (ulong) (ProcessService.GetCyclesPerSecond());
                Console.Write(" Target {0,7} us  TSC {1,7} us  HW {2,7} us\n",
                              1000000 / divisor, (int)usTSC, (int)usKernel);
            }

            Console.WriteLine("\nHW Clock as reference for delay yields:");
            for (uint divisor = 512; divisor > 0; divisor >>= 1) {
                long  endKernelTicks = 0;
                ulong endTSC;

                long  startKernelTicks = ProcessService.GetUpTime().Ticks;
                ulong startTSC = (ulong) (ProcessService.GetCycleCount());

                long finalKernelTicks = startKernelTicks + 10000000 / divisor;

                do {
                    endKernelTicks = ProcessService.GetUpTime().Ticks;
                    endTSC = (ulong) (ProcessService.GetCycleCount());
                } while (endKernelTicks < finalKernelTicks);

                long usKernel = (endKernelTicks - startKernelTicks) / 10;
                ulong usTSC   = 1000000u * (endTSC - startTSC) / (ulong) (ProcessService.GetCyclesPerSecond());
                Console.Write(" Target {0,7} us  TSC {1,7} us  HW {2,7} us\n",
                              1000000 / divisor, (int)usTSC, (int)usKernel);
            }
            return 0;
        }
    }
}
