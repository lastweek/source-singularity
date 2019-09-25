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
    [ConsoleCategory(HelpMessage="CreateProcess benchmark test", DefaultAction=true)]
    internal class Parameters 
    {
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
            return CreateProcessTest.AppMain(this);
        }
    }

    //
    // The goal of this test is to time how long it takes to
    // create a process.
    //
    public class CreateProcessTest
    {
        private static bool AtRing3;

#if x64_PERF
        [CLSCompliant(false)]
        public struct PerfEvtSel
        {
            // Bits and Flags
            public const uint CNT_MASK  = 0xff000000;
            public const uint INV       = 0x00800000;
            public const uint EN        = 0x00400000;
            public const uint INT       = 0x00100000;
            public const uint PC        = 0x00080000;
            public const uint E         = 0x00040000;
            public const uint OS        = 0x00020000;
            public const uint USR       = 0x00010000;
            public const uint UNIT_MASK = 0x0000ff00;
            public const uint SELECTOR  = 0x000000ff;

            // Common setting: Count all, but don't interrupt,
            public const uint COUNT     = (EN | PC | OS | USR);

            // Selector values.
            public const uint DtlbL1MissL2Hit                   = 0x45; // Speculative
            public const uint DtlbL1MissL2Miss                  = 0x46; // Speculative
            public const uint CyclesNotHalted                   = 0x76;
            public const uint RequestsToL2Cache                 = 0x7d;
            public const uint ItlbL1MissL2Hit                   = 0x84;
            public const uint ItlbL1MissL2Miss                  = 0x85;
            public const uint RetiredInstructions               = 0xc0;
            public const uint RetiredBranchInstructions         = 0xc2;
            public const uint RetiredBranchesMispredicted       = 0xc3;
            public const uint RetiredBranchesTaken              = 0xc4;
            public const uint CyclesInterruptsMasked            = 0xcd;
            public const uint CyclesInterruptsBlocked           = 0xce;
        }

        public static void Reset(uint pmc, ulong value)
        {
            // Clear the event selector.
            Processor.WriteMsr(0xc0010000 + pmc, 0);
            // Clear the performance counter.
            Processor.WriteMsr(0xc0010004 + pmc, 0);
            // Enable the event selector.
            Processor.WriteMsr(0xc0010000 + pmc, value);
        }

        public static string EvtSelToString(ulong value)
        {
            switch (value & 0xff) {
                case PerfEvtSel.DtlbL1MissL2Hit:            return "DTLB_L2_Hit";
                case PerfEvtSel.DtlbL1MissL2Miss:           return "DTBL_L2_Miss";
                case PerfEvtSel.CyclesNotHalted:            return "CyclesNotHalted";
                case PerfEvtSel.RequestsToL2Cache:          return "TLB_L2_Requests";
                case PerfEvtSel.ItlbL1MissL2Hit:            return "ITLB_L2_Hit";
                case PerfEvtSel.ItlbL1MissL2Miss:           return "ITLB_L2_Miss";
                case PerfEvtSel.RetiredInstructions:        return "Retired_Inst.";
                case PerfEvtSel.RetiredBranchInstructions:  return "Branches";
                case PerfEvtSel.RetiredBranchesMispredicted:return "Br_Mispredicted";
                case PerfEvtSel.RetiredBranchesTaken:       return "Br_Taken";
                case PerfEvtSel.CyclesInterruptsMasked:     return "Ints_Masked (cyc)";
                case PerfEvtSel.CyclesInterruptsBlocked:    return "Ints_Blocked (cyc)";
                default:
                    return String.Format("{0:x16}", value);
            }
        }

        private static ulong x64_i0, x64_p0;
        private static ulong x64_i1, x64_p1;
        private static ulong x64_i2, x64_p2;
        private static ulong x64_i3, x64_p3;
#endif

        private static void DualWriteLine(string message)
        {
            Console.WriteLine(message);
            DebugStub.WriteLine(message);
        }

        public struct PerfSnap
        {
            private bool disabled;
            private long begCycleCount;
            private long endCycleCount;
            private long begSwitchCount;
            private long endSwitchCount;
            private long begInterruptCount;
            private long endInterruptCount;
            private long begKernelGcCount;
            private long endKernelGcCount;
            private long begProcessGcCount;
            private long endProcessGcCount;
            private long iterations;
            private ulong begAllocatedCount;
            private ulong begAllocatedBytes;
            private ulong begFreedCount;
            private ulong begFreedBytes;
            private ulong endAllocatedCount;
            private ulong endAllocatedBytes;
            private ulong endFreedCount;
            private ulong endFreedBytes;
            private ulong begStackGets;
            private ulong begStackRets;
            private ulong endStackGets;
            private ulong endStackRets;


            public long Cycles      { get { return endCycleCount - begCycleCount; } }
            public long Interrupts  { get { return endInterruptCount - begInterruptCount; } }
            public long Switches    { get { return endSwitchCount - begSwitchCount; } }
            public long KernelGCs   { get { return endKernelGcCount - begKernelGcCount; } }
            public long ProcessGCs  { get { return endProcessGcCount - begProcessGcCount; } }
            public ulong AllocatedCount { get { return endAllocatedCount-begAllocatedCount; } }
            public ulong AllocatedBytes { get { return endAllocatedBytes-begAllocatedBytes; } }
            public ulong FreedCount { get { return endFreedCount - begFreedCount; } }
            public ulong FreedBytes { get { return endFreedBytes - begFreedBytes; } }
            public ulong StackGets { get { return endStackGets - begStackGets; } }
            public ulong StackRets { get { return endStackRets - begStackRets; } }

            public void Start()
            {
                if (!AtRing3) {
                    disabled = Processor.DisableLocalPreemption();
                }

                int collectorCount;
                long collectorMillis;
                long collectorBytes;
                GC.PerformanceCounters(out collectorCount,
                                       out collectorMillis,
                                       out collectorBytes);

                ulong stackGets;
                ulong stackRets;
                StackService.GetUsageStatistics(out stackGets,
                                                out stackRets);
                begStackGets = stackGets;
                begStackRets = stackRets;

                ulong allocatedCount;
                ulong allocatedBytes;
                ulong freedCount;
                ulong freedBytes;
                PageTableService.GetUsageStatistics(out allocatedCount,
                                                    out allocatedBytes,
                                                    out freedCount,
                                                    out freedBytes);
                begAllocatedCount = allocatedCount;
                begAllocatedBytes = allocatedBytes;
                begFreedCount = freedCount;
                begFreedBytes = freedBytes;

                begInterruptCount = ProcessService.GetKernelInterruptCount();
                begSwitchCount = ProcessService.GetContextSwitchCount();
                begKernelGcCount = ProcessService.GetKernelGcCount();
                begProcessGcCount = collectorCount;

#if x64_PERF
                // Set up for perf counting
                if (!AtRing3) {
                    // Reset the performance counters to what we're interested in.
                    Reset(0, PerfEvtSel.COUNT | PerfEvtSel.CyclesNotHalted);
                    Reset(1, PerfEvtSel.COUNT | PerfEvtSel.RetiredInstructions);
                    Reset(2, PerfEvtSel.COUNT | PerfEvtSel.RetiredBranchInstructions);
                    Reset(3, PerfEvtSel.COUNT | PerfEvtSel.RequestsToL2Cache | 0x400);
                }
                else {
                    // We're not allowed to reset the perf counters, so take note
                    // of their current values; we will subtract from this later.
                    x64_i0 = Processor.ReadPmc(0);
                    x64_i1 = Processor.ReadPmc(1);
                    x64_i2 = Processor.ReadPmc(2);
                    x64_i3 = Processor.ReadPmc(3);
                }
#endif

                begCycleCount = unchecked((long)Processor.CycleCount);
            }

            public void Finish(long iterations)
            {
                endCycleCount = unchecked((long)Processor.CycleCount);

#if X64_PERF
                x64_p0 = Processor.ReadPmc(0);
                x64_p1 = Processor.ReadPmc(1);
                x64_p2 = Processor.ReadPmc(2);
                x64_p3 = Processor.ReadPmc(3);
#endif

                endInterruptCount = ProcessService.GetKernelInterruptCount();
                endSwitchCount = ProcessService.GetContextSwitchCount();
                endKernelGcCount = ProcessService.GetKernelGcCount();

                int collectorCount;
                long collectorMillis;
                long collectorBytes;
                GC.PerformanceCounters(out collectorCount,
                                       out collectorMillis,
                                       out collectorBytes);
                endProcessGcCount = collectorCount;

                ulong allocatedCount;
                ulong allocatedBytes;
                ulong freedCount;
                ulong freedBytes;
                PageTableService.GetUsageStatistics(out allocatedCount,
                                                    out allocatedBytes,
                                                    out freedCount,
                                                    out freedBytes);
                endAllocatedCount = allocatedCount;
                endAllocatedBytes = allocatedBytes;
                endFreedCount = freedCount;
                endFreedBytes = freedBytes;

                ulong stackGets;
                ulong stackRets;
                StackService.GetUsageStatistics(out stackGets,
                                                out stackRets);
                endStackGets = stackGets;
                endStackRets = stackRets;

                if (!AtRing3) {
                    Processor.RestoreLocalPreemption(disabled);
                }

                this.iterations = iterations;
            }

            public void Display(string name)
            {
                DualWriteLine(
                    String.Format("{0,-16} {1,6:d} x{2,8:d} ={3,12:d} " +
                                  "[swi={4,6:d} int={5,3:d} gc={6:d}/{7:d}]",
                                  name,
                                  iterations,
                                  Cycles / iterations,
                                  Cycles,
                                  Switches,
                                  Interrupts,
                                  KernelGCs,
                                  ProcessGCs)
                    );


                if (AllocatedCount != 0 || FreedCount != 0 || StackGets != 0) {
                    DualWriteLine(
                        string.Format(
                            "                       " +
                            "[alloc={0,4:d}/{1,8:x} free={2,4:d}/{3,8:x} " +
                            "stack={4,4:d}/{5,4:d}]",
                            AllocatedCount,
                            AllocatedBytes,
                            FreedCount,
                            FreedBytes,
                            StackGets,
                            StackRets)
                        );
                }

#if x64_PERF
                if (!AtRing3) {
                    // Read off the current MSR values and turn them
                    // into nice labels
                    ulong e0 = Processor.ReadMsr(0xc0010000);
                    ulong e1 = Processor.ReadMsr(0xc0010001);
                    ulong e2 = Processor.ReadMsr(0xc0010002);
                    ulong e3 = Processor.ReadMsr(0xc0010003);

                    DualWriteLine(
                        String.Format("evt: {0,16} {1,16} {2,16} {3,16}",
                                      EvtSelToString(e0),
                                      EvtSelToString(e1),
                                      EvtSelToString(e2),
                                      EvtSelToString(e3)));
                }
                else {
                    // Subtract from the initial perf-counter values to
                    // get the delta we want
                    x64_p0 -= x64_i0;
                    x64_p1 -= x64_i1;
                    x64_p2 -= x64_i2;
                    x64_p3 -= x64_i3;
                }

                DualWriteLine(
                    String.Format("pmc: {0:d16} {1:d16} {2:d16} {3:d16} {4:d16}\n\n",
                                  Cycles, x64_p0, x64_p1, x64_p2, x64_p3));
#endif
            }
        }


        internal static int AppMain(Parameters! config)
        {
            bool runQuiet = config.quietMode;
            long repetitions = config.repetitions; 

            Console.Write("\nProcess creation test\n\n");
            string [] arguments;
            for (long i = 0; i < repetitions; i++) {
                arguments = new string[2];
                arguments[0] = "testpe";
                arguments[1] = "!"; // Special flag to not notify debugger.
                TimeProcess(arguments, runQuiet);
            }
            return 0;
        }

        public static void TimeProcess(String[]! args, bool runQuiet)
        {
            ulong baseline;
            ulong created;
            ulong started;
            ulong exited;
            Process process = null;

            PerfSnap snap = new PerfSnap();

            snap.Start();
            try {
                ProcessService.Waypoint0();
                baseline = Processor.CycleCount;

                //
                // Time process creation.
                //
                ProcessService.Waypoint(1500);
                process = new Process(args);
                created = Processor.CycleCount;

                //
                // Time process start.
                //
                ProcessService.Waypoint(1501);

                process.Start();
                started = Processor.CycleCount;

                ProcessService.Waypoint(1502);
                //
                // Time process execution.
                //
                process.Join();
                ProcessService.Waypoint(1503);
                exited = Processor.CycleCount;
            }
            finally {
                snap.Finish(1);
            }

            snap.Display("CreateProc");

            ProcessService.Waypoint(1504);
            process.Dispose(true);
            ProcessService.Waypoint(1505);
            ProcessService.WaypointDump();


            if (runQuiet) {
                return;
            }

            //
            // Tell the world.
            //
            Console.WriteLine();
            Console.WriteLine("Tested process: {0}", args[0]);
            Console.WriteLine("Create process: {0,15:d} cycles", created - baseline);
            Console.WriteLine("Start process:  {0,15:d} cycles", started - created);
            Console.WriteLine("Run process:    {0,15:d} cycles", exited - started);
            Console.WriteLine("Total:          {0,15:d} cycles", exited - baseline);
            Console.WriteLine("Process.Create: {0,15:d} cycles", started - baseline);
            Console.WriteLine();
            Console.WriteLine();
        }
    }
}
