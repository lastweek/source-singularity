//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


//#define ENABLED  

namespace System.GCs {
    using System;
    using System.Threading;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

#if SINGULARITY
    using Microsoft.Singularity;
#if SINGULARITY_PROCESS
    using Microsoft.Singularity.V1.Services;
#endif
#endif

    /// <summary>
    /// Enumeration of Event Types.
    /// </summary>
    public enum GCEvent: int {
        CreateHeap,
        DestroyHeap,
        StopTheWorld,
        StopThread,
        ResumeTheWorld,
        ComputeRootSet,
        TraceStart,
        TraceSpecial,
        SweepStart,
        SweepSpecial,
        SweepPreCommit,
        CollectionComplete,
        RootSetComputed,
        StackScanStart,
        StackScanComplete
    }

    /// <summary>
    /// Manages statistics from the collector. Intended for communication
    /// with the scheduler.
    /// </summary>
    internal class CollectorStatistics {
        [Inline]
        private static string EventToString(GCEvent ev) {
            switch (ev) {
              case GCEvent.CreateHeap:         return "CreateHeap        ";
              case GCEvent.DestroyHeap:        return "DestroyHeap       ";
              case GCEvent.StopTheWorld:       return "StopTheWorld      ";
              case GCEvent.StopThread:         return "StopThread        ";
              case GCEvent.ResumeTheWorld:     return "ResumeTheWorld    ";
              case GCEvent.ComputeRootSet:     return "ComputeRootSet    ";
              case GCEvent.TraceStart:         return "TraceStart        ";
              case GCEvent.TraceSpecial:       return "TraceSpecial      ";
              case GCEvent.SweepStart:         return "SweepStart        ";
              case GCEvent.SweepSpecial:       return "SweepSpecial      ";
              case GCEvent.SweepPreCommit:     return "SweepPreCommit    ";
              case GCEvent.CollectionComplete: return "CollectionComplete";
              case GCEvent.RootSetComputed:    return "RootSetComputed   ";
              case GCEvent.StackScanStart:     return "StackScanStart    ";
              case GCEvent.StackScanComplete:  return "StackScanComplete ";
              default:                         return "Unknown!          ";
            }
        }

        [Inline]
        private static string EventToFormatString(GCEvent ev) {
            switch (ev) {
              case GCEvent.CreateHeap:         return "CreateHeap";
              case GCEvent.DestroyHeap:        return "DestroyHeap";
              case GCEvent.StopTheWorld:       return "StopTheWorld";
              case GCEvent.StopThread:         return "StopThread, thread {0}";
              case GCEvent.ResumeTheWorld:     return "ResumeTheWorld";
              case GCEvent.ComputeRootSet:     return "ComputeRootSet";
              case GCEvent.TraceStart:         return "TraceStart";
              case GCEvent.TraceSpecial:       return "TraceSpecial";
              case GCEvent.SweepStart:         return "SweepStart";
              case GCEvent.SweepSpecial:       return "SweepSpecial";
              case GCEvent.SweepPreCommit:     return "SweepPreCommit";
              case GCEvent.CollectionComplete: return "CollectionComplete";
              case GCEvent.RootSetComputed:    return "RootSetComputed";
              case GCEvent.StackScanStart:     return "StackScanStart, thread {0}";
              case GCEvent.StackScanComplete:  return "StackScanComplete, thread {0}";
              default:                         return "Unknown!";
            }
        }

        /// <summary>
        /// The current value of the counter.
        /// </summary>
        public static long PerformanceCounter {
            [Inline]
            get {
                long val;
                bool ok = QueryPerformanceCounter(out val);
                VTable.Assert(ok);
                return val;
            }
        }

        public static long ThreadTime {
            [Inline]
            get {
#if SINGULARITY
                return 0;
#else
                long creationTime, exitTime, kernelTime, userTime;

                UIntPtr handle = Thread.CurrentThread.asmWin32ThreadHandle;

                bool ok = GetThreadTimes(handle,
                                         out creationTime,
                                         out exitTime,
                                         out kernelTime,
                                         out userTime);
                VTable.Assert(ok);
                return kernelTime + userTime;
#endif
            }
        }

#if SINGULARITY_KERNEL
        public static bool QueryPerformanceCounter(out long lpPerformanceCount)
        {
            lpPerformanceCount = unchecked((long)Processor.CycleCount);
            return true;
        }

        public static bool QueryPerformanceFrequency(out long lpFrequency)
        {
            lpFrequency = unchecked((long)Processor.CyclesPerSecond);
            return true;
        }
#elif SINGULARITY_PROCESS
        public static bool QueryPerformanceCounter(out long lpPerformanceCount)
        {
            lpPerformanceCount = unchecked((long)ProcessService.GetCycleCount());
            return true;
        }

        public static bool QueryPerformanceFrequency(out long lpFrequency)
        {
            lpFrequency = unchecked((long)ProcessService.GetCyclesPerSecond());
            return true;
        }
#else // not SINGULARITY
        [DllImport("BRT")]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1024)]
        public static extern bool QueryPerformanceCounter(
            out long lpPerformanceCount);

        [DllImport("BRT")]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1024)]
        public static extern bool QueryPerformanceFrequency(
            out long lpFrequency);

        [DllImport("BRT")]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1024)]
        public static extern bool GetThreadTimes(
            UIntPtr hThread,
            out long lpCreationTime,
            out long lpExitTime,
            out long lpKernelTime,
            out long lpUserTime
            );
#endif

        /// <summary>
        /// The number of counter values per microsecond.
        /// </summary>
        public static long CounterFrequency;

        /// <summary>
        /// The counter value at the initialization of statistics.
        /// </summary>
        public static long StartCount;

        /// <summary>
        /// Initialize the statistics information
        /// </summary>
        public static void Initialize() {
#if ENABLED
            bool ok = QueryPerformanceFrequency(out CounterFrequency);
            VTable.Assert(CounterFrequency > 0);
            VTable.Assert(ok);
            StartCount = PerformanceCounter;
#endif
        }

        /// <summary>
        /// Print out a summary
        /// </summary>
        public static void Summary() {

        }

        /// <summary>
        /// A GC event.
        /// </summary>
        [Inline]
        public static void Event(GCEvent ev) {
            Event(ev, -1);
        }

        /// <summary>
        /// A GC event.
        /// </summary>
        [Inline]
        public static void Event(GCEvent ev, long val) {
#if ENABLED
            long time = ((PerformanceCounter - StartCount) * 1000000
                         / CounterFrequency);

            LogEntry le;

            le.TimeStamp = time;
            le.ThreadTime = 0;
            le.Event = ev;
            le.Data = val;

            Log(le);
#endif
        }

        private static void Log(LogEntry le) {
#if SINGULARITY
            Tracing.Log(Tracing.Audit,
                        EventToFormatString(le.Event),
                        unchecked((UIntPtr)(uint)le.Data));
#endif
#if DONT
            Thread t = Thread.CurrentThread;
            VTable.DebugPrint("#GCEVENT Thread {0}: {1}, {2}, {3}\n",
                              __arglist(t.threadIndex,
                                        EventToString(le.Event),
                                        le.TimeStamp,
                                        le.Data));
#endif
        }


        private struct LogEntry {
            public GCEvent Event;
            public long TimeStamp;
            public long ThreadTime;
            public long Data;
        }
    }
}
