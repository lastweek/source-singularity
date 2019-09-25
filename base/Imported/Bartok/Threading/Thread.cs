////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Thread.cs
//
//  Note:
//
//      The Thread class and the Scheduler interact through three mechanisms.
//
//      First, the synchronization operations acquire the Scheduler's dispatch
//      lock (via Scheduler.DispatchLock() and Scheduler.DispatchRelease()
//      to ensure that no two processors ever attempt to dispatch on the block
//      or release threads at exactly the same time.
//
//      Second, the Thread class notifies the Scheduler of important events
//      in the life of each thread.  These notifications are done via overrides
//      on the thread class.  The mixin overrides are:
//          Scheduler.OnThreadStateInitialize(): Thread has been created.
//          Scheduler.OnThreadStart():      Thread is ready to start.
//          Scheduler.OnThreadBlocked():    Thread just blocked on a handle.
//          Scheduler.OnThreadUnblocked():  Thread is now runnable.
//          Scheduler.OnThreadYield():      Thread yields processor.
//          Scheduler.OnThreadStop():       Thread is ready to stop.
//          Scheduler.OnThreadFreezeIncrement(): Freeze thread, incr count.
//          Scheduler.OnThreadFreezeDecrement(): Decr count, if 0 then unfreeze
//
//      Third, the Scheduler calls Thread.Stopped() when it has finish with a
//      thread that is no longer runnable.
//

//#define DEBUG_SWITCH

namespace System.Threading
{
    using System.Threading;
    using System.Runtime.InteropServices;
    using System;
    using System.Diagnostics;
    using System.Globalization;
    using System.GCs;
    using System.Collections;
    using System.Runtime.CompilerServices;
    using Microsoft.Bartok.Runtime;

    ///
    /// <summary>
    ///     Class implements thread functionality in Singluarity
    /// </summary>
    ///
    [CCtorIsRunDuringStartup]
    [StructLayout(LayoutKind.Sequential)]
    [CLSCompliant(false)]
    [RequiredByBartok]
    [AccessedByRuntime("referenced from c++")]
    public sealed partial class Thread
    {

        // this is used by bartok backend. When bartok try to generate
        // callback stub for delegate, it checks to see if it is
        // ThreadProc, if it is not, bartok adds leaveGCSafeState and
        // enterGCSafeState around the delegate call.
        [RequiredByBartok]
        private unsafe delegate uint ThreadProc(void *param);

        // Other part of class must define:

        //   private static Thread GetCurrentThreadNative();
        //   public static int GetCurrentThreadIndex();

        /// <summary> Thread specific heap allocator </summary>
        [RequiredByBartok]
        internal SegregatedFreeList     segregatedFreeList;

        /// <summary>Thread specific bump allocator </summary>
        [RequiredByBartok]
        internal BumpAllocator          bumpAllocator;

        /// <summary>
        ///      Bartok specific field: Support for try_all { ... } construct
        ///</summary>
        [RequiredByBartok]
        internal TryAllManager          tryAllManager;
    }
}

