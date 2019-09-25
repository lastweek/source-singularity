////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ThreadEntry.cs
//
//  Note:
//

// #define DEBUG_SCHEDULER

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;

namespace Microsoft.Singularity.Scheduling
{
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from threads.cpp")]
    public class ThreadEntry
    {
        public readonly Thread  Thread = null;
        internal int            id = -1;
        internal ThreadEntry    next = null;
        internal ThreadEntry    prev = null;
          
        [AccessedByRuntime("referenced from threads.cpp")]
        internal ThreadQueue queue = null;

        public ThreadEntry(Thread thread)
        {
            Thread = thread;
        }

        public ThreadEntry Next
        {
            [NoHeapAllocation]
            get { return next; }
        }

        public ThreadEntry Prev
        {
            [NoHeapAllocation]
            get { return prev; }
        }

        public bool Enqueued
        {
            [NoHeapAllocation]
            get { return (queue != null); }
        }

        [NoHeapAllocation]
        public void RemoveFromQueue()
        {
            if (queue != null) {
                queue.Remove(this);
            }

            VTable.Assert(next == null);
            VTable.Assert(prev == null);
            VTable.Assert(queue == null);
        }

        [NoHeapAllocation]
        public Thread GetBeneficiary()
        {
            return queue.Handle.GetBeneficiary();
        }

        ///
        /// <summary>
        ///     Set/Get Entry Id
        /// </summary>
        ///
        public int Id
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.id;
            }

            [Inline]
            [NoHeapAllocation]
            set 
            {
                this.id = value;
            }
        }
    }
}
