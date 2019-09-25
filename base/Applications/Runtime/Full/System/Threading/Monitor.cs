//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace System.Threading
{

    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    using Microsoft.Bartok.Runtime;

    using Microsoft.Singularity;

    /// <summary>
    /// A monitor is used for synchronization. Only a single thread can
    /// hold the monitor at any given time.
    ///
    /// The monitor maintains two lists of threads: one for threads waiting
    /// to enter the monitor, and one for threads waiting for a pulse within
    /// the monitor.
    /// </summary>
    public sealed partial class Monitor {
        /// <summary>
        /// Private so that only we can create instances.
        /// </summary>
        internal Monitor()
        {
            this.mutex = new Mutex();
            this.depth = 0;
        }

        /// <summary>
        /// Wake up a thread waiting on the monitor.
        /// </summary>
        public static void Pulse(Object obj)
        {
            Monitor monitor = GetMonitorFromObject(obj);
            monitor.Pulse();
        }

        /// <summary>
        /// Wake up all threads waiting on the monitor.
        /// </summary>
        public static void PulseAll(Object obj)
        {
            Monitor monitor = GetMonitorFromObject(obj);
            monitor.PulseAll();
        }

        /// <summary>
        /// Attempt to enter the monitor, returning immediately if it is
        /// already held by another thread.
        /// </summary>
        public static bool TryEnter(Object obj)
        {
            Monitor monitor = GetMonitorFromObject(obj);
            return monitor.TryEnter();
        }

        /// <summary>
        /// Attempt to enter the monitor, returning if it can not be taken
        /// within the specified timeout.
        /// </summary>
        public static bool TryEnter(Object obj, TimeSpan timeout)
        {
            Monitor monitor = GetMonitorFromObject(obj);
            return monitor.TryEnter(SchedulerTime.Now + timeout);
        }

        /// <summary>
        /// Wait to be woken up by a holder of the monitor.
        /// </summary>
        public static bool Wait(Object obj)
        {
            Monitor monitor = GetMonitorFromObject(obj);
            return monitor.Wait(SchedulerTime.MaxValue);
        }

        /// <summary>
        /// Wait to be woken up by a holder of the monitor. Give up after
        /// a specified timeout.
        /// </summary>
        public static bool Wait(Object obj, TimeSpan timeout)
        {
            Monitor monitor = GetMonitorFromObject(obj);
            return monitor.Wait(SchedulerTime.Now + timeout);
        }

        /// <summary>
        /// Wait to be woken up by a holder of the monitor. Give up after
        /// a specified timeout.
        ///
        /// Overload exists to match the CLR. Exit Context not supported.
        /// </summary>
        public static bool Wait(Object obj,
                                TimeSpan timeout,
                                bool exitContext)
        {
            if (exitContext) {
                DebugStub.Break();
                throw new NotSupportedException("exitContext not supported!");
            }
            Monitor monitor = GetMonitorFromObject(obj);
            return monitor.Wait(SchedulerTime.Now + timeout);
        }

        /// <summary>
        /// Enter the monitor, blocking until it is held.
        /// </summary>
        internal void Enter()
        {
            TryEnter(SchedulerTime.MaxValue);
        }

        /// <summary>
        /// Exit the monitor.
        /// </summary>
        internal void Exit()
        {
            if (!mutex.IsOwnedByCurrentThread()) {
                DebugStub.Break();
                throw new SynchronizationLockException("Monitor not held on Exit");
            }

            depth--;
            if (depth == 0) {
                mutex.ReleaseMutex();
            }
        }

        /// <summary>
        /// Wake up a single thread waiting on the monitor.
        /// </summary>
        internal void Pulse()
        {
            if (!mutex.IsOwnedByCurrentThread()) {
                DebugStub.Break();
                throw new SynchronizationLockException("Monitor not held on Pulse");
            }

            // Wake up thread at the head of the wait list.
            if (waitListHead != null) {
                Thread t = Dequeue();
                if (t != null) {
                    t.nextThread = null;
                    t.SignalMonitor();
                }
            }
        }

        /// <summary>
        /// Wake up all threads waiting on the monitor.
        /// </summary>
        internal void PulseAll()
        {
            if (!mutex.IsOwnedByCurrentThread()) {
                DebugStub.Break();
                throw new SynchronizationLockException("Monitor not held on PulseAll");
            }

            // Wake up all threads the wait list.
            if (waitListHead != null) {
                Thread t = waitListHead;
                while (t != null) {
                    Thread next = t.nextThread;
                    t.nextThread = null;
                    t.SignalMonitor();
                    t = next;
                }
                waitListHead = null;
                waitListTail = null;
            }
        }

        /// <summary>
        /// Try to enter the monitor, returning immediately if it is
        /// already held.
        /// </summary>
        internal bool TryEnter()
        {
            return TryEnter(new SchedulerTime(0));
        }

        /// <summary>
        /// Try to enter the monitor, giving up if it cannot be
        /// entered after a timeout.
        /// </summary>
        internal bool TryEnter(SchedulerTime stop)
        {
            if (mutex.IsOwnedByCurrentThread()) {
                depth++;
                return true;
            }

            if (mutex.AcquireMutex(stop)) {
                depth = 1;
                return true;
            }
            return false;
        }

        /// <summary>
        /// Wait within the monitor for a Pulse.
        /// </summary>
        internal bool Wait(SchedulerTime stop)
        {
            Thread currentThread = Thread.CurrentThread;
            if (!mutex.IsOwnedByCurrentThread()) {
                DebugStub.Break();
                throw new SynchronizationLockException("Monitor not held on Wait");
            }

            int rememberedDepth = depth;
            depth = 0;

            // Add me onto the waiting list.
            Enqueue(currentThread);

            // Exit the monitor
            mutex.ReleaseMutex();

            // Wait
            currentThread.WaitForMonitor(stop);

            // Re-enter the monitor
            mutex.AcquireMutex();
            depth = rememberedDepth;

            bool success = !Remove(currentThread);

            if (!success && stop == SchedulerTime.MaxValue) {
                VTable.DebugBreak();
            }

            return success;
        }

        /// <summary>
        /// Ensure that the passed object has a monitor (and associated
        /// SyncBlock) allocated.
        /// </summary>
        internal static void CreateMonitor(Object obj)
        {
            GetMonitorFromObject(obj);
        }

        // BUGBUG: The garbage collectors will not collect monitors that are
        // in use.  Use a very defensive strategy for now.
        internal bool IsInUse() {
            return true;
        }

        /// <summary>
        /// Internal Type conversion method.
        /// Note: we don't use VTable.fromAddress because we
        /// cannot do a checked cast from Object to Monitor during GC
        /// (because the GC may be using the vtable word)
        /// </summary>
        ///
        internal static Monitor FromAddress(UIntPtr v) {
            return Magic.toMonitor(Magic.fromAddress(v));
        }

        /// <summary>
        /// Look up the Monitor for the specified object in the SyncBlock
        /// tables. If no Monitor exists for the object then one is created.
        /// </summary>
        private static Monitor GetMonitorFromObject(Object obj)
        {
            if (obj == null) {
                DebugStub.Break();
                throw new ArgumentNullException("obj");
            }
            Monitor result = MultiUseWord.GetMonitor(obj);
            return result;
        }

        //////////////////////////////////////////////////////////////////////
        //
        // Linked list of threads waiting for a Pulse in a monitor.
        private Thread waitListHead;
        private Thread waitListTail;

        /// <summary>
        /// Dequeue a thread from the singly linked list from head to tail,
        /// acquiring the ListLock if necessary.
        ///
        /// If the list is empty then this method returns null.
        /// </summary>
        [Inline]
        private Thread Dequeue()
        {
            Thread result;
            if (waitListHead == null) {
                // Empty list
                result = null;
            }
            else if (waitListHead == waitListTail) {
                // Single entry on list
                VTable.Assert(waitListHead.nextThread == null);
                result = waitListHead;
                waitListHead = waitListTail = null;
            }
            else {
                // Multiple entries on list
                result = waitListHead;
                waitListHead = waitListHead.nextThread;
            }
            return result;
        }

        /// <summary>
        /// Search the linked list and remove the specified thread if
        /// it is linked in.
        ///
        /// Acquires the ListLock if necessary.
        /// </summary>
        [Inline]
        private bool Remove(Thread target)
        {
            if (waitListHead == null) {
                return false;
            }

            if (waitListHead == waitListTail) {
                // Single entry on list
                VTable.Assert(waitListHead.nextThread == null);

                if (waitListHead != target) {
                    // Not on list
                    return false;
                }

                waitListHead = waitListTail = null;
            }
            else if (waitListHead == target) {
                // At waitListHead of list
                waitListHead = target.nextThread;
                target.nextThread = null;
            }
            else {
                // Multiple entries on list
                Thread next = waitListHead;
                while (next != null && next.nextThread != target) {
                    next = next.nextThread;
                }

                if (next == null) {
                    // Not on list
                    return false;
                }

                if (waitListTail == target) {
                    // Update the waitListTail
                    waitListTail = next;
                }

                next.nextThread = target.nextThread;
                target.nextThread = null;
            }
            return true;
        }

        /// <summary>
        /// Append a thread at the tail of a queue. If the queue is
        /// currently null this method initializes it.
        ///
        /// Acquires the ListLock if necessary.
        /// </summary>
        [Inline]
        private void Enqueue(Thread target)
        {
            if (waitListHead == null) {
                waitListHead = waitListTail = target;
            }
            else {
                waitListTail.nextThread = target;
                waitListTail = target;
            }
        }

        /// <summary>
        /// The recursion depth of the current holder of the monitor.
        /// </summary>
        private int depth;

        /// <summary>
        /// The mutex that is held by the thread that holds the monitor
        /// </summary>
        private Mutex mutex;
    }
}
