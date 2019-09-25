//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace System.Threading
{

    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    /// <summary>
    /// A monitor is used for synchronization. Only a single thread can
    /// hold the monitor at any given time.
    ///
    /// The monitor maintains two lists of threads: one for threads waiting
    /// to enter the monitor, and one for threads waiting for a pulse within
    /// the monitor.
    /// </summary>
    public sealed class Monitor {
        /// <summary>
        /// Private so that only we can create instances.
        /// </summary>
        private Monitor() {
            this.Mutex = new Mutex();
            this.WaitEvent = new AutoResetEvent(false);
            this.Depth = 0;
        }

        /// <summary>
        /// Attempt to enter the monitor, blocking until it is held.
        /// </summary>
        public static void Enter(Object obj) {
            VTable.DebugBreak();
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            monitor.Enter();
        }

        /// <summary>
        /// Exit the monitor.
        /// </summary>
        public static void Exit(Object obj) {
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            monitor.Exit();
        }

        /// <summary>
        /// Wake up a thread waiting on the monitor.
        /// </summary>
        public static void Pulse(Object obj) {
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            monitor.Pulse();
        }

        /// <summary>
        /// Wake up all threads waiting on the monitor.
        /// </summary>
        public static void PulseAll(Object obj) {
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            monitor.PulseAll();
        }

        /// <summary>
        /// Attempt to enter the monitor, returning immediately if it is
        /// already held by another thread.
        /// </summary>
        public static bool TryEnter(Object obj) {
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            return monitor.TryEnter();
        }

        /// <summary>
        /// Attempt to enter the monitor, returning if it can not be taken
        /// within the specified timeout.
        /// </summary>
        public static bool TryEnter(Object obj, int millisecondTimeout) {
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            return monitor.TryEnter(millisecondTimeout);
        }

        /// <summary>
        /// Attempt to enter the monitor, returning if it can not be taken
        /// within the specified timeout.
        /// </summary>
        public static bool TryEnter(Object obj, TimeSpan timeout) {
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            return monitor.TryEnter(GetMillisecondTimeout(timeout));
        }

        /// <summary>
        /// Wait to be woken up by a holder of the monitor.
        /// </summary>
        public static bool Wait(Object obj) {
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            return monitor.Wait(Timeout.Infinite);
        }

        /// <summary>
        /// Wait to be woken up by a holder of the monitor. Give up after
        /// a specified timeout.
        /// </summary>
        public static bool Wait(Object obj, int millisecondsTimeout) {
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            return monitor.Wait(millisecondsTimeout);
        }

        /// <summary>
        /// Wait to be woken up by a holder of the monitor. Give up after
        /// a specified timeout.
        /// </summary>
        public static bool Wait(Object obj, TimeSpan timeout) {
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            return monitor.Wait(GetMillisecondTimeout(timeout));
        }

        /// <summary>
        /// Wait to be woken up by a holder of the monitor. Give up after
        /// a specified timeout.
        ///
        /// Overload exists to match the CLR. Exit Context not supported.
        /// </summary>
        public static bool Wait(Object obj,
                                int millisecondsTimeout,
                                bool exitContext) {
            if (exitContext)
                throw new NotSupportedException("exitContext not supported!");
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            return monitor.Wait(millisecondsTimeout);
        }

        /// <summary>
        /// Wait to be woken up by a holder of the monitor. Give up after
        /// a specified timeout.
        ///
        /// Overload exists to match the CLR. Exit Context not supported.
        /// </summary>
        public static bool Wait(Object obj,
                                TimeSpan timeout,
                                bool exitContext) {
            if (exitContext)
                throw new NotSupportedException("exitContext not supported!");
            Monitor monitor = GetMonitorFromSyncBlock(obj);
            return monitor.Wait(GetMillisecondTimeout(timeout));
        }

        /// <summary>
        /// Extract Milliseconds from a TimeSpan
        /// </summary>
        [Inline]
        private static int GetMillisecondTimeout(TimeSpan timeout) {
            int tm = (int)timeout.TotalMilliseconds;
            if (tm < - 1 || tm > Int32.MaxValue) {
                throw new ArgumentOutOfRangeException("timeout",
                    "ArgumentOutOfRange_NeedNonNegOrNegative1");
            }
            return tm;
        }

        /// <summary>
        /// Enter the monitor, blocking until it is held.
        /// </summary>
        internal void Enter() {
            TryEnter(Timeout.Infinite);
        }

        /// <summary>
        /// Exit the monitor.
        /// </summary>
        internal void Exit() {
            Thread currentThread = Thread.CurrentThread;
            if (this.Mutex.GetBeneficiary() != currentThread) {
                throw new SynchronizationLockException("Monitor not held on Exit");
            }

            this.Depth--;
            if (this.Depth == 0) {
                this.Mutex.ReleaseMutex();
            }
        }

        /// <summary>
        /// Wake up a single thread waiting on the monitor.
        /// </summary>
        internal void Pulse() {
            Thread currentThread = Thread.CurrentThread;
            if (this.Mutex.GetBeneficiary() != currentThread) {
                throw new SynchronizationLockException("Monitor not held on Pulse");
            }

            this.WaitEvent.NotifyOne();
        }

        /// <summary>
        /// Wake up all threads waiting on the monitor.
        /// </summary>
        internal void PulseAll() {
            Thread currentThread = Thread.CurrentThread;
            if (this.Mutex.GetBeneficiary() != currentThread) {
                throw new SynchronizationLockException("Monitor not held on PulseAll");
            }

            this.WaitEvent.NotifyAll();
        }

        /// <summary>
        /// Try to enter the monitor, returning immediately if it is
        /// already held.
        /// </summary>
        internal bool TryEnter() {
            return TryEnter(0);
        }

        /// <summary>
        /// Try to enter the monitor, giving up if it cannot be
        /// entered after a timeout.
        /// </summary>
        internal bool TryEnter(int timeout) {
            Thread currentThread = Thread.CurrentThread;
            if (this.Mutex.GetBeneficiary() == currentThread) {
                this.Depth++;
                return true;
            }

            this.Depth = 0;
            return Mutex.WaitOne(timeout);
        }

        /// <summary>
        /// Wait within the monitor for a Pulse.
        /// </summary>
        internal bool Wait(int timeout) {
            Thread currentThread = Thread.CurrentThread;
            if (this.Mutex.GetBeneficiary() != currentThread) {
                throw new SynchronizationLockException("Monitor not held on Wait");
            }

            int rememberedDepth = this.Depth;
            this.Mutex.ReleaseMutex();
            bool waitSuccess = this.WaitEvent.WaitOne();
            this.Mutex.WaitOne();
            this.Depth = rememberedDepth;

            return waitSuccess;
        }

        /// <summary>
        /// Ensure that the passed object has a monitor (and associated
        /// SyncBlock) allocated.
        /// </summary>
        internal static void CreateMonitor(Object obj) {
            GetMonitorFromSyncBlock(obj);
        }

        /// <summary>
        /// Look up the Monitor for the specified object in the SyncBlock
        /// tables. If no Monitor exists for the object then one is created.
        /// </summary>
        private static Monitor GetMonitorFromSyncBlock(Object obj) {
            if (obj == null) {
                throw new ArgumentNullException();
            }
            SyncBlock[] table;
            int index = SyncBlock.GetSyncBlockIndex(obj, out table);
            if (index < 0 || table[index].Monitor == null) {
                if (index < 0) {
                    index = SyncBlock.LazyCreateSyncBlock(obj, out table);
                }
                Monitor monitor = table[index].Monitor;
                if (monitor == null) {
                    Interlocked.CompareExchange(ref table[index].Monitor, new Monitor(), null);
                    monitor = table[index].Monitor;
                }
                return monitor;
            }
            else {
                return table[index].Monitor;
            }
        }

        /// <summary>
        /// The recursion depth of the current holder of the monitor.
        /// </summary>
        internal int Depth;

        /// <summary>
        /// The mutex that is held by the thread that holds the monitor
        /// </summary>
        internal Mutex Mutex;

        /// <summary>
        /// The event that is used for threads waiting for Pulses
        /// </summary>
        internal AutoResetEvent WaitEvent;
    }

}
