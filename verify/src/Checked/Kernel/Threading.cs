//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System.Runtime.CompilerServices;
using kernel;
using TimeSpan = System.TimeSpan;

namespace System.Threading
{
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    public interface IThreadStart
    {
        void Run();
    }

    public class Thread: kernel.ThreadStart
    {
        IThreadStart iThreadStart;
        kernel.Thread kThread;

        [RequiredByBartok]
        private extern static Thread GetCurrentThreadNative();

        public Thread(IThreadStart iThreadStart)
        {
            this.iThreadStart = iThreadStart;
        }

        public override void Run()
        {
            iThreadStart.Run();
        }

        public void Start()
        {
            kThread = Kernel.kernel.NewThread(this);
        }

        public static void Yield()
        {
            Kernel.kernel.Yield();
        }

        public override String ToString()
        {
            return "Thread(" + kThread.id + ")";
        }
    }

    public class Monitor
    {
        public static void Enter(MonitorLock m)
        {
            m.Acquire();
        }

        public static bool TryEnter(MonitorLock m)
        {
            return m.TryAcquire();
        }

        public static void Exit(MonitorLock m)
        {
            m.Release();
        }

        public static bool TryEnter(MonitorLock m, TimeSpan timeout)
        {
            return m.Acquire(timeout);
        }

        public static void Wait(MonitorLock m)
        {
            m.Wait();
        }

        public static bool Wait(MonitorLock m, TimeSpan timeout)
        {
            return m.Wait(timeout);
        }

        public static void Pulse(MonitorLock m)
        {
            m.PulseAll();
        }

        public static void PulseAll(MonitorLock m)
        {
            m.PulseAll();
        }
    }

    public struct MonitorLocked: IDisposable
    {
        private MonitorLock monitorLock;

        internal MonitorLocked(MonitorLock monitorLock)
        {
            this.monitorLock = monitorLock;
        }

        public void Dispose()
        {
            monitorLock.Release();
        }
    }

    public class MonitorLock
    {
        private Semaphore lockSemaphore = Kernel.kernel.NewSemaphore(1);
        private Semaphore waitSemaphore = null;
        private volatile uint lockHolder = 0xffffffff;
        private volatile uint lockDepth = 0;

        public void Acquire()
        {
            Acquire(null);
        }

        public bool Acquire(TimeSpan timeout)
        {
            return Acquire(new WakeUp(timeout));
        }

        internal bool Acquire(WakeUp wakeUp)
        {
            try
            {
                CompilerIntrinsics.Cli();
                uint cur = Kernel.CurrentThread;
                if (lockHolder == cur)
                {
                    lockDepth++;
                    return true;
                }
                bool gotIt = lockSemaphore.WaitInterruptsDisabled(wakeUp);
                lockHolder = cur;
                return gotIt; // TODO: return value doesn't match documentation, but should it?
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }

        public bool TryAcquire()
        {
            try
            {
                CompilerIntrinsics.Cli();
                uint cur = Kernel.CurrentThread;
                if (lockHolder == cur)
                {
                    lockDepth++;
                    return true;
                }
                bool gotIt = lockSemaphore.TryWaitInterruptsDisabled();
                if (gotIt)
                {
                    lockHolder = cur;
                }
                return gotIt;
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }

        public void Release()
        {
            try
            {
                CompilerIntrinsics.Cli();
                if (lockDepth > 0)
                {
                    lockDepth--;
                    return;
                }
                lockHolder = 0xffffffff;
                lockSemaphore.SignalInterruptsDisabled();
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }

        public MonitorLocked Lock()
        {
            Acquire();
            return new MonitorLocked(this);
        }

        // requires lockSemaphore held
        public void Wait()
        {
            Wait(null);
        }

        // requires lockSemaphore held
        public bool Wait(TimeSpan timeout)
        {
            return Wait(new WakeUp(timeout));
        }

        private bool Wait(WakeUp wakeUp)
        {
            try
            {
                CompilerIntrinsics.Cli();
                if (waitSemaphore == null)
                {
                    waitSemaphore = Kernel.kernel.NewSemaphore(0);
                }
                uint depth = lockDepth;
                uint cur = Kernel.CurrentThread;
                lockHolder = 0xffffffff;
                lockDepth = 0;
                lockSemaphore.SignalInterruptsDisabled();
                bool gotIt = waitSemaphore.WaitInterruptsDisabled(wakeUp);
                lockSemaphore.WaitInterruptsDisabled();
                lockDepth = depth;
                lockHolder = cur;
                return gotIt;
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }

        public void Pulse()
        {
            try
            {
                CompilerIntrinsics.Cli();
                if (waitSemaphore == null)
                {
                    return;
                }
                if (waitSemaphore.capacity != 0)
                {
                    waitSemaphore.SignalInterruptsDisabled();
                }
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }

        public void PulseAll()
        {
            try
            {
                CompilerIntrinsics.Cli();
                if (waitSemaphore == null)
                {
                    return;
                }
                while (waitSemaphore.capacity != 0)
                {
                    waitSemaphore.SignalInterruptsDisabled();
                }
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }
    }

    public abstract class WaitHandle {}

    public class Mutex {}

    // TODO: REVIEW
    public sealed class ManualResetEvent : WaitHandle
    {
        Semaphore waitSemaphore = Kernel.kernel.NewSemaphore(0); // waitSemaphore.capacity <= 0
        bool isSet; // isSet ==> waitSemaphore.capacity == 0

        public ManualResetEvent(): this(false) {}
        public ManualResetEvent(bool isSet) {this.isSet = isSet;}

        public void Set()
        {
            try
            {
                CompilerIntrinsics.Cli();
                isSet = true;
                while (waitSemaphore.capacity != 0)
                {
                    // signal a waiter
                    waitSemaphore.SignalInterruptsDisabled();
                }
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }

        public void Reset()
        {
            try
            {
                CompilerIntrinsics.Cli();
                isSet = false;
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }

        public void WaitOne()
        {
            WaitOne(null);
        }

        public bool WaitOne(TimeSpan timeout)
        {
            return WaitOne(new WakeUp(timeout));
        }

        public bool WaitOne(DateTime time)
        {
            return WaitOne(new WakeUp(time - DateTime.Now));
        }

        private bool WaitOne(WakeUp wakeUp)
        {
            try
            {
                CompilerIntrinsics.Cli();
                if (isSet)
                {
                    return true;
                }
                else
                {
                    return waitSemaphore.WaitInterruptsDisabled(wakeUp);
                }
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }
    }

    // TODO: REVIEW
    public sealed class AutoResetEvent : WaitHandle
    {
        Semaphore waitSemaphore = Kernel.kernel.NewSemaphore(0); // waitSemaphore.capacity <= 0
        bool isSet; // isSet ==> waitSemaphore.capacity == 0

        public AutoResetEvent(): this(false) {}
        public AutoResetEvent(bool isSet) {this.isSet = isSet;}

        public void Set()
        {
            try
            {
                CompilerIntrinsics.Cli();
                if (waitSemaphore.capacity == 0)
                {
                    // no waiters
                    isSet = true;
                }
                else
                {
                    // signal a waiter
                    isSet = false;
                    waitSemaphore.SignalInterruptsDisabled();
                }
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }

        public void Reset()
        {
            try
            {
                CompilerIntrinsics.Cli();
                isSet = false;
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }

        public void WaitOne()
        {
            WaitOne(null);
        }

        public bool WaitOne(TimeSpan timeout)
        {
            return WaitOne(new WakeUp(timeout));
        }

        public bool WaitOne(DateTime time)
        {
            return WaitOne(new WakeUp(time - DateTime.Now));
        }

        private bool WaitOne(WakeUp wakeUp)
        {
            try
            {
                CompilerIntrinsics.Cli();
                if (isSet)
                {
                    isSet = false;
                    return true;
                }
                else
                {
                    return waitSemaphore.WaitInterruptsDisabled(wakeUp);
                }
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }
    }
}

