//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System.Runtime.CompilerServices;
using TimeSpan = System.TimeSpan;
using kernel;

namespace kernel
{

public abstract class ThreadStart
{
    public ThreadStart() {}

    [InterruptsDisabled]
    public ThreadStart(bool dummy) {}

    public abstract void Run();
}

public class Thread
{
    internal uint id;
    internal ThreadStart start;
    internal volatile bool alive = true;
    internal volatile Thread nextInQueue;
    internal volatile WakeUp wakeUp; // null if thread not waiting on a timeout

    internal Thread(ThreadStart start)
    {
        this.start = start;
    }

    [InterruptsDisabled]
    internal Thread(ThreadStart start, bool dummy)
    {
        this.start = start;
    }
}

public class Semaphore
{
    internal ThreadQueue waiters;
    internal volatile int capacity;

    internal Semaphore(ThreadQueue waiters, int capacity)
    {
        this.waiters = waiters;
        this.capacity = capacity;
    }

    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    internal void WaitInterruptsDisabled()
    {
        CompilerIntrinsics.Cli(); // TODO: superfluous
        capacity--;
        if (capacity < 0)
        {
            Kernel.kernel.EnqueueAndYield(waiters);
        }
    }

    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    internal bool WaitInterruptsDisabled(WakeUp wakeUp)
    {
        CompilerIntrinsics.Cli(); // TODO: superfluous
        capacity--;
        if (capacity < 0)
        {
            if (wakeUp != null)
            {
                if (wakeUp.time <= 0) {
                    return false;
                }
                uint cur = Kernel.CurrentThread;
                wakeUp.thread = Kernel.kernel.threadTable[cur];
                wakeUp.queue = waiters;
                wakeUp.thread.wakeUp = wakeUp;
            }
            Kernel.kernel.EnqueueAndYield(waiters);
            if (wakeUp != null)
            {
                if (wakeUp.thread.wakeUp == null)
                {
                    // We timed out
                    return false;
                }
                wakeUp.thread.wakeUp = null;
            }
        }
        return true;
    }

    public void Wait()
    {
        try
        {
            CompilerIntrinsics.Cli();
            capacity--;
            if (capacity < 0)
            {
                Kernel.kernel.EnqueueAndYield(waiters);
            }
        }
        finally
        {
            CompilerIntrinsics.Sti();
        }
    }

    [InterruptsDisabled]
    internal bool TryWaitInterruptsDisabled()
    {
        if (capacity <= 0)
        {
            return false;
        }
        capacity--;
        return true;
    }

    public bool TryWait()
    {
        try
        {
            CompilerIntrinsics.Cli();
            if (capacity <= 0)
            {
                return false;
            }
            capacity--;
            return true;
        }
        finally
        {
            CompilerIntrinsics.Sti();
        }
    }

    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    internal void SignalInterruptsDisabled()
    {
        CompilerIntrinsics.Cli(); // TODO: superfluous
        capacity++;
        Thread t = waiters.Dequeue();
        if (t != null)
        {
            ThreadQueue ready = Kernel.kernel.readyQueue;
            ready.Enqueue(t);
            Kernel.kernel.EnqueueAndYield(ready);
        }
    }

    public void Signal()
    {
        try
        {
            CompilerIntrinsics.Cli();
            capacity++;
            Thread t = waiters.Dequeue();
            if (t != null)
            {
                ThreadQueue ready = Kernel.kernel.readyQueue;
                ready.Enqueue(t);
                Kernel.kernel.EnqueueAndYield(ready);
            }
        }
        finally
        {
            CompilerIntrinsics.Sti();
        }
    }
}

internal class ThreadQueue
{
    // circular list based on Thread.nextInQueue
    // tail.nextInQueue points to the head
    private volatile Thread tail;

    internal ThreadQueue()
    {
    }

    [InterruptsDisabled]
    internal ThreadQueue(bool dummy)
    {
    }

    [InterruptsDisabled]
    internal void Enqueue(Thread t)
    {
        Thread tl = tail;
        if (tl == null)
        {
            t.nextInQueue = t;
            tail = t;
        }
        else
        {
            Thread hd = tl.nextInQueue;
            tl.nextInQueue = t;
            t.nextInQueue = hd;
            tail = t;
        }
    }

    [InterruptsDisabled]
    internal Thread Dequeue()
    {
        Thread tl = tail;
        if (tl == null)
        {
            return null;
        }
        else
        {
            Thread hd = tl.nextInQueue;
            if (hd == tl)
            {
                tail = null;
                return hd;
            }
            else
            {
                tl.nextInQueue = hd.nextInQueue;
                return hd;
            }
        }
    }

    [InterruptsDisabled]
    // requires t in queue
    internal void Remove(Thread t)
    {
        Thread tl = tail;
        Thread i = tl;
        for (;;)
        {
            Thread j = i.nextInQueue;
            if (j == t)
            {
                // remove j
                i.nextInQueue = j.nextInQueue;
                if (tail == j)
                {
                    tail = i;
                    if (i == j)
                    {
                        tail = null;
                    }
                }
                return;
            }
        }
    }
}

// Records a thread that is blocked (in queue) but will be unblocked at some time
internal class WakeUp
{
    internal long time;
    internal Thread thread;
    internal ThreadQueue queue;

    internal WakeUp(TimeSpan span)
    {
        this.time = Kernel.GetUtcTime() + span.Ticks;
    }

    internal WakeUp(long time, Thread thread, ThreadQueue queue)
    {
        this.time = time;
        this.thread = thread;
        this.queue = queue;
    }
}
} // namespace kernel

public class Kernel
{
    internal static Kernel kernel;
    internal static volatile uint CurrentThread;

    // Thread 0 is the kernel private thread
    // Threads 1...NUM_THREADS-1 are user threads
    internal const int NUM_THREADS = 64;
    internal Thread[] threadTable = new Thread[Kernel.NUM_THREADS];
    // Threads ready to run:
    internal ThreadQueue readyQueue = new ThreadQueue(true);
    // Threads waiting to be garbage collected:
    internal ThreadQueue collectionQueue = new ThreadQueue(true);
    internal volatile bool collectionRequested;

    internal const int STACK_EMPTY = 0;
    internal const int STACK_RUNNING = 1;
    internal const int STACK_YIELDED = 2;
    internal const int STACK_INTERRUPTED = 3;

    [InterruptsDisabled]
    private Kernel()
    {
    }

    // Entry point for initial threads and new threads.
    // The TAL checker verifies that Main has type ()->void and that Main never returns.
    [RequiresInterruptsDisabled]
    private static void Main()
    {
        uint id = CurrentThread;
        if (id == 0)
        {
            kernel = new Kernel();
            kernel.KernelMain();
        }
        else
        {
            kernel.ThreadMain(id);
        }
        CompilerIntrinsics.Cli(); // TODO: superfluous
        NucleusCalls.DebugPrintHex(0, 0xdead0001);
        while(true) {}
    }

    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    private void KernelMain()
    {
        CompilerIntrinsics.Cli(); // TODO: superfluous
        for (uint i = 0; i < 50 * 80; i++)
        {
            NucleusCalls.VgaTextWrite(i, 0);
        }

        Thread init = new Thread(new InitThread(), true);
        _NewThread(init);

        uint x = 0xe100;
        uint y = 0;
        while (true)
        {
            CompilerIntrinsics.Cli(); // TODO: superfluous
            NucleusCalls.VgaTextWrite(79, x);
            x++;

            // Schedule thread, wait for exception or interrupt
            ScheduleNextThread();

            // CurrentThread received exception, interrupt, or exited voluntarily
            uint cid = CurrentThread;
            Thread t = threadTable[cid];

            CompilerIntrinsics.Cli(); // TODO: superfluous
            uint cState = NucleusCalls.GetStackState(cid);
            if (cState == STACK_EMPTY)
            {
                // Thread received an exception.  Kill it.
                t.alive = false;
            }

            CompilerIntrinsics.Cli(); // TODO: superfluous
            if (t.alive)
            {
                // Thread was interrupted.  It's still ready to run.
                NucleusCalls.SendEoi();
                CheckWakeUp();
                CompilerIntrinsics.Cli(); // TODO: superfluous
                NucleusCalls.StartTimer(0);
                readyQueue.Enqueue(t);
            }
            else
            {
                NucleusCalls.VgaTextWrite(78, (uint)(0x5b00 + 0x1100 * (y++) + 48 + cid));
                // Thread is dead.  Dead threads always jump back to stack 0.
                threadTable[cid] = null;
                NucleusCalls.ResetStack(cid);
            }
        }
    }

    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    internal void EnqueueAndYield(ThreadQueue queue)
    {
        uint cid = CurrentThread;
        Thread current = threadTable[cid];
        queue.Enqueue(current);
        ScheduleNextThread();

        // We're back.  Somebody yielded to us.
    }

    private static uint gcCount;

    // Switch to the next ready thread.
    // (This may be called from stack 0 or from any thread.)
    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    internal void ScheduleNextThread()
    {
        Thread t = readyQueue.Dequeue();

        if (t == null)
        {
            if (collectionRequested)
            {
                CompilerIntrinsics.Cli(); // TODO: superfluous
                NucleusCalls.DebugPrintHex(70, ++gcCount);
                NucleusCalls.DebugPrintHex(60, 0);
                long t1 = NucleusCalls.Rdtsc();

                // No ready threads.
                // Make anyone waiting for GC ready:
                while (true)
                {
                    t = collectionQueue.Dequeue();
                    if (t == null)
                    {
                        break;
                    }
                    readyQueue.Enqueue(t);
                }

                t = readyQueue.Dequeue();

                // Garbage collect, then we're ready to go.
                NucleusCalls.GarbageCollect();
                collectionRequested = false;

                long t2 = NucleusCalls.Rdtsc();
                uint diff = (uint)((t2 - t1) >> 10);
                NucleusCalls.DebugPrintHex(60, diff);
            }

            while (t == null)
            {
                // TODO: let the CPU sleep here
                // TODO: enable interrupts
                CompilerIntrinsics.Cli(); // TODO: superfluous
                if (!CheckWakeUp())
                {
                    // No threads to run.  The system is finished.
                    CompilerIntrinsics.Cli(); // TODO: superfluous
                    NucleusCalls.DebugPrintHex(0, 0x76543210);
                    while (true) {}
                }

                t = readyQueue.Dequeue();
                CompilerIntrinsics.Cli(); // TODO: superfluous
            }
        }

        // Go to t.
        RunThread(t);

        // We're back.  Somebody (not necessarily t) yielded to us.
    }

    // Run a thread in a new scheduling quantum.
    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    private bool RunThread(Thread t)
    {
        uint id = t.id;
        CurrentThread = id;
        NucleusCalls.YieldTo(id);
        return true;
    }

    [InterruptsDisabled]
    private bool CheckWakeUp()
    {
        long now = GetUtcTimeInterruptsDisabled();
        bool foundSleeper = false;

        // TODO: more efficient data structure
        foreach (Thread t in threadTable)
        {
            if (t != null)
            {
                WakeUp wakeUp = t.wakeUp;
                if (wakeUp != null)
                {
                    foundSleeper = true;
                    if (now - wakeUp.time >= 0)
                    {
                        // time to wake up
                        wakeUp.queue.Remove(t);
                        t.wakeUp = null;
                        readyQueue.Enqueue(t);
                    }
                }
            }
        }

        return foundSleeper;
    }

    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    private void ThreadMain(uint id)
    {
        Thread t = threadTable[id];
        CompilerIntrinsics.Sti();
        t.start.Run();
        CompilerIntrinsics.Cli();
        t.alive = false;
        NucleusCalls.YieldTo(0);

        // Should never be reached:
        NucleusCalls.DebugPrintHex(0, 0xdead0002);
        while(true) {}
    }

    [InterruptsDisabled]
    private Thread _NewThread(Thread t)
    {
        for (uint i = 1; i < threadTable.Length; i++)
        {
            if (threadTable[i] == null)
            {
                t.id = i;
                threadTable[i] = t;
                readyQueue.Enqueue(t);
                return t;
            }
        }
        return null;
    }

    public Thread NewThread(ThreadStart start)
    {
        Thread t = new Thread(start);
        try
        {
            CompilerIntrinsics.Cli();
            return _NewThread(t);
        }
        finally
        {
            CompilerIntrinsics.Sti();
        }
    }

    public Semaphore NewSemaphore(int capacity)
    {
        return new Semaphore(new ThreadQueue(), capacity);
    }

    public void Yield()
    {
        try
        {
            CompilerIntrinsics.Cli();
            if (collectionRequested)
            {
                EnqueueAndYield(collectionQueue);
            }
            else
            {
                EnqueueAndYield(readyQueue);
            }
        }
        finally
        {
            CompilerIntrinsics.Sti();
        }
    }

    [RequiresInterruptsDisabled]
    [EnsuresInterruptsDisabled]
    public static void Collect()
    {
        kernel.collectionRequested = true;
        // Wait in the collectionQueue for the next GC.
        kernel.EnqueueAndYield(kernel.collectionQueue);
        // no sti needed here; we're returning to do another allocation anyway
    }

    // TODO: calibrate timing
    [InterruptsDisabled]
    internal static long GetUtcTimeInterruptsDisabled()
    {
        CompilerIntrinsics.Cli(); // TODO: superfluous
        long tsc = NucleusCalls.Rdtsc();
        return unchecked(tsc >> 8);
    }

    // TODO: calibrate timing
    public static long GetUtcTime()
    {
        long tsc = INucleusCalls.Rdtsc();
        return unchecked(tsc >> 8);
    }
}

