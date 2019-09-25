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
//          Scheduler.OnThreadFreezeDecrement(): Decr count, if 0 then unfreeze.
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
    using Microsoft.Singularity;
    using Microsoft.Singularity.Channels;
    using Microsoft.Singularity.Hal;
    using Microsoft.Singularity.Scheduling;
    using Microsoft.Singularity.Security;
    using Microsoft.Singularity.V1.Threads;
    using Microsoft.Singularity.Memory;
    using Microsoft.Singularity.Isal;
    using Microsoft.Bartok.Runtime;

    [CLSCompliant(false)]
    public enum ThreadEvent : ushort
    {
        CreateIdle = 12,
        Create = 13,
        WaitAny = 30,
        WaitFail = 31,
        SwitchTo = 3,
        ThreadPackageInit = 10
    }

    internal enum AbortRequestSource
    {
        ABIExit = 0,
        ABINoGCExit = 1,
        WaitHandle = 2,
    }

    ///
    /// <summary>
    /// Class implements thread functionality in Singluarity
    /// </summary>
    ///
    public sealed partial class Thread
    {

        ///
        /// <summary>
        /// Constructor to create a new thread
        ///</summary>
        ///
        /// <param name="process">A process to which thread belongs to</param>
        ///
        private Thread(Process process)
        {

            // Initialize thread fields to default values
            this.processThreadIndex = -1;
            this.threadIndex = -1;
            this.schedulerInfo.State = ThreadState.Unstarted;

            // Set up thread kernel mode information
            this.SetKernelMode();

            // Bind thread to a process
            this.process = process;

            // Bind thread to a proper scheduler
#if false
            if (process != null) {
                this.ScheduleData = process.DefaultScheduleData;
            }
#endif

            // Initialize context fields
            this.context.threadIndex = unchecked((ushort)-1);
            this.context.processThreadIndex = unchecked((ushort)-1);
            this.context.processId = unchecked((ushort)-1);
            Transitions.InitializeStatusWord(ref this.context);

            // Allocate the kernel objects needed by the thread.
            this.threadLock = new SpinLock(SpinLock.Types.Thread);
            this.autoEvent = new AutoResetEvent(false);
            this.joinEvent = new ManualResetEvent(false);
            this.localServiceRequest = new ThreadLocalServiceRequest();
            this.schedulerEntry = new ThreadEntry(this);
            this.timerEntry= new ThreadEntry(this);
            this.deferredEntry= new ThreadEntry(this);

            // Initialize wait entries cache so that we don't have to perform allocation in most
            // common case, when thread is waiting on single handle
            this.GetWaitEntries(1);

            // Try to put the thread in the thread table.
            bool saved = Processor.DisableInterrupts();
            threadTableLock.Acquire(CurrentThread);
            try {
                // Grab the first empty spot in thread table
                for (int i = 0; i < threadTable.Length; i++) {
                    // Calculate possible thread index starting from the last time success
                    int index = (threadIndexGenerator + i) % threadTable.Length;

                    // If none of the existing thread occupies this particular index use it:
                    if (threadTable[index] == null) {

                            // Bind table to our thread and our thread to table
                            threadTable[index] = this;
                            this.threadIndex = index;

                            // Remember last we visited this place
                            threadIndexGenerator = index + 1;

                            // NB: We call this once, subsequently the GC visitor calls it.
                            context.UpdateAfterGC(this);
                            break;
                   }
                }
            }
            finally {
                threadTableLock.Release(CurrentThread);
                Processor.RestoreInterrupts(saved);
            }

            // Assert that thread table is not full temporary before real fix
            VTable.Assert(this.threadIndex != -1);

            // Initialize context with proper thread index
            context.threadIndex = unchecked((ushort)(threadIndex));
            Transitions.InitializeStatusWord(ref context);

            // Bind context to a process if one exists
            if (process != null) {
                    context.processId = unchecked((ushort)(process.ProcessId));
            }

            // Initialize thread's stack.
            context.stackBegin = 0;
            context.stackLimit = 0;
        }

        ///
        /// <summary>
        /// Idle thread constructor, deligates major initialization to main constructor by
        /// using idle process
        ///</summary>
        ///
        /// <param name="idle">Indicates if thread is idle or not</param>
        ///
        protected Thread(bool idle)
            : this(Process.idleProcess)
        {
            // Initialize stack
            UIntPtr stackSegment = Stacks.GetInitialStackSegment(ref context);

            // At this point we can't fail
            DebugStub.Assert(stackSegment != UIntPtr.Zero);

#if PAGING
            // Initialize idle context
            context.InitializeIdle(threadIndex, stackSegment,
                                   unchecked((uint)Process.kernelProcess.Domain.AddressSpace.PdptPage.Value));
#else
            // Initialize idle context
            context.InitializeIdle(threadIndex, stackSegment, 0);
#endif
            // Record ilde thread creation event
            Monitoring.Log(Monitoring.Provider.Thread,
                           (ushort)ThreadEvent.CreateIdle, 0,
                           (uint)threadIndex, 0, 0, 0, 0);
        }

        ///
        /// <summary>
        /// A thread constructor with a start routine, deligates major initialization to main constructor by
        /// using idle process
        ///</summary>
        ///
        /// <param name="process">A process to which thread belongs to</param>
        /// <param name="start">Thread's start routine</param>
        ///
        protected Thread(Process process, ThreadStart start)
            : this(process)
        {
            // If no start routine specified throw exception
            if (start == null) {
                throw new ArgumentNullException("start");
            }

            // Initialize thread's start routine
            this.threadStart = start;

#if PAGING
            // In case of paging initialize abi stack
            this.context.abiStackHead = Stacks.GetStackSegment(0, ref context, true, false);
            this.context.abiStackBegin = this.context.stackBegin;
            this.context.abiStackLimit = this.context.stackLimit;
            this.context.stackBegin = 0;
            this.context.stackLimit = 0;
#endif
            // Allocation initial stack segment for the thread
            UIntPtr stackSegment = Stacks.GetInitialStackSegment(ref context);
            // Assert condition - no stack, no thread - is this really true?
            DebugStub.Assert(stackSegment != UIntPtr.Zero);
#if PAGING
            // Initialize context
            context.Initialize(threadIndex, stackSegment,
                               unchecked((uint)(Process.Domain.AddressSpace.PdptPage.Value)));
#else
            // Initialize context
            context.Initialize(threadIndex, stackSegment, 0);
#endif
            Monitoring.Log(Monitoring.Provider.Thread,
                           (ushort)ThreadEvent.Create, 0,
                           (uint)threadIndex, 0, 0, 0, 0);
        }

        ///
        /// <summary>
        /// An API to create a thread
        ///</summary>
        ///
        /// <param name="processor">An idle thread for a given processor </param>
        ///
        public static Thread CreateIdleThread(Processor processor)
        {
            // Allocate new idle thread.
            Thread idle = new Thread(true);
            idle.Affinity = processor.Id;

            // Check if new thread is valid
            if (idle.threadIndex < 0) {
                Tracing.Log(Tracing.Warning, "Thread table is full.");
                DebugStub.Break();
                return null;
            }

            return idle;
        }

        ///
        /// <summary>
        /// An API to create a thread
        ///</summary>
        ///
        /// <param name="process">A process to which thread belongs to</param>
        /// <param name="start">Thread's start routine</param>
        ///
        [Inline]
        public static Thread CreateThread(Process process, ThreadStart start)
        {
            return CreateThread(process, start, false);
        }

        ///
        /// <summary>
        /// An API to create a thread
        ///</summary>
        ///
        /// <param name="process">A process to which thread belongs to</param>
        /// <param name="start">Thread's start routine</param>
        /// <param name="needThreadHandle">Whether a thread handle should be created</param>
        ///
        public static Thread CreateThread(Process process, ThreadStart start, bool needThreadHandle)
        {
            ThreadHandle handle;

            // If no process specified use current one
            if (process == null) {
                process = CurrentProcess;
            }

            //Process can't be null from this point on
            VTable.Assert(process != null);

            // Allocate the thread.
            Thread thread = new Thread(process, start);

            // Check if thread is valid, return right a way if it is not
            if (thread.threadIndex < 0) {
                Tracing.Log(Tracing.Warning, "Thread table is full.");
                DebugStub.Break();
                return null;
            }

            // Add newly created thread to the process
            process.AddThread(thread, needThreadHandle);

            //MemoryBarrier();?

            // Notifiy perfcounters about thread creation
            PerfCounters.IncrementThreadsCreated();
            DebugStub.AddToPerfCounter(4, 1);

            return thread;
        }

        ///
        /// <summary>
        /// Retrieve thread's scheduler for a thread
        /// </summary>
        ///
        public ProcessorDispatcher Dispatcher
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.dispatcher;
            }

            [Inline]
            [NoHeapAllocation]
            set
            {
                this.dispatcher = value;
            }
        }

        ///
        /// <summary>
        /// Retrieve thread's scheduler info
        /// </summary>
        ///
        public SchedulerInfo ThreadSchedulerInfo
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.schedulerInfo;
            }
        }

        ///
        /// <summary>
        /// Find out if thread is suspended
        /// </summary>
        ///
        public bool IsSuspended
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return (this.schedulerInfo.State == ThreadState.Suspended);
            }
        }

        ///
        /// <summary>
        /// Find out if thread is blocked
        /// </summary>
        ///
        public bool IsBlocked
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.schedulerInfo.State == ThreadState.Blocked;
            }
        }

        ///
        /// <summary>
        ///    Check if thread is idle
        /// </summary>
        ///
        public bool IsIdle
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.type == ThreadType.Idle;
            }
        }

        ///
        /// <summary>
        ///    Check if thread is idle
        /// </summary>
        ///
        public bool IsScavenger
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.type == ThreadType.Scavenger;
            }
        }


        ///
        /// <summary>
        ///    Check if thread is idle
        /// </summary>
        ///
        public ThreadType Type
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.type;
            }

            [Inline]
            [NoHeapAllocation]
            set
            {
                this.type = value;;
            }
        }


        ///
        /// <summary>
        /// Find out if thread is runnable
        /// </summary>
        ///
        public bool IsRunnable
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.schedulerInfo.State == ThreadState.Runnable;
            }
        }

        ///
        /// <summary>
        /// Find out if thread is running
        /// </summary>
        ///
        public bool IsRunning
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.schedulerInfo.State == ThreadState.Running;
            }
        }


        ///
        /// <summary>
        /// Find out who unblocked the thread
        /// </summary>
        ///
        public int UnblockedBy
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.schedulerInfo.UnblockedBy;
            }

            [Inline]
            [NoHeapAllocation]
            set
            {
                this.schedulerInfo.UnblockedBy = value;
            }
        }

        ///
        /// <summary>
        /// Find out thread freeze count
        /// </summary>
        ///
        public int FreezeCount
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return this.schedulerInfo.FreezeCount;
            }
        }

        ///
        /// <summary>
        /// Spawns off a new thread which will begin executing at the
        /// ThreadStart delegate passed in the constructor. Once the thread is
        /// dead, it cannot be restarted with another call to Start.
        /// </summary>
        ///
        public void Start()
        {
            // Notify process that thread is about to start
            process.StartThread();

            // Go ahead and start thread - attach it scheduler and start running
            StartRunningThread();
        }

        ///
        /// <summary>
        /// Start running main thread inside of process
        /// </summary>
        ///
        ///<remark> precondition: process.processLock held </remark>
        internal void SetMainThreadRunning()
        {
            VTable.Assert(this.ThreadState == ThreadState.Unstarted);
            process.StartMainThread();
        }

        ///
        /// <summary>
        /// Start thread running: Attach to GC and process's scheduler
        /// </summary>
        ///
        internal void StartRunningThread()
        {
            VTable.Assert(this.ThreadState == ThreadState.Unstarted);

            // Tell the GC that we have created the thread
            GC.NewThreadNotification(this, false);

            // Tell the scheduler to initialize the thread.
            Kernel.TheScheduler.OnThreadStateInitialize(this, true);

            // Let scheduler start thread: Scheduler is responsible for changing thread state
            Kernel.TheScheduler.OnThreadStart(this);
        }

        ///
        /// <summary>
        /// An entry point for an idle thread. ThreadContext.InitializeIdle sets
        /// DispatcherThreadStub as the first instruction to be executed in a new thread context.
        /// </summary>
        ///
        /// <remarks>
        /// There are currently only two dispatcher threads: Idle and Scavenger. Both
        /// of them are created during processor startup
        /// </remarks>
        ///
        /// <param name="index">An index represents a thread we are starting</param>
        ///
        [AccessedByRuntime("referenced from c++")]
        private static unsafe void DispatcherThreadStub(int index)
        {
            Thread currentThread = Thread.CurrentThread;

            // Assert preconditions: Thread should be really one of dispatcher threads
            VTable.Assert(threadTable[index] == currentThread);
            VTable.Assert(
                Processor.CurrentProcessor.Dispatcher.IsOneOfMyDispatcherThreads(currentThread));;

            // If processor idle use idle loop otherwise use scavanager loop
            if (Processor.CurrentProcessor.Dispatcher.IsMyIdleThread(currentThread)) {
                // Mark thread idle before running
                Thread.CurrentThread.Type = ThreadType.Idle;
                ProcessorDispatcher.IdleThreadLoop();
            }
            else {
                Thread.CurrentThread.Type = ThreadType.Scavenger;
                // This is a scavanger thread so use the appropriate loop
                ProcessorDispatcher.ScavengerThreadLoop();
            }
        }

        ///
        /// <summary>
        /// An entry point for any thread.  ThreadContext.Initialize sets ThreadStub as
        /// the first instruction to be executed in a new thread context.
        /// </summary>
        ///
        /// <param name="threadIndex">An index represents a thread we are starting</param>
        ///
        [AccessedByRuntime("referenced from c++")]
        private static unsafe void ThreadStub(int threadIndex)
        {
            Thread currentThread = threadTable[threadIndex];

            // Give our Protection Domain a chance to set up
            // if we're first in here. Run this before anything
            // else!
            currentThread.process.Domain.InitHook();

            // Attach thread to GC
            Transitions.ThreadStart();
            GC.ThreadStartNotification(threadIndex);

            Tracing.Log(Tracing.Trace, "ThreadStub() entered");
            ThreadStart startFun = currentThread.threadStart;

            // Initialize procesor FPU
            Isa.InitFpu();

            // Start an entry point of actual thread
            try {
                startFun();
            }
            catch (ProcessStopException) {
                // Stop exception is the only "good" exception expect at this point
                // Ok, exit thread without failure.
            }
            catch (Exception e) {
                // Not ok, fail: This is pretty much unhandled exception
                Tracing.Log(Tracing.Notice,
                            "Thread failed with exception {0}.{1}",
                            e.GetType().Namespace, e.GetType().Name);
                Tracing.Log(Tracing.Trace, "Exception message was {0}",
                            e.Message);
                DebugStub.Assert(e == null,
                                 "Thread {0} failed w/ exception {1}.{2}: {3}",
                                 __arglist(threadIndex,
                                           e.GetType().Namespace,
                                           e.GetType().Name,
                                           e.Message));
            }

            Tracing.Log(Tracing.Trace, "{0:x} ThreadStub() stopping",
                        Kernel.AddressOf(currentThread));

            // We are done: stop thread and disassociate it from scheduler
            Kernel.TheScheduler.OnThreadStop(currentThread);
        }

        ///
        /// <summary>
        /// Service a stop thread - Method perfoms final tearing down of thread it is called
        /// on special service thread.
        /// </summary>
        ///
        internal void ServiceStopped()
        {
            // Make sure ThreadStub has gotten a chance to exit before
            // we deallocate its stack:
            bool wasUnstarted;

            // Indicate all waiters on this thread that we are done
            joinEvent.Set();

            // Make sure nobody else has access to the thread
            bool saved = Processor.DisableInterrupts();
            this.threadLock.Acquire();
            try {
                // Thread might have never started
                wasUnstarted = (this.ThreadState == ThreadState.Unstarted);

                // If thread has never started set state by hand to stopped
                if (wasUnstarted) {
                    this.schedulerInfo.State = ThreadState.Stopped;
                }

            }
            finally {
                this.threadLock.Release();
                Processor.RestoreInterrupts(saved);
            }


            // Asssert preconditions
            VTable.Assert(this.ThreadState == ThreadState.Stopped);
            VTable.Assert(threadIndex > 0);

            // Notify GC that thread is tearing down
            if (!wasUnstarted) {
                if (Transitions.InMutatorState(GetThreadId())){
                    Transitions.ThreadEnd(GetThreadId());
                }
                GC.DeadThreadNotification(this);
            }

            int count = 0;
#if !PAGING
            while (context.stackBegin != 0) {

                if (count == 0) {
                    Stacks.ReturnInitialStackSegment(ref context);
                }
                else {
                    Stacks.ReturnStackSegment(ref context);
                }

                count++;
            }
#else
            // Free up stack
            while (context.stackBegin != 0) {

                // HACK: if the thread stops abruptly, the stack may contain the abi segment
                if (context.stackBegin == context.abiStackBegin) {
                    context.abiStackBegin = 0;
                    context.abiStackLimit = 0;
                }

                if (count == 0) {
                    // First segment is reported to balance AllocateInitialStackSegment
                    Stacks.ReturnInitialStackSegment(ref context);
                }
                else {
                    Stacks.ReturnStackSegment(ref context);
                }
                count++;
            }
#endif

            VTable.Assert(context.stackLimit == 0);
            VTable.Assert(context.stackBegin == 0);

#if PAGING
            // See HACK above for why abiStackBegin may be 0
            if (context.abiStackBegin != 0) {
                context.stackLimit = context.abiStackLimit;
                context.stackBegin = context.abiStackBegin;
                Stacks.ReturnStackSegment(ref context);
            }
#endif

            Thread currentThread = Thread.CurrentThread;

            // Free up table index
            saved = Processor.DisableInterrupts();
            threadTableLock.Acquire(currentThread);

            try {
                threadTable[threadIndex] = null;
                Transitions.DeadThreadNotification(threadIndex);
            }
            finally {
                threadTableLock.Release(currentThread);
                Processor.RestoreInterrupts(saved);
            }

            if (process != null) {
                process.ServiceOnThreadStop(this);
            }
        }

        ///
        /// <summary>
        /// Thread is alive only if it has been started and it is not stopped. There is no
        /// gurantee as this call returns thread will stay alive. You will need to provide extra
        /// synchronization
        /// </summary>
        ///
        public bool IsAlive
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return (this.ThreadState != ThreadState.Unstarted &&
                       this.ThreadState != ThreadState.Stopped);
            }
        }

        ///
        /// <summary>
        /// Wait for thread to stop
        /// </summary>
        ///
        /// <remark>
        /// Exceptions: ThreadStateException if the thread has not been started yet.
        /// </remark>
        public void Join()
        {
            Join(SchedulerTime.MaxValue);
        }

        ///
        /// <summary>
        /// Wait for thread to stop or specified timeout expires
        /// </summary>
        ///
        /// <remark>
        /// Exceptions: ThreadStateException if the thread has not been started yet.
        /// </remark>
        public bool Join(TimeSpan timeout)
        {
            if (this.ThreadState == ThreadState.Unstarted) {
                throw new ThreadStateException();
            }
            else if (this.ThreadState == ThreadState.Stopped) {
                return true;
            }
            return joinEvent.WaitOne(timeout);
        }

        ///
        /// <summary>
        /// Wait for thread to stop or specified timeout expires
        /// </summary>
        ///
        /// <remark>
        /// Exceptions: ThreadStateException if the thread has not been started yet.
        /// </remark>
        public bool Join(SchedulerTime timeout)
        {
            if (this.ThreadState == ThreadState.Unstarted) {
                throw new ThreadStateException();
            }
            else if (this.ThreadState == ThreadState.Stopped) {
                return true;
            }
            return joinEvent.WaitOne(timeout);
        }

        ///
        /// <summary>
        /// Set thread's affinity
        /// </summary>
        ///
        public void SetAffinity(int affinity)
        {
            // Affinity can only be changed when it has not been set
            if (Affinity == NoAffinity) {
                Affinity = affinity;
            }
        }

        //////////////////////////////////////////////////////////////////////
        // Suspends the current thread for timeout milliseconds. If timeout
        // == 0, forces the thread to give up the remainder of its timeslice.
        //
        // Exceptions: ArgumentException if timeout < 0.
        //
        public static void Sleep(int milliseconds)
        {
            Sleep(TimeSpan.FromMilliseconds(milliseconds));
        }

        //| <include path='docs/doc[@for="Thread.Sleep"]/*' />
        public static void Sleep(SchedulerTime stop)
        {
            Tracing.Log(Tracing.Audit, "Sleep until stop");
            WaitHandle.WaitAny(null, 0, stop);
            Tracing.Log(Tracing.Audit, "Sleep until stop finished");
        }

        //| <include path='docs/doc[@for="Thread.Sleep"]/*' />
        public static void Sleep(TimeSpan timeout)
        {
            Tracing.Log(Tracing.Audit, "Sleep until time");
            SchedulerTime stop = SchedulerTime.Now + timeout;
            Thread.CurrentThread.WaitAny(null, 0, stop);
            Tracing.Log(Tracing.Audit, "Sleep until time finished");
        }

        //////////////////////////////////////////////////////////////////////
        // Wait for a length of time proportional to 'iterations'.  Each
        // iteration is should only take a few machine instructions.  Calling
        // this method is preferable to coding a explicit busy loop because the
        // hardware can be informed that it is busy waiting.
        //
        //| <include path='docs/doc[@for="Thread.SpinWait"]/*' />
        [NoHeapAllocation]
        public static void SpinWait(int iterations)
        {
            for (int i = iterations; i > 0; i--) {
                // Ensure that the optimizer doesn't remove this
                NativeNoOp();
            }
        }

        [Intrinsic]
        [NoHeapAllocation]
        public static extern void NativeNoOp();

        internal static int GetCurrentProcessIndex() {
            return Thread.CurrentProcess.ProcessId;
        }

        internal bool WaitForMonitor(SchedulerTime stop)
        {
            return autoEvent.WaitOne(stop);
        }

        internal bool WaitForEvent(SchedulerTime stop)
        {
            return autoEvent.WaitOne(stop);
        }

        internal bool WaitForEvent(TimeSpan timeout)
        {
            return autoEvent.WaitOne(timeout);
        }

        internal static void WaitForGCEvent(int currentThreadIndex)
        {
            Thread.WaitForGCEvent(currentThreadIndex, SchedulerTime.MaxValue);
        }

        internal static void WaitForGCEvent(int currentThreadIndex, int millis)
        {
            SchedulerTime stop = SchedulerTime.Now.AddMilliseconds(millis);
            Thread.WaitForGCEvent(currentThreadIndex, stop);
        }


        ///
        /// <summary>
        /// Signal thread's GC event, we can't use actual event object as it might allow
        /// unneccesasry reentrancy.
        /// </summary>
        ///
        [Inline]
        internal static void SignalGCEvent(int threadIndex) {
            SignalGCEvent(Thread.GetCurrentThreadIndex(), threadIndex);
        }

        ///
        /// <summary>
        /// Wait for GC - method is called by GC to park thread while GC is up and running
        /// At this point we chose not to use autoresetevent as it might introduce reentrancy.
        /// In this method we closely mimic to what we are doing in WaitAny when waiting on handles
        /// </summary>
        ///
        private static void WaitForGCEvent(
            int             currentThreadIndex,
            SchedulerTime   stop)
        {
            Thread  currentThread = threadTable[currentThreadIndex];

            Tracing.Log(Tracing.Audit, "WaitForGCEvent({0})",
                        (UIntPtr) currentThreadIndex);
            VTable.Deny(ProcessorDispatcher.IsIdleThread(currentThreadIndex));

            while (true) {
                // Attempt to reset the one-shot from true to false
                if (Interlocked.CompareExchange(ref currentThread.gcEventSignaled,
                                                0,
                                                1) == 1) {
                    break;
                }
                // If we failed, yield the processor.  Eventually we will block, but the
                // dispatcher doesn't yet provide a suitable blocking primitive below the
                // scheduler -- beyond perhaps Suspend.
                Yield();
            }
        }

        ///
        /// <summary>
        /// Signal thread's GC event. For more information see WaitForGCEvent
        /// </summary>
        ///
        internal static void SignalGCEvent(int currentThreadIndex,int threadIndex)
        {
            Thread  currentThread = threadTable[threadIndex];

            Tracing.Log(Tracing.Audit, "SignalGCEvent({0})",
                        (UIntPtr) threadIndex);
            VTable.Deny(ProcessorDispatcher.IsIdleThread(threadIndex));

            if (currentThread != null) {
                Interlocked.Exchange(ref currentThread.gcEventSignaled, 1);
            }
        }

        internal void SignalEvent()
        {
            this.autoEvent.Set();
        }

        internal void SignalMonitor()
        {
            this.autoEvent.Set();
        }

        //| <include path='docs/doc[@for="Thread.CurrentThread"]/*' />
        public static extern Thread CurrentThread
        {
            [NoStackLinkCheck]
            [NoHeapAllocation]
            [Intrinsic]
            get;
        }

        public static Process CurrentProcess
        {
            [NoStackLinkCheckTrans]
            [NoHeapAllocation]
            get {
                return Processor.GetCurrentThread().process;
            }
        }

        public Process Process
        {
            [NoHeapAllocation]
            get { return process; }
        }

        public ThreadHandle Handle
        {
            [NoHeapAllocation]
            get { return threadHandle; }
        }

        [NoStackLinkCheckTrans]
        [RequiredByBartok]
        [NoHeapAllocation]
        public static int GetCurrentThreadIndex()
        {
            return Processor.GetCurrentThread().threadIndex;
        }

        [NoStackLinkCheckTrans]
        [RequiredByBartok]
        [NoHeapAllocation]
        private static Thread GetCurrentThreadNative()
        {
            return Processor.GetCurrentThread();
        }

        [NoHeapAllocation]
        public static UIntPtr GetThreadLocalValue()
        {
            return Processor.GetCurrentThread().threadLocalValue;
        }

        [NoHeapAllocation]
        public static void SetThreadLocalValue(UIntPtr value)
        {
            Processor.GetCurrentThread().threadLocalValue = value;
        }

        ///
        /// <summary>
        /// Retrieve thread's state
        /// </summary>
        ///
        public ThreadState ThreadState
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return schedulerInfo.State;
            }
        }

        [NoHeapAllocation]
        public int GetThreadId()
        {
            return threadIndex;
        }

        // Return true if the thread is in kernel mode, false if the
        // thread is in process mode.
        // Note that by the time this method returns, the thread might
        // have already switched to a different mode; in other words,
        // don't rely on this result of this method being up-to-date unless
        // the thread is suspended or blocked.
        [NoHeapAllocation]
        public unsafe bool IsInKernelMode()
        {
            return context.IsInKernelMode();
        }

        [NoHeapAllocation]
        internal unsafe void SetKernelMode()
        {
            context.SetKernelMode();
        }

        [NoHeapAllocation]
        internal unsafe void SetProcessMode()
        {
            context.SetProcessMode();
        }

        ///
        /// <summary>
        /// Suspend thread and wait till it is suspended
        /// </summary>
        ///
        internal void Suspend(bool aboutToStop)
        {
            Kernel.TheScheduler.Suspend(this);
        }

        ///
        /// <summary>
        /// Resume thread
        /// </summary>
        ///
        internal void Resume()
        {
            Kernel.TheScheduler.Resume(this);
        }

        ///
        /// <summary>
        /// Handle abort - if abort is requested for the current thread, calling this
        /// method stops the thread immediately. Note this method can only be called
        /// by the current thread
        /// </summary>
        ///
        /// <param name="source"> Where the request come from, for debugging purpose</param>
        ///
        [Inline]
        [NoHeapAllocation]
        internal void ProcessAbortIfRequested(AbortRequestSource source)
        {
            // TODO: This exists with no
            // code as a means of getting an updated Bartok in
            // the tree - the added files in the process call
            // this method and the files can't be edited until
            // checked in.
#if false
            // Assert preconditions: This method can only be called by the current thread
            VTable.Assert(this == Thread.CurrentThread);

            // If the thread is requested to abort, stop it now
            if (IsAbortRequested) {

                // We are done: stop thread and disassociate it from scheduler
                Scheduler.OnThreadStop(this);
            }
#endif // false
        }

        ///
        /// <summary>
        /// Abort thread - thread will be aborted right a way unless dealy abort bit is set
        /// </summary>
        ///
        internal void Stop()
        {
            // First make sure that thread is stable - suspended
            Suspend(false);

            // Now we can stop thread
            StopSuspended();
        }

        ///
        /// <summary>
        /// Abort suspended thread - thread will be aborted right a way unless dealy abort bit is set
        /// Once stop call is processed, thread will be resumed to finish stop
        /// </summary>
        ///
        internal void StopSuspended()
        {
            bool    shouldResumeAtTheEnd = true;
            // Once thread is supsended - turn on abort
            Abort();

            // If thread is not stopped already and is not blocked and not in delay abort scope unblock it
            if (!IsStopped() && !IsAbortDelayed()) {
                // Try to unblock it if it is blocked
                if (this.UnblockedBy == WaitHandle.UninitWait) {
                        // Just go ahead and try to unblock it if we succesfuly thread will be
                        // aborted after resume
                        if (Unblock(WaitHandle.UnblockedByAbort) == WaitHandle.UnblockedByAbort &&
                            ShouldCallSchedulerUnBlock(WaitHandle.UnblockedByAbort)) {

                            // Before we can unblock thread we have to resume it -currently
                            // we don't have a way of going from block and suspend state back
                            // and forward:
                            Resume();

                            // Now are ready to unblock it
                            Kernel.TheScheduler.OnThreadUnblocked(this);

                            shouldResumeAtTheEnd = false;
                        }
                }
            }

            // We are done with thread just resume it
            if (shouldResumeAtTheEnd) {
                Resume();
            }
        }

        ///
        /// <summary>
        /// Move thread abort status to abort state
        /// </summary>
        ///
        private void Abort()
        {
            SchedulerInfo     newInfo;
            SchedulerInfo     oldInfo;

            do {
                // Copy scheduler state to memory
                newInfo = this.schedulerInfo;
                oldInfo = newInfo;

                // Mark thread as aborted
                newInfo.IsAborted = true;

            // Attempt to update atomicatlly the state.
            } while (oldInfo.Data != Interlocked.CompareExchange(ref this.schedulerInfo.Data,
                                                                 newInfo.Data,
                                                                 oldInfo.Data));
            return;
        }

        ///
        /// <summary>
        /// Handle Abort - if abort is set and we are not in dealy abort scope throw
        /// abort exception
        /// </summary>
        ///
        internal void ProcessAbortIfRequired()
        {
            // Assert preconditions: This method can only be called by the current thread
            VTable.Assert(this == Thread.CurrentThread);

            // If thread is aborted and abort is not delayed handle it!
            if (ShouldStop()) {
                // Stop if we have to

                // We are done: stop thread and disassociate it from scheduler
                Kernel.TheScheduler.OnThreadStop(this);
            }
            return;
        }

        ///
        /// <summary>
        /// Enable/Disable delay abort on the thread depending on the passed in flag
        /// </summary>
        ///
        /// <param name="shouldDelayAbort">Flag indicating if abort has to be enabled or disabled </param>
        ///
        [NoHeapAllocation]
        internal void DelayStop(bool shouldDelayAbort)
        {
            SchedulerInfo     newInfo;
            SchedulerInfo     oldInfo;

            do {
                // Copy scheduler state to memory
                newInfo = this.schedulerInfo;
                oldInfo = newInfo;

                // Check the abort direction - enabling or disabling
                if (shouldDelayAbort) {
                    // We are enabling abort
                    newInfo.IncrementDelayAbortCount();
                }
                else {
                    // We are disabling abort
                    newInfo.DecrementDelayAbortCount();
                }

            // Attempt to update atomicatlly the state.
            } while (oldInfo.Data != Interlocked.CompareExchange(ref this.schedulerInfo.Data,
                                                                 newInfo.Data,
                                                                 oldInfo.Data));
        }

        ///
        /// <summary>
        /// Handle Abort - if abort is set and we are not in dealy abort scope throw
        /// abort exception
        /// </summary>
        ///
        [Inline]
        [NoHeapAllocation]
        internal bool ShouldStop()
        {
            // Check if thread has to be stopped
            return (IsAborted() && !IsAbortDelayed());
        }

        ///
        /// <summary>
        /// Check if we can abort thread
        /// </summary>
        ///
        [NoHeapAllocation]
        internal bool IsAbortDelayed()
        {
            return this.schedulerInfo.DelayAbortCount > 0;
        }

        ///
        /// <summary>
        /// Check if thread has abort bit set
        /// </summary>
        ///
        [NoHeapAllocation]
        internal bool IsAborted()
        {
            return this.schedulerInfo.IsAborted;
        }

        ///
        /// <summary>
        /// Notify thread that it acquired spinlock of specific rank
        /// </summary>
        ///
        /// <param name="type">Type of a spinlock </param>
        ///
        [NoHeapAllocation]
        internal void NotifySpinLockAboutToAcquire(int type)
        {
            int rank = SpinLock.DeriveRank(type);

            // Assert preconditions - we can't acquire spinlocks of the lower rank than we already
            // acquired
            VTable.Assert(rank == (int) SpinLock.Ranks.NoRank ||
                        this.spinLockRankMask == (int) SpinLock.Ranks.NoRank ||
                        this.spinLockRankMask > rank);
            VTable.Assert(Processor.InterruptsDisabled());

            // Record rank
            this.spinLockRankMask |= rank;

            // Update number of spinlocks held - we have to do until we remove NoRank...
            this.numberOfSpinlocksHeld++;

            // If spinlock has a rank higher than dispatcher, we need to mark thread for delay
            // abortion
            if (rank == (int)SpinLock.Ranks.NoRank || rank > (int)SpinLock.Ranks.Dispatcher) {
                DelayStop(true);
            }
        }

        ///
        /// <summary>
        /// Notify thread that released a spinlock of specific rank
        /// </summary>
        ///
        /// <param name="type">Type of a spinlock </param>
        ///
        [NoHeapAllocation]
        internal void NotifySpinLockReleased(int type)
        {
            VTable.Assert(Processor.InterruptsDisabled());

            int rank = SpinLock.DeriveRank(type);

            // Assert preconditions: We can't release multiple ranks at the same time: There should
            // be only a single bit set for the rank. The following calculation turns off a least
            // significant bit: x & (x-1) and hence the assert:
            VTable.Assert((rank & (rank-1)) == 0);

            // We can't release spinlocks out of order. The calculation below
            // relies on the following property of bitmask operations:If we turn off least significant bit
            // and then or it with the rank we are releasing, we should get the same mask as we head
            // before. To turn off least significant bit we use operation such as x = x&(x-1). If
            // spinlocks released out of order we will turn off least significant bit other than
            // rank we about to release so when we apply or with rank to the result we won't get
            // the same mask back.

            VTable.Assert(rank == (int)SpinLock.Ranks.NoRank ||
                        this.spinLockRankMask == (
                        (this.spinLockRankMask & (this.spinLockRankMask-1)) | rank));

            // We should have acquired spinlock of such rank before
            VTable.Assert(rank == (int)SpinLock.Ranks.NoRank ||
                        (this.spinLockRankMask & rank) != 0);

            // Turn off specified rank
            this.spinLockRankMask ^= rank;

            // Update number of spinlocks held - we have to do until we remove NoRank...
            this.numberOfSpinlocksHeld--;

            // If spinlock has a rank higher than dispatcher , we need to mark thread that
            // it can be stopped
            if (rank == (int)SpinLock.Ranks.NoRank || rank > (int)SpinLock.Ranks.Dispatcher) {
                DelayStop(false);
            }
        }

        ///
        /// <summary>
        /// Given a thread id return thread
        /// </summary>
        ///
        /// <param name="threadId">Thread Id</param>
        ///
        [NoHeapAllocation]
        internal static Thread GetThreadFromThreadId(int threadId)
        {
            // Assert preconditions: threadId has to be in range and thread can't be null
            VTable.Assert(threadId < threadTable.Length);
            VTable.Assert(threadTable[threadId] != null);

            return threadTable[threadId];
        }


        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(4)]
        private static extern void setStopContext(Thread t, Exception exn);

        //////////////////////////////////////////////////////////////////////
        // Allocates an un-named data slot. The slot is allocated on ALL the
        // threads.
        //| <include path='docs/doc[@for="Thread.AllocateDataSlot"]/*' />
        public static LocalDataStoreSlot AllocateDataSlot()
        {
            return localDataStoreMgr.AllocateDataSlot();
        }

        //////////////////////////////////////////////////////////////////////
        // Allocates a named data slot. The slot is allocated on ALL the
        // threads.  Named data slots are "public" and can be manipulated by
        // anyone.
        //| <include path='docs/doc[@for="Thread.AllocateNamedDataSlot"]/*' />
        public static LocalDataStoreSlot AllocateNamedDataSlot(String name)
        {
            return localDataStoreMgr.AllocateNamedDataSlot(name);
        }

        //////////////////////////////////////////////////////////////////////
        // Looks up a named data slot. If the name has not been used, a new
        // slot is allocated.  Named data slots are "public" and can be
        // manipulated by anyone.
        //| <include path='docs/doc[@for="Thread.GetNamedDataSlot"]/*' />
        public static LocalDataStoreSlot GetNamedDataSlot(String name)
        {
            return localDataStoreMgr.GetNamedDataSlot(name);
        }

        //////////////////////////////////////////////////////////////////////
        // Frees a named data slot. The slot is allocated on ALL the
        // threads.  Named data slots are "public" and can be manipulated by
        // anyone.
        //| <include path='docs/doc[@for="Thread.FreeNamedDataSlot"]/*' />
        public static void FreeNamedDataSlot(String name)
        {
            localDataStoreMgr.FreeNamedDataSlot(name);
        }

        //////////////////////////////////////////////////////////////////////
        // Retrieves the value from the specified slot on the current thread.
        //| <include path='docs/doc[@for="Thread.GetData"]/*' />
        public static Object GetData(LocalDataStoreSlot slot)
        {
            localDataStoreMgr.ValidateSlot(slot);

            if (localDataStore != null) {
                return localDataStore.GetData(slot);
            }
            return null;
        }

        //////////////////////////////////////////////////////////////////////
        // Sets the data in the specified slot on the currently running thread.
        //| <include path='docs/doc[@for="Thread.SetData"]/*' />
        public static void SetData(LocalDataStoreSlot slot, Object data)
        {
            // Create new DLS if one hasn't been created for this thread.
            if (localDataStore == null) {
                localDataStore = localDataStoreMgr.CreateLocalDataStore();
            }
            localDataStore.SetData(slot, data);
        }

        internal Object ExceptionState
        {
            [NoHeapAllocation]
            get { return exceptionStateInfo;}
            [NoHeapAllocation]
            set { exceptionStateInfo = value;}
        }

        //
        // This is just designed to prevent compiler warnings.
        // This field is used from native, but we need to prevent the compiler warnings.
        //
#if _DEBUG
        private void DontTouchThis()
        {
            threadStart = null;
            m_Priority = 0;
        }
#endif
        //////////////////////////////////////////////////////////////////////
        // Volatile Read & Write and MemoryBarrier methods.
        // Provides the ability to read and write values ensuring that the values
        // are read/written each time they are accessed.
        //

        //| <include path='docs/doc[@for="Thread.VolatileRead"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern byte VolatileRead(ref byte address);

        //| <include path='docs/doc[@for="Thread.VolatileRead1"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern short VolatileRead(ref short address);

        //| <include path='docs/doc[@for="Thread.VolatileRead2"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern int VolatileRead(ref int address);

        //| <include path='docs/doc[@for="Thread.VolatileRead3"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern long VolatileRead(ref long address);

        //| <include path='docs/doc[@for="Thread.VolatileRead4"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern sbyte VolatileRead(ref sbyte address);

        //| <include path='docs/doc[@for="Thread.VolatileRead5"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern ushort VolatileRead(ref ushort address);

        //| <include path='docs/doc[@for="Thread.VolatileRead6"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern uint VolatileRead(ref uint address);

        //| <include path='docs/doc[@for="Thread.VolatileRead7"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern IntPtr VolatileRead(ref IntPtr address);

        //| <include path='docs/doc[@for="Thread.VolatileRead8"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern UIntPtr VolatileRead(ref UIntPtr address);

        //| <include path='docs/doc[@for="Thread.VolatileRead9"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern ulong VolatileRead(ref ulong address);

        //| <include path='docs/doc[@for="Thread.VolatileRead10"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern float VolatileRead(ref float address);

        //| <include path='docs/doc[@for="Thread.VolatileRead11"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern double VolatileRead(ref double address);

        //| <include path='docs/doc[@for="Thread.VolatileRead12"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern Object VolatileRead(ref Object address);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern byte VolatileReadUnsafe(byte* address);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern short VolatileReadUnsafe(short* address);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern int VolatileReadUnsafe(int* address);

        //| <include path='docs/doc[@for="Thread.VolatileWrite"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref byte address, byte value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite1"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref short address, short value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite2"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref int address, int value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite3"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref long address, long value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite4"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref sbyte address, sbyte value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite5"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref ushort address, ushort value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite6"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref uint address, uint value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite7"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref IntPtr address, IntPtr value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite8"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref UIntPtr address, UIntPtr value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite9"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref ulong address, ulong value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite10"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref float address, float value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite11"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref double address, double value);

        //| <include path='docs/doc[@for="Thread.VolatileWrite12"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void VolatileWrite(ref Object address, Object value);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern void VolatileWriteUnsafe(int* address,
                                                               int value);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern void VolatileWriteUnsafe(short* address,
                                                               short value);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern void VolatileWriteUnsafe(byte* address,
                                                               byte value);

        //| <include path='docs/doc[@for="Thread.MemoryBarrier"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public static extern void MemoryBarrier();

        [NoHeapAllocation]
        internal static unsafe void DisplayAbbrev(ref ThreadContext context, String s)
        {
            fixed (ThreadContext * pContext = &context) {
                DebugStub.Print("{0}: ctx={1:x8} esp={2:x8} ebp={3:x8} eip={4:x8} " +
                                "thr={5:x8} efl={6:x8} p={7:x8} n={8:x8}\n",
                                __arglist(
                                    s,
                                    (UIntPtr)pContext,
                                    context.threadRecord.spill.StackPointer,
                                    context.threadRecord.spill.FramePointer,
                                    context.threadRecord.spill.InstructionPointer,
                                    Kernel.AddressOf(context.thread),
                                    context.threadRecord.spill.Flags,
                                    (UIntPtr)context.prev,
                                    (UIntPtr)context.next));
            }
        }

        [NoHeapAllocation]
        internal static unsafe void TraceAbbrev(ref ThreadContext context, String s)
        {
            fixed (ThreadContext* pContext = &context)
            {
                Tracing.Log(Tracing.Debug, s);
                context.threadRecord.spill.Trace();
            }
        }

        [NoHeapAllocation]
        internal static unsafe void Display(ref ThreadContext context, String s)
        {
            fixed (ThreadContext * pContext = &context) {
                DebugStub.Print("{0}: ctx={1:x8} num={2:x2}\n",
                                __arglist(
                                    s,
                                    (UIntPtr)pContext,
                                    context.num));
            }

            DebugStub.Print("  thr={0:x8} prv={1:x8} nxt={2:x8}\n",
                            __arglist(
                                (UIntPtr)Kernel.AddressOf(context.thread),
                                (UIntPtr)context.prev,
                                (UIntPtr)context.next));

            context.threadRecord.spill.Display();

        }

        ///////////////////////////////////////////////// Blocking operatings.
        //
        internal int WaitAny(WaitHandle[] waitHandles,
                             int waitHandlesCount,
                             TimeSpan timeout)
        {

            SchedulerTime stop;

            if (timeout != TimeSpan.MaxValue) {
                stop = SchedulerTime.Now + timeout;
            }
            else {
                stop = SchedulerTime.MaxValue;
            }
            return WaitHandle.WaitAny(waitHandles, waitHandlesCount, stop);
        }

        internal int WaitAny(WaitHandle[] waitHandles,
                             int waitHandlesCount,
                             SchedulerTime stop)
        {
            return WaitHandle.WaitAny(waitHandles, waitHandlesCount, stop);
        }

        [NoHeapAllocation]
        public static void Yield()
        {
            Kernel.TheScheduler.OnThreadYield(CurrentThread);
        }

        [NoHeapAllocation]
        public bool IsWaiting()
        {
            return IsBlocked;
        }

        [NoHeapAllocation]
        public bool IsStopped()
        {
            return (this.schedulerInfo.State == ThreadState.Stopped);
        }

        [NoHeapAllocation]
        public bool IsStopping()
        {
            return IsStopped();
        }

        [PreInitRefCounts]
        static unsafe Thread()
        {
            threadIndexGenerator = 1;

            DebugStub.Print("Thread()");

            // Enable Thread.CurrentThread as soon as we can!
            initialThread = Magic.toThread(GCs.BootstrapMemory.Allocate(typeof(Thread)));
            initialThread.schedulerInfo.State = ThreadState.Running;
            initialThread.SetKernelMode();
            initialThread.threadIndex = 0;

            // Allocate tables for thread management
            threadTableLock = new SpinLock(SpinLock.Types.ThreadTable);
            threadTable = (Thread[])
                GCs.BootstrapMemory.Allocate(typeof(Thread[]), maxThreads);

            // Initialize the thread and event tables
            threadTable[initialThread.threadIndex] = initialThread;

            initialThread.context.threadIndex =
                unchecked((ushort)(initialThread.threadIndex));
            Transitions.InitializeStatusWord(ref initialThread.context);
            initialThread.context.processId = unchecked((ushort)(1));

            // Prevent stack linking.
            initialThread.context.stackBegin = 0;
            initialThread.context.stackLimit = 0;
            initialThread.context.UpdateAfterGC(initialThread);
            Processor.SetCurrentThreadContext(ref initialThread.context);

#if DEBUG_THREAD_CONTEXT_ALIGNMENT
            Tracing.Log(Tracing.Debug, "Thread.alignment = {0}",
                        (((RuntimeType)typeof(Thread)).classVtable).baseAlignment);
            Tracing.Log(Tracing.Debug, "ThreadContext.alignment = {0}",
                        (((RuntimeType)typeof(ThreadContext)).classVtable).baseAlignment);
            Tracing.Log(Tracing.Debug, "MmxContext.alignment = {0}",
                        (((RuntimeType)typeof(MmxContext)).classVtable).baseAlignment);

            Tracing.Log(Tracing.Debug, "&initialThread         = {0:x8}",
                        Kernel.AddressOf(initialThread));
            fixed (void *v = &initialThread.context) {
                Tracing.Log(Tracing.Debug, "&initialThread.context = {0:x8}",
                            (UIntPtr)v);
            }
            fixed (void *v = &initialThread.context.mmx) {
                Tracing.Log(Tracing.Debug, "&initialThread.context.mmx = {0:x8}",
                            (UIntPtr)v);
            }
            fixed (void *v = &initialThread.context.mmx.st0) {
                Tracing.Log(Tracing.Debug, "&initialThread.context.mmx.st0 = {0:x8}",
                            (UIntPtr)v);
            }
#endif

            VTable.Assert((int)(((RuntimeType)typeof(Thread)).classVtable).baseAlignment == 16);
            VTable.Assert((int)(((RuntimeType)typeof(ThreadContext)).classVtable).baseAlignment == 16);

            Tracing.Log(Tracing.Debug, "InitialThread={0:x8}",
                        Kernel.AddressOf(initialThread));
            Monitoring.Log(Monitoring.Provider.Thread,
                           (ushort)ThreadEvent.ThreadPackageInit);
            initialThread.bumpAllocator.Dump();

            Tracing.Log(Tracing.Debug, "Class constructor Thread() exiting\n");
        }

        internal static unsafe void FinishInitializeThread()
        {
            // Set the fields of initialThread
            int stackVariable;
            initialThread.context.stackBegin =
                (new UIntPtr(&stackVariable) + 0xfff) & new UIntPtr(~0xfffU);
            initialThread.context.stackLimit = 0;

            initialThread.autoEvent = new AutoResetEvent(false);
            initialThread.joinEvent = new ManualResetEvent(false);
            initialThread.schedulerEntry = new ThreadEntry(initialThread);
            initialThread.timerEntry = new ThreadEntry(initialThread);
            initialThread.deferredEntry= new ThreadEntry(initialThread);
            initialThread.GetWaitEntries(1); // Cache allows wait without alloc
            Transitions.RuntimeInitialized();
            Transitions.ThreadStart();

            // Instantiate the static variable that needs to be initialized
            localDataStoreMgr = new LocalDataStoreMgr();

            processStopException = new ProcessStopException();
        }

        /// <summary> Prepares a new Thread to take on role as kernel thread
        /// for upcoming processor.  Called by Bootstrap processor. </summary>
        public static Thread PrepareKernelThread(Processor p)
        {
            Thread kernelThread = new Thread(null);
            GC.NewThreadNotification(kernelThread, false);
            return kernelThread;
        }

        public static void BindKernelThread(Thread  kernelThread,
                                            UIntPtr stackBegin,
                                            UIntPtr stackLimit)
        {
            kernelThread.context.processId  = initialThread.context.processId;
            kernelThread.context.stackBegin = stackBegin;
            kernelThread.context.stackLimit = 0/* stackLimit */;

            kernelThread.context.UpdateAfterGC(kernelThread);
            Processor.SetCurrentThreadContext(ref kernelThread.context);
            kernelThread.schedulerInfo.State = ThreadState.Running;
            Transitions.ThreadStart();
        }

        [NoHeapAllocation]
        public void DumpStackInfo()
        {
            Tracing.Log(Tracing.Debug, "<< thr={0:x8} beg={1:x8} lim={2:x8} ptr={3:x8} >>",
                        Kernel.AddressOf(this),
                        context.stackBegin,
                        context.stackLimit,
                        Isa.GetStackPointer());
        }

#if THREAD_TIME_ACCOUNTING
        // timestamp of last update for ExecutionTime
        internal ulong LastUpdateTime
        {
            [NoHeapAllocation]
            get { return context.lastExecutionTimeUpdate; }
            [NoHeapAllocation]
            set { context.lastExecutionTimeUpdate = value; }
        }

        // fixme: where to init. this one ???
        //        FinishInitializeThread() seems to be called before
        //        Processor.CyclesPerSecond is set up
        //static private ulong multiplyer = Processor.CyclesPerSecond /
        //                                  TimeSpan.TicksPerSecond
#else
        protected TimeSpan executionTime;
#endif
        public TimeSpan ExecutionTime
        {
#if THREAD_TIME_ACCOUNTING
            //[NoHeapAllocation]
            get
            {
                ulong m = Processor.CyclesPerSecond / TimeSpan.TicksPerSecond;

                bool saved = Processor.DisableInterrupts();
                try {
                    if (Processor.GetCurrentThread() == this) {
                        ulong now = Processor.CycleCount;
                        context.executionTime += now -
                            context.lastExecutionTimeUpdate;
                        LastUpdateTime = now;
                    }
                }
                finally {
                    Processor.RestoreInterrupts(saved);
                }

                // fixme: this division is bad (slow), hot to get rid of it?
                return new TimeSpan((long)(context.executionTime / m));
            }
#else
            [NoHeapAllocation]
            get { return executionTime; }
#endif
        }

#if THREAD_TIME_ACCOUNTING
        // This provides access to the raw cycle counter, so access to it
        // should be fast, compared to ExecutionTime.  This might be useful
        // for monitoring code which calls this often and can postprocess
        // these times otherwise
        public ulong RawExecutionTime
        {
            //[NoHeapAllocation]
            get
            {
                bool saved = Processor.DisableInterrupts();
                try {
                    if (Processor.GetCurrentThread() == this) {
                        ulong now = Processor.CycleCount;
                        context.executionTime += now -
                            context.lastExecutionTimeUpdate;
                        LastUpdateTime = now;
                    }
                }
                finally {
                    Processor.RestoreInterrupts(saved);
                }

                return context.executionTime;
            }
        }
#endif

        internal static
        void VisitBootstrapData(ReferenceVisitor visitor)
        {
            visitor.VisitReferenceFields(initialThread);
            visitor.VisitReferenceFields(threadTable);
        }

        internal static void UpdateAfterGC()
        {
            // Update all the thread pointers in the thread contexts
            for (int i = 0; i < threadTable.Length; i++) {
                Thread thread = threadTable[i];
                if (thread != null) {
                    thread.context.UpdateAfterGC(thread);
                }
            }
        }

        // Cache for ABI synchronization
        private WaitHandle[] syncHandles;
        internal WaitHandle[] GetSyncHandles(int num)
        {
            if (syncHandles == null || syncHandles.Length < num) {
                syncHandles = new WaitHandle[num + 8];
            }
            return syncHandles;
        }

        // Cache for handle synchronization
        private ThreadEntry[] entries;
        internal ThreadEntry[] GetWaitEntries(int num)
        {
            if (entries == null || entries.Length < num) {
                num += 8;   // So we don't have to do this too frequently.
                entries = new ThreadEntry[num];
                for (int i = 0; i < num; i++) {
                    entries[i] = new ThreadEntry(this);
                }
            }
            return entries;
        }

        // Caches for Select synchronization
        // We use stacks, because selectable abstractions might
        // internally implement HeadMatches using select receive
        // which is called from within an outer select.
        // NOTE however that internal selects should never block
        // (use timeout)
        private Stack selectBoolsStack;
        private Stack selectObjectsStack;
        private Stack selectSyncHandlesStack;

        public bool[] PopSelectBools(int size)
        {
            if (selectBoolsStack == null) {
                selectBoolsStack = new Stack();
            }
            if (selectBoolsStack.Count == 0) {
                return new bool [size];
            }
            bool[] selectBools = (bool[])selectBoolsStack.Pop();
            if (selectBools.Length < size) {
                return new bool [size];
            }
            return selectBools;
        }

        public void PushSelectBools(bool[] cache) {
            selectBoolsStack.Push(cache);
        }

        public ISelectable[] PopSelectObjects(int size)
        {
            if (selectObjectsStack == null) {
                selectObjectsStack = new Stack();
            }
            if (selectObjectsStack.Count == 0) {
                return new ISelectable [size];
            }
            ISelectable[] selectObjects = (ISelectable[])selectObjectsStack.Pop();
            if (selectObjects.Length < size) {
                return new ISelectable [size];
            }
            return selectObjects;
        }
        public void PushSelectObjects(ISelectable[] cache) {
            for (int i = 0; i < cache.Length; i++) {
                cache[i] = null;
            }
            selectObjectsStack.Push(cache);
        }

        public SyncHandle[] PopSelectSyncHandles(int size)
        {
            if (selectSyncHandlesStack == null) {
                selectSyncHandlesStack = new Stack();
            }
            if (selectSyncHandlesStack.Count == 0) {
                return new SyncHandle [size];
            }
            SyncHandle[] selectSyncHandles = (SyncHandle[])selectSyncHandlesStack.Pop();
            if (selectSyncHandles.Length < size) {
                return new SyncHandle [size];
            }
            return selectSyncHandles;
        }
        public void PushSelectSyncHandles(SyncHandle[] cache) {
            for (int i = 0; i < cache.Length; i++) {
                cache[i] = new SyncHandle();
            }
            selectSyncHandlesStack.Push(cache);
        }

        /// <summary>  </summary>
        public SchedulerTime BlockedUntil
        {
            [NoHeapAllocation]
            get { return blockedUntil; }
        }

        // Given a frame's range in memory (its esp/ebp), check whether
        // the frame contains the top transition record.  If so,
        // prepare to skip over a process's frames.
        [AccessedByRuntime("referenced from halasm.asm")]
        [NoStackLinkCheckTrans] // We don't want to throw an exception here;
            // Therefore, we cannot risk allocating stack segments,
            // and we should only call other NoStackLinkCheck functions (XXX).
        internal static unsafe UIntPtr CheckKernelProcessBoundary(UIntPtr esp, UIntPtr ebp, Exception exn)
        {
            ThreadContext *context = Processor.GetCurrentThreadContext();
            System.GCs.CallStack.TransitionRecord *topMarker = context->processMarkers;
            System.GCs.CallStack.TransitionRecord *secondMarker = context->stackMarkers;
            UIntPtr topMarkerPtr = (UIntPtr) topMarker;
            // If the top marker is in our frame, we've reached a boundary:
            if (esp < topMarkerPtr && topMarkerPtr <= ebp) {
                Thread.CurrentThread.lastUncaughtException = exn;
                //   Is this a ProcessStopException?  If not, it's a bug; log the bug.

                // NOTE: Removing the 'if'.  This
                //       will be removed soon, and the 'is' here
                //       results in an unbreakable cycle.
                //if (!(exn is ProcessStopException)) {
                    // Log the bug, but don't do anything that could
                    // throw another exception (e.g. memory allocation).
                    // XXX: what if stack allocation throws an exception here?
                    DebugStub.Print("Bug: kernel exception thrown to process (saved to Thread.LastUncaughtException)\n");
                    Tracing.Log(Tracing.Warning, "Bug: kernel exception thrown to process (saved to Thread.LastUncaughtException)\n");
                //}
                //   atomic
                //   {   // do these together so we never enter process mode
                //       remove top process->kernel marker from marker list
                //       remove top kernel->process marker from marker list
                //   }
                bool iflag = Processor.DisableInterrupts();

                try {
                    context->processMarkers = context->processMarkers->oldTransitionRecord;
                    context->stackMarkers = context->stackMarkers->oldTransitionRecord;
                    context->SetKernelMode();
                }
                finally {
                    Processor.RestoreInterrupts(iflag);
                }

                //Return the kernel->process marker, in preparation for these operations:
                //   edx := retAddr from *stackBottom from kernel->process marker
                //   restore esp,ebp from kernel->process marker
                //   while(top kernel->process marker not in stack segment)
                //       pop (and free) stack segment
                //   restore ebx,edi,esi from kernel->process marker
                return new UIntPtr(secondMarker);
            }
            else {
                return 0;
            }
        }

        // Discard any garbage stack segments that follow the segment
        // containing the marker.  After this runs, the topmost stack
        // segment will contain the marker.
        [AccessedByRuntime("referenced from halasm.asm")]
        [NoStackLinkCheckTrans]
        internal static unsafe void DiscardSkippedStackSegments(
            System.GCs.CallStack.TransitionRecord *marker,
            System.GCs.CallStack.TransitionRecord *oldMarker)
        {
            ThreadContext *context = Processor.GetCurrentThreadContext();
            UIntPtr markerPtr = new UIntPtr(marker);
            //   while(top kernel->process marker not in stack segment)
            //       pop (and free) stack segment

            //
            // HACKHACK: think about what this is doing. The topmost
            // stack segment is the one *currently in use*. On a paging
            // system, freeing it unmaps the underlying physical page.
            // Needless to say, our ability to use esp after that is
            // severely compromised.
            //
#if !PAGING
            while ((context->stackBegin != 0) && !(context->stackLimit <= markerPtr && markerPtr < context->stackBegin)) {
                Microsoft.Singularity.Memory.Stacks.ReturnStackSegment(ref *context);
            }
#endif

            // Unlink marker:
            context->stackMarkers = oldMarker;

            // Update stack limit.
            context->threadRecord.activeStackLimit = context->stackLimit;
        }

        // Most recently thrown exception object that the thread
        // did not catch at all (i.e. that propagated to the bottom
        // of the stack without encountering an appropriate catch clause).
        public Exception LastUncaughtException
        {
            [NoHeapAllocation]
            get {
                return lastUncaughtException;
            }
        }

#if PAGING
        // Switch to a different protection domain. This is an advanced stunt
        // for use by kernel threads only
        internal static void SwitchToDomain(ProtectionDomain newDomain)
        {
            Thread currentThread = CurrentThread;
            currentThread.CheckAddressSpaceConsistency();

            AddressSpace processorSpace = Processor.GetCurrentAddressSpace();
            AddressSpace newSpace = newDomain.AddressSpace;

            if (newSpace != processorSpace) {
                Processor.ChangeAddressSpace(newSpace);
                currentThread.tempDomain = newDomain;
            }

            currentThread.CheckAddressSpaceConsistency();
        }

        // Call this to snap back to our parent process' domain.
        internal static void RevertToParentDomain()
        {
            Thread currentThread = CurrentThread;
            currentThread.CheckAddressSpaceConsistency();
            Processor.ChangeAddressSpace(currentThread.process.Domain.AddressSpace);
            currentThread.tempDomain = null;
            currentThread.CheckAddressSpaceConsistency();
        }

        // This property provides the correct answer even when an
        // arbitrary protection domain is temporarily being used
        internal ProtectionDomain CurrentDomain {
            get {
                CheckAddressSpaceConsistency();
                return (tempDomain != null) ? tempDomain : process.Domain;
            }
        }

        [Inline]
        private void CheckAddressSpaceConsistency()
        {
            ProtectionDomain currentDomain = (tempDomain != null) ? tempDomain : process.Domain;
            DebugStub.Assert(Processor.GetCurrentAddressSpace() ==
                             currentDomain.AddressSpace);
        }
#endif

        ///
        /// <summary>
        /// Prepare thread for blocking - initialize UnblockedBy state
        /// </summary>
        ///
        [NoHeapAllocation]
        public int PrepareForBlocking()
        {
            SchedulerInfo       newInfo;
            SchedulerInfo       oldInfo;
            int                 prevUnblockedBy;

            do {
                // Copy scheduler state to memory
                newInfo = this.schedulerInfo;
                oldInfo = newInfo;

                // Initialize unblocked by - this is all we pretty much going to update
                newInfo.UnblockedBy = WaitHandle.UninitWait;

                // Remember who unblocked us before
                prevUnblockedBy = oldInfo.UnblockedBy;

            // Attempt to update atomicatlly the state.
            } while (oldInfo.Data != Interlocked.CompareExchange(ref this.schedulerInfo.Data,
                                                        newInfo.Data,
                                                        oldInfo.Data));
            return prevUnblockedBy;
        }

        ///
        /// <summary>
        /// Finish blocking - only changes blocking state if UnblockedBy is uninitialized
        /// </summary>
        ///
        /// <param name="unblockedBy">
        /// Id of waithandle that is attempting to unblock thread
        /// </param>
        ///
        [NoHeapAllocation]
        public int Unblock(int unblockedBy)
        {
            SchedulerInfo     newInfo;
            SchedulerInfo     oldInfo;
            int               result;

            do {
                // Copy scheduler state to memory
                newInfo = this.schedulerInfo;
                oldInfo = newInfo;

                // We can't unblock stopped and unstarted thread
                if ((oldInfo.State & (ThreadState.Stopped | ThreadState.Unstarted)) != 0) {
                    result = WaitHandle.UninitWait;
                    break;
                }

                // If nobody unblocked thread yet proceed otherwise we can return right away
                if (oldInfo.UnblockedBy == WaitHandle.UninitWait) {

                    // Remember unblocked information
                    newInfo.UnblockedBy = unblockedBy;

                    // Return unblcoked information
                    result = unblockedBy;
                }
                else {
                    // Remember who unblocked thread
                    result = oldInfo.UnblockedBy;

                    // Now we are ready to return;
                    break;
                }
            // Attempt to update atomicatlly the state.
            } while (oldInfo.Data != Interlocked.CompareExchange(ref this.schedulerInfo.Data,
                                                        newInfo.Data,
                                                        oldInfo.Data));
            return result;
        }

        ///
        /// <summary>
        /// Block thread - only changes blocking state if UnblockedBy is uninitialized
        /// </summary>
        ///
        [NoHeapAllocation]
        public int BlockThread()
        {
            SchedulerInfo     newInfo;
            SchedulerInfo     oldInfo;
            int               result;

            do {
                // Copy scheduler state to memory
                newInfo = this.schedulerInfo;
                oldInfo = newInfo;

                // If nobody unblocked thread yet proceed otherwise we can return right a way
                if (oldInfo.UnblockedBy == WaitHandle.UninitWait) {

                    // Mark thread as blocked
                    newInfo.State = ThreadState.Blocked;
                    result = WaitHandle.UninitWait;
                }
                else {
                    // Remember who unblocked thread
                    result = oldInfo.UnblockedBy;

                    // Now we are ready to return;
                    break;
                }
            // Attempt to update atomicatlly the state.
            } while (oldInfo.Data != Interlocked.CompareExchange(ref this.schedulerInfo.Data,
                                                        newInfo.Data,
                                                        oldInfo.Data));
            return result;
        }


        ///
        /// <summary>
        /// Increment thread's freeze counter
        /// </summary>
        ///
        [NoHeapAllocation]
        public void IncrementFreezeCounter()
        {
            SchedulerInfo     newInfo;
            SchedulerInfo     oldInfo;
            int               result;

            do {
                // Copy scheduler state to memory
                newInfo = this.schedulerInfo;
                oldInfo = newInfo;

                // Freeze counter can't be negative
                VTable.Assert(newInfo.FreezeCount >= 0);

                // Increment freeze counter
                newInfo.FreezeCount++;

            } while (oldInfo.Data != Interlocked.CompareExchange(ref this.schedulerInfo.Data,
                                                        newInfo.Data,
                                                        oldInfo.Data));
        }

        ///
        /// <summary>
        /// Decrement thread's freeze counter, if thread was really suspended meaing
        /// its state was marked suspended by scheduler, return this information so that
        /// </summary>
        ///
        /// <param name="shouldPutOnRunnableQueue">
        /// Indicates if caller has to put thread on a runnable queue
        /// </param>
        ///
        [NoHeapAllocation]
        public int DecrementFreezeCounter(ref bool shouldPutOnRunnableQueue)
        {
            SchedulerInfo     newInfo;
            SchedulerInfo     oldInfo;
            int               result;

            do {
                // By default caller shouldn't be putting this thread on runnable queue
                shouldPutOnRunnableQueue = false;

                // Copy scheduler state to memory
                newInfo = this.schedulerInfo;
                oldInfo = newInfo;

                // Decrement freeze counter
                newInfo.FreezeCount--;

                // If thread is really suspended mark it as runnable - caller will put it on runnable
                // queue where it will change its state to ether runnable, blocked or suspended
                if (newInfo.FreezeCount == 0 &&
                        oldInfo.State == ThreadState.Suspended) {

                    // If we succeede with state change, caller will need to put thread on a
                    // runnable queue
                    shouldPutOnRunnableQueue = true;
                }

                // Freeze counter can't be negative
                VTable.Assert(newInfo.FreezeCount >= 0);

            } while (oldInfo.Data != Interlocked.CompareExchange(ref this.schedulerInfo.Data,
                                                        newInfo.Data,
                                                        oldInfo.Data));

            // Assert post conditions: If caller has to put thread on runnable queue then counter
            // had to be 1
            VTable.Assert(!shouldPutOnRunnableQueue || oldInfo.FreezeCount == 1);

            return oldInfo.FreezeCount -1;
        }

        ///
        /// <summary>
        ///    Verifies if caller has to call scheduler unblock - this will only required if thread is
        /// in blocked state, was unblocked by caller and blocking version is off by one
        /// </summary>
        ///
        /// <param name="unblocker">Id of handle unblocker that is attempting to unblock thread</param>
        ///
        [NoHeapAllocation]
        public bool ShouldCallSchedulerUnBlock(int unblocker)
        {
            return (this.schedulerInfo.State == ThreadState.Blocked &&
                  this.schedulerInfo.UnblockedBy == unblocker);
        }


        ///
        /// <summary>
        /// Given complete thread's scheduler information derive scheduler state
        /// </summary>
        ///
        /// <param name="threadSchedulerInfo">Given scheduler atomic info to use for derivation</param>
        ///
        /// <remark> Scheduler info is complex state that consist of three states: Sceduler state
        /// unblocked by information and freeze count. We need to examine all three peices
        /// of information as well current thread state to derive real scheduelr state
        ///</remark>
        ///
        [NoHeapAllocation]
        public static ThreadState DeriveCurrentSchedulerState(SchedulerInfo threadSchedulerInfo)
        {
            // Retrieve state
            ThreadState actualState = threadSchedulerInfo.State;

            // If thread is runnable and it is frozen use suspend state otherwise use actual state
            if (actualState == ThreadState.Runnable &&
                threadSchedulerInfo.FreezeCount > 0) {

                actualState = ThreadState.Suspended;
            }

            // If thread was unblocked but is marked as blocked it is no longer blocked - it is runnable
            if (threadSchedulerInfo.UnblockedBy != WaitHandle.UninitWait &&
                actualState == ThreadState.Blocked) {

                actualState = ThreadState.Runnable;
            }

            return actualState;
        }

        ///
        /// <summary>
        /// Derive new scheduler state
        /// </summary>
        ///
        /// <param name="threadSchedulerInfo">Given scheduler atomic info to use for derivation</param>
        /// <param name="schedulingAction">scheduling action thread is performing: for now maps to states</param>
        ///
        /// <remark> Scheduler info is complex state that consist of three states: Scheduler state
        /// unblocked by information and freeze count. We need to examine all three peices
        /// of information as well current thread state to derive real scheduler state
        ///</remark>
        ///
        [NoHeapAllocation]
        public static ThreadState DeriveNewSchedulerState(
            SchedulerInfo       threadSchedulerInfo,
            ThreadState         schedulingAction)
        {
            ThreadState     oldState;
            ThreadState     newState;

            // First derive old schduler state
            oldState = DeriveCurrentSchedulerState(threadSchedulerInfo);

            // Base on the current state and scheduling action calculate new state
            switch (oldState) {
                case ThreadState.Stopped: {
                    // When thread is stopped any of scheduling action on it is forbidden
                    VTable.Assert(false);
                    break;
                }
                case ThreadState.Unstarted: {
                    // Only two actions are allowed in this situation eiterh make thread runnable or
                    // stop
                    VTable.Assert(schedulingAction == ThreadState.Runnable ||
                                  schedulingAction == ThreadState.Stopped);

                    threadSchedulerInfo.State =schedulingAction;
                    break;
                }
                case ThreadState.Runnable: {
                    // When thread is runnable it is normal for scheduler to attempt it to mark
                    // runnable again - it could happen due to complex runnable state (unitwait + blocked)
                    // Two other actions can be apllied suspended and running
                    // any other action should be assumed incorrect
                    VTable.Assert(schedulingAction == ThreadState.Suspended ||
                                  schedulingAction == ThreadState.Running ||
                                  schedulingAction == ThreadState.Runnable);

                    threadSchedulerInfo.State = schedulingAction;

                    break;
                }
                case ThreadState.Running: {
                    // From this state we can go to blocked, runnable, stopped no other transition is
                    // possible
                    VTable.Assert(schedulingAction == ThreadState.Blocked ||
                                  schedulingAction == ThreadState.Runnable ||
                                  schedulingAction == ThreadState.Stopped);

                    threadSchedulerInfo.State = schedulingAction;
                    break;
                }
                case ThreadState.Blocked: {
                    // From this state we can go to runnable only no other transition is
                    // possible
                    VTable.Assert(schedulingAction == ThreadState.Runnable);

                    threadSchedulerInfo.State = schedulingAction;
                    break;
                }
                case ThreadState.Suspended: {
                    // From this state we can go to runnable however someone might attempt to
                    // make us rinnning - we need to ignore it!
                    VTable.Assert(schedulingAction == ThreadState.Runnable ||
                                schedulingAction == ThreadState.Running);

                    // Though we can recieve runnng signal we can't go to running by passing
                    // runnable
                    if (schedulingAction == ThreadState.Runnable) {
                        threadSchedulerInfo.State = schedulingAction;
                    }
                    else {
                        // Otherwise we have to stay suspendedcd .
                        threadSchedulerInfo.State = ThreadState.Suspended;
                    }
                    break;
                }
                default: {
                    // We shouldn't get here ever:
                    VTable.Assert(false);
                    break;
                }
            }

            // Now lets derive our new state
            return DeriveCurrentSchedulerState(threadSchedulerInfo);
        }

        ///
        /// <summary>
        /// Set new scheduler state on thread
        /// </summary>
        ///
        /// <param name="schedulerAction">Scheduler action</param>
        ///
        [NoHeapAllocation]
        internal ThreadState ChangeSchedulerState(ThreadState schedulerAction)
        {
            Thread.SchedulerInfo    oldSchedulerInfo;
            Thread.SchedulerInfo    newSchedulerInfo;

            do {
                  // Retrieve thread's complex scheduling state
                  oldSchedulerInfo = this.ThreadSchedulerInfo;
                  newSchedulerInfo = this.ThreadSchedulerInfo;

                  // Map thread's state to Scheduler state and derive thread's new state
                  newSchedulerInfo.State = DeriveNewSchedulerState(oldSchedulerInfo, schedulerAction);

                    // We calculated new state try change thread's new state.
            } while (!TryChangeSchedulerState(newSchedulerInfo.State, oldSchedulerInfo));

            return newSchedulerInfo.State;
        }

        ///
        /// <summary>
        /// Try to change scheduler state to a new state. New state usually is derived from
        /// calling DeriveSchedulerState method. For more info see comments to that method
        /// </summary>
        ///
        /// <param name="newState">New scheduling state</param>
        /// <param name="previousInfo">Scheduling information base on which we derived new state</param>
        ///
        [NoHeapAllocation]
        private bool TryChangeSchedulerState(
            ThreadState           newState,
            SchedulerInfo         previousInfo)
        {
            bool              didStateChange = true;
            SchedulerInfo     newInfo = previousInfo;

            // Update scheduler state in a new atomic info
            newInfo.State = newState;

            //Try to update the state and check if we were succesful
            didStateChange = previousInfo.Data == Interlocked.CompareExchange(ref this.schedulerInfo.Data,
                                                        newInfo.Data,
                                                        previousInfo.Data);
            return didStateChange;
        }

        ///
        /// <summary>
        /// Wait for reschedule - wait until thread is allowed to be running. This method
        /// should be exclusively used by processor dispatcher
        /// </summary>
        ///
        [NoHeapAllocation]
        internal void WaitUntilReadyForContextSwitch()
        {
            while (this.insideOfContextSwitchDepth > 0) {
                // Loop until thread is inside of context switch
                // use SpinWait intrinsic to optimize for hyperthreaded processors.
                Thread.SpinWait(1);
            }
            return;
        }

        ///
        /// <summary>
        /// Turn on  thread's state inside of context switch
        /// </summary>
        ///
        [NoHeapAllocation]
        internal void TurnOnInsideOfContextSwitch()
        {
            // Assert preconditions: Contex Switch Depth can't be negative
            VTable.Assert(this.insideOfContextSwitchDepth ==0);

            this.insideOfContextSwitchDepth++;
        }

        ///
        /// <summary>
        /// Turn off thread's state inside of context switch
        /// </summary>
        ///
        [NoHeapAllocation]
        internal void TurnOffInsideOfContextSwitch()
        {
            // Assert preconditions: Contex Switch Depth can't be 0
            VTable.Assert(this.insideOfContextSwitchDepth == 1);

            this.insideOfContextSwitchDepth--;
        }

        ///
        /// <summary>
        /// Find out if we inside of context switch
        /// </summary>
        ///
        [NoHeapAllocation]
        internal bool IsInsideOfContextSwitch()
        {
            return this.insideOfContextSwitchDepth > 0;
        }


        ///
        /// <summary>
        /// Scheduler specific information. Includes scheduler state, wait version and
        /// unblocked by information
        /// </summary>
        ///
        [StructAlign(8)]
        public struct SchedulerInfo
        {
            // NOTE:
            //  1. Ideally we can use Interlocked operations on a 64-bit struct, then we
            //      don't need to use bit masks and shifts. But Bartok doesn't support
            //      it at the moment.
            //  2. Another way is to use StructLayout to emulate union, but we have both
            //      performance issues in Bartok generated StructCopy and a Bartok bug
            //      that sometimes optimizes away useful code.
            //  3. There are different opinions about whether it's better to define
            //      constants for the masks and shifts, we'll re-evaluate.

            ///
            /// <summary>
            /// This separated into 5 different fields. We use a single 64-bit integer so that
            /// we can use Interlocked operations on this struct. The layout is:
            ///
            /// State            : byte  : byte 0               : mask 00000000000000FF
            /// DelayAbortCount  : byte  : bit 0-6 of byte 1    : mask 0000000000007F00
            /// IsAborted        : bool  : bit 7 of byte 1      : mask 0000000000008000
            /// FreezeCount      : UInt16: byte 2-3             : mask 00000000FFFF0000
            /// UnblockedBy      : Int32 : byte 4-7             : mask FFFFFFFF00000000
            /// </summary>
            ///
            public UInt64 Data;

            ///
            /// <summary>
            /// State of a thread with respect to scheduler: Runable, Running and etc...
            /// </summary>
            ///
            public ThreadState State
            {
                [Inline]
                [NoHeapAllocation]
                get
                {
                    // State is byte 0 of the data
                    return (ThreadState)(byte)Data;
                }
                [Inline]
                [NoHeapAllocation]
                set
                {
                    // State is byte 0 of the data
                    Data &= 0xFFFFFFFFFFFFFF00UL;
                    Data |= (byte)value;
                }
            }

            ///
            /// <summary>
            /// Reference counter of delay abort.
            /// Thread is not allowed to die with non zero DelayAbortCount.
            /// </summary>
            ///
            public byte DelayAbortCount
            {
                [Inline]
                [NoHeapAllocation]
                get
                {
                    // AbortState is bit 0-6 of byte 1 of the data
                    return (byte)(((UInt32)Data >> 8) & 0x7F);
                }
            }


            ///
            /// <summary>
            /// Increment the delay abort count.
            /// Thread is not allowed to die with non zero DelayAbortCount.
            /// </summary>
            ///
            [Inline]
            [NoHeapAllocation]
            public void IncrementDelayAbortCount()
            {
                // AbortState is bit 0-6 of byte 1 of the data
                // It must not overflow above 7 bits (0x7F)
                VTable.Assert(((UInt32)Data & 0x7F00) != 0x7F00);
                Data += 0x100;
            }

            ///
            /// <summary>
            /// Decrement the delay abort count.
            /// Thread is not allowed to die with non zero DelayAbortCount.
            /// </summary>
            ///
            [Inline]
            [NoHeapAllocation]
            public void DecrementDelayAbortCount()
            {
                // AbortState is bit 0-6 of byte 1 of the data
                // It must not underflow below 0
                VTable.Assert(((UInt32)Data & 0x7F00) != 0);
                Data -= 0x100;
            }

            ///
            /// <summary>
            /// Get or set whether the thread is aborted
            /// </summary>
            ///
            public bool IsAborted
            {
                [Inline]
                [NoHeapAllocation]
                get
                {
                    // IsAborted is bit 7 of byte 1 of the data
                    return ((UInt32)Data & 0x8000) != 0;
                }
                [Inline]
                [NoHeapAllocation]
                set
                {
                    // IsAborted is bit 7 of byte 1 of the data
                    if (value) {
                        Data |= 0x0000000000008000;
                    }
                    else {
                        Data &= 0xFFFFFFFFFFFF7FFFUL;
                    }
                }
            }

            ///
            /// <summary>
            /// A reference counter of how many times the thread is suspended. Threads
            /// with non zero FreezeCount are not allowed to run.
            /// </summary>
            ///
            public UInt16 FreezeCount
            {
                [Inline]
                [NoHeapAllocation]
                get
                {
                    // AbortState is byte 2 and 3 of the data
                    return (UInt16)(Data >> 16);
                }
                [Inline]
                [NoHeapAllocation]
                set
                {
                    // AbortState is byte 2 and 3 of the data
                    Data &= 0xFFFFFFFF0000FFFFUL;
                    Data |= (((UInt32)value) << 16);
                }
            }

            ///
            /// <summary>
            /// Filed represents an id of WaitHandle that performed unblock operation
            /// </summary>
            ///
            public int UnblockedBy
            {
                [Inline]
                [NoHeapAllocation]
                get
                {
                    // UnblockedBy is byte 4 to 7 of the data
                    return (int)(UInt32)(Data >> 32);
                }
                [Inline]
                [NoHeapAllocation]
                set
                {
                    // UnblockedBy is byte 4 to 7 of the data
                    Data &= 0x00000000FFFFFFFFUL;
                    Data |= (((UInt64)(UInt32)value) << 32);
                }
            }
        };

        ///
        /// <summary>
        /// Thread type
        /// </summary>
        ///
        public enum ThreadType
        {
            Unknown,
            Idle,
            Scavenger
        };

#if PAGING
        /// <summary> For use when we temporarily switch to a different domain </summary>
        private ProtectionDomain        tempDomain;
#endif

        /// <summary>
        /// This manager is responsible for storing the global data that is  shared amongst all
        /// the thread local stores.
        /// </summary>
        static private LocalDataStoreMgr            localDataStoreMgr;

        /// <summary> A maximum number of threads , must be power of 2 >=64</summary>
        internal const int              maxThreads = 1024;

        internal const int              NoAffinity = -1;

        /// <summary> A global counter to generate next thread index </summary>
        private static int              threadIndexGenerator;

        /// <summary> Thread is inside of context switch </summary>
        [AccessedByRuntime("referenced from halidt.asm")]
        internal int                    insideOfContextSwitchDepth = 0;

        /// <summary> MultiUseWord (object header) head</summary>
        internal UIntPtr                externalMultiUseObjAllocListHead;

        /// <summary>MultiUseWord (object header) tail </summary>
        internal UIntPtr                externalMultiUseObjAllocListTail;

        /// <summary> Thread index inside of a prcess </summary>
        internal int                    processThreadIndex;

        /// <summary> Global thread index </summary>
        internal int                    threadIndex;

        /// <summary> A method to start a thread</summary>
        private ThreadStart             threadStart;

        /// <summary> A state of a thread from scheduler point of view </summary>
        private SchedulerInfo           schedulerInfo;

        /// <summary> Previous scheduler info as seen by record event, used for debugging purposes</summary>
        private SchedulerInfo           prevSchedulerInfo;

        /// <summary> Thread state from dispatcher point of view </summary>
        private ProcessorDispatcher     dispatcher;

        /// <summary> Indicates if a thread is executing in a nonPreemptible region </summary>
        private int                     nonPreemptibleRegionCount;

        /// <summary> Thread's event used by monitor </summary>
        private AutoResetEvent          autoEvent;

        /// <summary> Indicates if thread's gc event has been signaled </summary>
        private int                     gcEventSignaled;

        /// <summary>Thread's join event</summary>
        private ManualResetEvent        joinEvent;

        /// <summary> This is needed for Bartok </summary>
        internal Thread                 blockingCctorThread;

        /// <summary>Preallocated services request object</summary>
        internal ThreadLocalServiceRequest          localServiceRequest;

        /// <summary>A timer indicating till when thread is blocked</summary>
        [AccessedByRuntime("referenced from c++")]
        internal SchedulerTime          blockedUntil;

        /// <summary>An entry used by scheduler queues to manipulate wit thread</summary>
        [AccessedByRuntime("referenced from c++")]
        internal ThreadEntry            schedulerEntry;

        /// <summary>An entry used by timer quieue to manipulate with thread</summary>
        internal ThreadEntry            timerEntry;

        /// <summary>An entry used by wait handle to put thread on deferred queue during wakeup</summary>
        internal ThreadEntry            deferredEntry;

        /// <summary>Thread context</summary>
        [AccessedByRuntime("referenced from c++")]
        internal ThreadContext          context;

        /// <summary>Thread's process</summary>
        [AccessedByRuntime("referenced from c++")]
        internal Process                process;

        /// <summary>Thread's handle</summary>
        internal ThreadHandle           threadHandle;

        /// <summary>Thread local value - single place for local storage</summary>
        internal UIntPtr                threadLocalValue;

        /// <summary>
        /// Most recently thrown exception object that the thread
        /// did not catch at all (i.e. that propagated to the bottom
        /// of the stack without encountering an appropriate catch clause).
        /// </summary>
        internal Exception              lastUncaughtException;

        /// <summary>
        /// Monitor link list of threads. Remove these and Monitor as soon as
        /// stack is out of kernel.
        /// </summary>
        internal Thread                 nextThread;

        /// <summary>  </summary>
        private Object                  exceptionStateInfo;

        /// <summary>Global thread table</summary>
        internal static Thread[]        threadTable;

        /// <summary>A lock protecting access to global trhead table</summary>
        private static SpinLock         threadTableLock;

        /// <summary>Thread local storage</summary>
        private static LocalDataStore   localDataStore;

        /// <summary>First thread in Singularity</summary>
        internal static Thread          initialThread;

        /// <summary>Spinlock protecting thread state</summary>
        private SpinLock                threadLock;

        /// <summary>An exception object to stop process </summary>
        private static ProcessStopException
                                        processStopException;

        /// <summary> The processor ID this thread is running on or ran on last time </summary>
        internal int                    Affinity = NoAffinity;

#if false
        /// <summary> scheduler specific data </summary>
        internal ThreadScheduleData     ScheduleData;
#endif

        /// <summary> Thread type </summary>
        internal ThreadType             type = ThreadType.Unknown;

        /// <summary> SpinLock ranking masks </summary>
        internal int                    spinLockRankMask;

        /// <summary>A number of spinlocks held by a thread</summary>
        internal int                    numberOfSpinlocksHeld = 0;
    }
}

