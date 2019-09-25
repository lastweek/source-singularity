// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

// #define DEBUG_SWITCH

namespace System.Threading
{
    using System;
    using System.Collections;
    using System.Diagnostics;
    using System.GCs;
    using System.Globalization;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

    using Microsoft.Bartok.Runtime;

    using Microsoft.Singularity;
    using Microsoft.Singularity.Channels;
    using Microsoft.Singularity.V1.Services;
    using Microsoft.Singularity.V1.Threads;

    //| <include path='docs/doc[@for="Thread"]/*' />
    public sealed partial class Thread
    {
        // Singularity specific fields
        // Need CPU context
        // Need stack

        internal AutoResetEvent processGcEvent;

        private AutoResetEvent autoEvent;
        private ManualResetEvent joinEvent;

        internal Thread blockingCctorThread;

        // Singularity specific fields
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal unsafe ThreadContext * context;
        internal ThreadHandle threadHandle;

        // Most recently thrown exception object that the thread
        // did not catch at all (i.e. that propagated to the bottom
        // of the stack or to a kernel/process boundary without
        // encountering an appropriate catch clause).
        private Exception lastUncaughtException;

        private bool ignoredByJoinAll; // for "service" threads

        private Object m_ExceptionStateInfo;            // Exception info latched to the thread on a thread abort

        // Bartok specific fields
        internal Thread nextThread; // Link for linked lists of threads

        // This array is of length 1 and contains a queue item for this
        // thread.  It allows WaitOne and the scheduler to add this thread
        // to their queues without allocating memory.
        internal ThreadQueueItem[] singleQueueItem;

        // MultiUseWord (object header) fields.
        internal UIntPtr externalMultiUseObjAllocListHead;
        internal UIntPtr externalMultiUseObjAllocListTail;

        // Bartok specific fields
        internal int threadIndex;
        private ThreadStart     threadStart;
        private ThreadState     threadState;
        internal int waitingCriticalSectionDepth;
        internal Object waitingObject; // Not used, but useful for debugging

        private static bool closing;
        private static long totalArrayAllocations;
        private static long totalArrayBytesAllocated;
        private static long totalBytes;
        private static long totalStructBytesAllocated;

        internal static Thread[] threadTable;
        private static SpinLock threadTableLock;

        private static LocalDataStore localDataStore;
        private object m_userScheduler;

        internal static Thread initialThread;

        //=========================================================================
        // This manager is responsible for storing the global data that is
        // shared amongst all the thread local stores.
        //=========================================================================  
        static private LocalDataStoreMgr m_LocalDataStoreMgr;

        internal const int maxThreads = 1024; // Must be power of 2 >= 64
        private static int threadIndexGenerator;

        //=========================================================================
        // Creates a new Thread object which will begin execution at
        // start.ThreadStart on a new thread when the Start method is called.
        //
        // Exceptions: ArgumentNullException if start == null.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.Thread"]/*' />
        public unsafe Thread(ThreadStart start)
        {
            Tracing.Log(Tracing.Audit, "Application Thread()");

            if (start == null) {
                throw new ArgumentNullException("start");
            }

            threadIndex = -1;
            threadState = ThreadState.Unstarted;
            threadStart = start;

            // Create the event for the thread to wait upon
            autoEvent = new AutoResetEvent(false);
            joinEvent = new ManualResetEvent(false);
            processGcEvent = new AutoResetEvent(false);
            singleQueueItem = new ThreadQueueItem [1] { new ThreadQueueItem(this) };

            // Find a usable entry in the thread table
            // Disable local preemption while holding the lock. This might also be a 
            // the property of the lock
            
            bool disabled = Processor.DisableLocalPreemption();
            Thread.threadTableLock.Acquire(CurrentThread);
            try {
                for (int i = 0; i < threadTable.Length; i++) {
                    int index = (threadIndexGenerator + i) % threadTable.Length;
                    if (threadTable[index] == null) {
                        threadTable[index] = this;
                        this.threadIndex = index;
                        threadIndexGenerator = index + 1;
                        // NB: We call this once, afterwards the GC visitor calls it.
                        break;
                    }
                }
            }
            finally {
                Thread.threadTableLock.Release(CurrentThread);
                Processor.RestoreLocalPreemption(disabled);
            }

            VTable.Assert(threadIndex >= 0, "Out of thread slots!");

            //MemoryBarrier();

            // Must check closing after being insert into table to avoid race condition.
            if (closing) {
                threadState = ThreadState.Stopped;
                joinEvent.Set();
                Tracing.Log(Tracing.Warning, "Aborting: Runtime closing.");
                return;
            }

            ThreadHandle handleOnStack;
            UIntPtr threadContext;
            if (!ThreadHandle.Create(threadIndex,
                                     new ContainerHandle(),
                                     out handleOnStack,
                                     out threadContext)) {
                Tracing.Log(Tracing.Warning, "Aborting: ThreadHandle.Create failed.");
                threadState = ThreadState.Stopped;
                joinEvent.Set();
                return;
            }
            this.threadHandle = handleOnStack;
            this.context = (ThreadContext *) threadContext;
            this.context->threadIndex = unchecked((ushort) threadIndex);
            this.context->UpdateAfterGC(this);
        }



        /// <summary>
        /// Finalizer is responsible for freeing handle that keeps corresponding
        /// kernel object live.
        /// </summary>
        ~Thread() {
            if (this.threadHandle.id != 0) {
                ThreadHandle.Dispose(this.threadHandle);
                this.threadHandle = new ThreadHandle();
            }
        }

        //=========================================================================
        // Spawns off a new thread which will begin executing at the ThreadStart
        // method on the IThreadable interface passed in the constructor. Once the
        // thread is dead, it cannot be restarted with another call to Start.
        //
        // Exceptions: ThreadStateException if the thread has already been started.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.Start"]/*' />
        public void Start()
        {
            lock ((Object) this) {
                if (closing) {
                    throw new ThreadStateException("Cannot start thread when closing");
                }

                ThreadState oldState = threadState;
                if (oldState != ThreadState.Unstarted) {
                    throw new ThreadStateException("Cannot start thread in state "+oldState);
                }

                threadState = ThreadState.Running;

                // Tell the GC that we have created the thread
                GC.NewThreadNotification(this, false);

                ThreadHandle.Start(threadHandle);
                GC.KeepAlive(this);
            }
        }

        // HalInitContext sets ThreadStub as the first process code to be
        // executed in a new thread context.
        [AccessedByRuntime("referenced from hal.cpp")]
        private static unsafe void ThreadStub(int threadIndex)
        {
            Transitions.ThreadStart();
            GC.ThreadStartNotification(threadIndex);
            Thread currentThread = threadTable[threadIndex];
            if (AddThread(threadIndex)) {
                // Log Thread Start.
                Tracing.Log(Tracing.Audit, "ThreadStub(atid={0}) Entered",
                            (UIntPtr)unchecked((uint)threadIndex));

                ThreadStart startFun = currentThread.threadStart;

                try {
                    startFun();
                }
                catch (Exception uncaughtException) {
                    // Save Uncaught Exception in Thread instance.
                    currentThread.lastUncaughtException = uncaughtException;

                    // Dump (possibly nested) Exceptions to the Debugger.
                    //  Note: The first line identifies the outer exception,
                    //  later lines identify the inner exceptions nesting level.
                    string formatString;
                    uint nestingLevel = 0;
                    Exception currentException = uncaughtException;
                    formatString = "Thread{0,3}   Outer" +
                                   " Exception: Type '{2}', Message '{3}'.";
                    while (currentException != null) {
                        DebugStub.WriteLine(
                            formatString,
                            __arglist(threadIndex,
                                      nestingLevel,
                                      currentException.GetType().ToString(),
                                      currentException.Message));
                        currentException = currentException.InnerException;
                        formatString = "Thread{0,3} Inner{1,2}" +
                                       " Exception: Type '{2}', Message '{3}'.";
                        if (++nestingLevel > 16) break;
                    }

                    // Assert (always asserts as exception is never null here).
                    string message = uncaughtException.Message;
                    if (message == null) message = String.Empty;

                    VTable.Assert(uncaughtException == null,
                                  "Thread " + threadIndex +
                                  " failed with Exception Type '" +
                                  uncaughtException.GetType().ToString() +
                                  "', Message '" + message + "'.");
                }

                // Log Thread Exit.
                Tracing.Log(Tracing.Audit, "ThreadStub(atid={0}) Exiting",
                            (UIntPtr)unchecked((uint)threadIndex));
            }

            currentThread.joinEvent.Set();
            RemoveThread(threadIndex);
            GC.DeadThreadNotification(currentThread);

            bool disabled = Processor.DisableLocalPreemption();
            // REVIEW: this is a dangerous locking strategy as the transition code
            // may decide it needs to wake up another thread.
            Thread.threadTableLock.Acquire(currentThread);
            try {
                Transitions.ThreadEnd(threadIndex);
                // You may not do any calls out of proc after this point!
                threadTable[threadIndex] = null;
                Transitions.DeadThreadNotification(threadIndex);
            }
            finally {
                Thread.threadTableLock.Release(currentThread);
                Processor.RestoreLocalPreemption(disabled);
            }
        }

        //====================================================================
        // Support for service threads.  Service threads should not count
        // towards keeping a process alive.  When all non-service threads
        // have terminated, the service threads are asked to stop themselves
        // so the process can terminate gracefully.
        //===================================================================  

        // The number of non-service threads running in the process
        private static int threadCount;
        private static Object notificationTableObject;
        private static Object[] notificationTable;

        public delegate void StopServiceNotice();

        public void MakeServiceThread(StopServiceNotice notification)
        {
            Tracing.Log(Tracing.Audit, "MakeServiceThread {0}",
                        (UIntPtr) threadIndex);
            if (this != Thread.CurrentThread) {
                throw new Exception("Only the thread itself may call MakeServiceThread");
            }
            if (notificationTable == null) {
                int tableSize = threadTable.Length;
                Interlocked.CompareExchange(ref notificationTableObject,
                                            new Object[tableSize],
                                            null);
                notificationTable = (Object[]) notificationTableObject;
            }
            Tracing.Log(Tracing.Audit, "  previous notification: {0:x8}",
                        Magic.addressOf(notificationTable[threadIndex]));
            // BUGBUG: Should have been Interlocked.Exchange, but that
            // doesn't work due to a Bartok codegen bug.
            Object oldNotification = notificationTable[threadIndex];
            while (Interlocked.CompareExchange(ref notificationTable[threadIndex], notification, oldNotification) != oldNotification) {
                oldNotification = notificationTable[threadIndex];
            }
            if (oldNotification == null) {
                // We made the thread a service thread for the first time.
                if (Interlocked.Decrement(ref threadCount) == 0) {
                    NotifyServiceThreads();
                }
            }
            VTable.Assert(threadCount >= 0);
        }

        public void ClearServiceThread(Thread thread)
        {
            Tracing.Log(Tracing.Audit, "ClearServiceThread");
            if (this != Thread.CurrentThread) {
                throw new Exception("Only the thread itself may call ClearServiceThread");
            }
            if (notificationTable == null) {
                return;
            }
            if (Interlocked.Exchange(ref notificationTable[threadIndex],
                                     null) != null) {
                // We cleared the notification
                Interlocked.Increment(ref threadCount);
            }
            VTable.Assert(threadCount >= 0);
        }

        private static bool AddThread(int index)
        {
            Tracing.Log(Tracing.Audit, "AddThread {0} ({1})",
                        (UIntPtr) index, (UIntPtr) threadCount);
            VTable.Assert(threadCount >= 0);
            if (Interlocked.Increment(ref threadCount) == 1 &&
                notificationTable != null) {
                // The thread was started after we started sending out
                // notifications, so indicate that the thread should not
                // really be started
                return false;
            }
            else {
                return true;
            }
        }

        internal static void RemoveThread(int index)
        {
            Tracing.Log(Tracing.Audit, "RemoveThread {0} ({1})",
                        (UIntPtr) index, (UIntPtr) threadCount);
            if (Interlocked.Decrement(ref threadCount) == 0) {
                NotifyServiceThreads();
            }
            VTable.Assert(threadCount >= 0);
        }

        private static void NotifyServiceThreads()
        {
            Tracing.Log(Tracing.Audit, "NotifyServiceThreads");
            if (notificationTable == null) {
                return;
            }
            for (int i = 0; i < notificationTable.Length; i++) {
                if (notificationTable[i] != null) {
                    Tracing.Log(Tracing.Audit, "  Notifying thread {0}",
                                (UIntPtr) i);
                    ((StopServiceNotice)notificationTable[i])();
                }
            }
        }


        //=========================================================================
        // Returns true if the thread has been started and is not dead.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.IsAlive"]/*' />
        public bool IsAlive {
            [NoHeapAllocation]
            get { return (threadState != ThreadState.Unstarted &&
                          threadState != ThreadState.Stopped); }
        }


        //=========================================================================
        // Waits for the thread to die.
        //
        // Exceptions: ThreadStateException if the thread has not been started yet.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.Join"]/*' />
        public void Join()
        {
            Join(SchedulerTime.MaxValue);
        }

        //=========================================================================
        // Waits for the thread to die or for timeout milliseconds to elapse.
        // Returns true if the thread died, or false if the wait timed out.
        //
        // Exceptions: ArgumentException if timeout < 0.
        //             ThreadStateException if the thread has not been started yet.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.Join2"]/*' />
        public bool Join(TimeSpan timeout)
        {
            if (threadState == ThreadState.Unstarted) {
                throw new ThreadStateException();
            }
            return joinEvent.WaitOne(timeout);
        }

        public bool Join(SchedulerTime timeout)
        {
            if (threadState == ThreadState.Unstarted) {
                throw new ThreadStateException();
            }
            return joinEvent.WaitOne(timeout);
        }

        internal static bool JoinAll()
        {
            // To avoid races, join all does the following:
            // 1) Wait for all known peer threads to terminate.
            // 2) Set the closing flag to disallow creating of new threads.
            // 3) Wait for any threads that have started in the mean time.

            for (uint iteration = 0; iteration < 2; iteration++) {
                for (int i = 0; i < threadTable.Length; i++) {
                    Thread thread = null;

                    bool disabled = Processor.DisableLocalPreemption();
                    Thread.threadTableLock.Acquire(CurrentThread);
                    try {
                        thread = threadTable[i];
                    }
                    finally {
                        Thread.threadTableLock.Release(CurrentThread);
                        Processor.RestoreLocalPreemption(disabled);
                    }

                    if (thread != null &&
                        thread != CurrentThread &&
                        thread.threadState != ThreadState.Unstarted &&
                        !thread.ignoredByJoinAll) {
                        thread.Join();
                    }
                }
                closing = true;
            }
            return true;
        }

        //=========================================================================
        // Suspends the current thread for timeout milliseconds. If timeout == 0,
        // forces the thread to give up the remainder of its timeslice.
        //
        // Exceptions: ArgumentException if timeout < 0.
        //=========================================================================  

        public static void Sleep(int milliseconds)
        {
            Sleep(TimeSpan.FromMilliseconds(milliseconds));
        }

        //| <include path='docs/doc[@for="Thread.Sleep"]/*' />
        public static void Sleep(TimeSpan timeout)
        {
            ThreadHandle.Sleep(timeout);
        }

        // wait for a length of time proportional to 'iterations'.  Each iteration is should
        // only take a few machine instructions.  Calling this API is preferable to coding
        // an explicit busy loop because the hardware can be informed that it is busy waiting.   

        //| <include path='docs/doc[@for="Thread.SpinWait"]/*' />
        [NoHeapAllocation]
        public static void SpinWait(int iterations)
        {
            for (int i = iterations; i > 0; i--) {
                // Ensure that the optimizer doesn't remove this
                NativeNoOp();
            }
        }

        ///
        /// <summary>
        ///     Notify thread that it acquired spinlock of specific rank
        /// </summary>
        ///
        /// <param name="type">Type of spinlock</param>
        ///
        [NoHeapAllocation]
        internal void NotifySpinLockAboutToAcquire(int type)
        {
            // Add rank verification and etc .. 
        }

        ///
        /// <summary>
        ///     Notify thread that released a spinlock of specific rank
        /// </summary>
        ///
        /// <param name="type">Type of spinlock</param>
        ///
        [NoHeapAllocation]
        internal void NotifySpinLockReleased(int type)
        {
            // Add rank verification and etc .. 
        }

        ///
        /// <summary>
        ///     Given a thread id, return actual thread
        /// </summary>
        ///
        /// <param name="threadId">Thread id</param>
        ///
        [NoHeapAllocation]
        internal static Thread GetThreadFromThreadId(int threadId)
        {
            // Assert preconditions: threadId has to be in range and thread can't be null
            VTable.Assert(threadId < threadTable.Length);
            VTable.Assert(threadTable[threadId] != null);

            return threadTable[threadId];
        }


        [Intrinsic]
        [NoHeapAllocation]
        public static extern void NativeNoOp();

        internal static int GetCurrentProcessIndex() {
            return ProcessService.GetCurrentProcessId();
        }

        internal bool WaitForMonitor(SchedulerTime timeOut)
        {
            return autoEvent.WaitOne(timeOut);
        }

        internal bool WaitForEvent(SchedulerTime timeOut)
        {
            DebugStub.Break();
            return autoEvent.WaitOne(timeOut);
        }

        internal bool WaitForEvent(TimeSpan timeout)
        {
            DebugStub.Break();
            return autoEvent.WaitOne(timeout);
        }

        internal static unsafe bool WaitForGCEvent(int currentThreadIndex)
        {
            AutoResetEvent are =
                threadTable[currentThreadIndex].processGcEvent;
            // BUGBUG: The restoration of the gcState should be taken
            // care of by the compiler.
            return are.WaitOneNoGC();
        }

        internal void SignalMonitor()
        {
            autoEvent.Set();
        }

        internal void SignalEvent()
        {
            DebugStub.Break();
            autoEvent.Set();
        }

        [Inline]
        internal static void SignalGCEvent(int currentThreadIndex,
                                           int threadIndex)
        {
            SignalGCEvent(threadIndex);
        }

        internal static unsafe void SignalGCEvent(int threadIndex)
        {
            Thread thread = threadTable[threadIndex];
            if (thread == null) {
                return;
            }
            thread.processGcEvent.SetNoGC();
        }

        //| <include path='docs/doc[@for="Thread.CurrentThread"]/*' />
        public static Thread CurrentThread
        {
            [NoHeapAllocation]
            [NoStackLinkCheckTrans]
            get {
                return Processor.GetCurrentThread();
            }
        }

        internal ThreadHandle Handle
        {
            [NoHeapAllocation]
            get { return threadHandle; }
        }

        [NoStackLinkCheckTrans]
        [RequiredByBartok]
        [NoHeapAllocation]
        private static Thread GetCurrentThreadNative()
        {
            return Processor.GetCurrentThread();
        }

        [NoStackLinkCheckTrans]
        [RequiredByBartok]
        [NoHeapAllocation]
        internal static int GetCurrentThreadIndex()
        {
            return Processor.GetCurrentThread().threadIndex;
        }

        //=========================================================================
        // Return the thread state as a consistent set of bits.  This is more
        // general then IsAlive or IsBackground.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.ThreadState"]/*' />
        public ThreadState ThreadState
        {
            [NoHeapAllocation]
            get { return threadState; }
        }

        [NoHeapAllocation]
        public int GetThreadId()
        {
            return threadIndex;
        }

        public object UserScheduler
        {
            get {
                return m_userScheduler;
            }
            set {
                if (null != m_userScheduler) {
                    // TODO make this a security exception
                    throw new Exception("User scheduler may not be changed");
                }
                m_userScheduler = value;
            }
        }

        public int Affinity
        {
            get { return ThreadHandle.GetAffinity(threadHandle); }
            set { ThreadHandle.SetAffinity(threadHandle, value); }
        }


        //=========================================================================
        // Allocates an un-named data slot. The slot is allocated on ALL the
        // threads.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.AllocateDataSlot"]/*' />
        public static LocalDataStoreSlot AllocateDataSlot()
        {
            return m_LocalDataStoreMgr.AllocateDataSlot();
        }

        //=========================================================================
        // Allocates a named data slot. The slot is allocated on ALL the
        // threads.  Named data slots are "public" and can be manipulated by
        // anyone.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.AllocateNamedDataSlot"]/*' />
        public static LocalDataStoreSlot AllocateNamedDataSlot(String name)
        {
            return m_LocalDataStoreMgr.AllocateNamedDataSlot(name);
        }

        //=========================================================================
        // Looks up a named data slot. If the name has not been used, a new slot is
        // allocated.  Named data slots are "public" and can be manipulated by
        // anyone.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.GetNamedDataSlot"]/*' />
        public static LocalDataStoreSlot GetNamedDataSlot(String name)
        {
            return m_LocalDataStoreMgr.GetNamedDataSlot(name);
        }

        //=========================================================================
        // Frees a named data slot. The slot is allocated on ALL the
        // threads.  Named data slots are "public" and can be manipulated by
        // anyone.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.FreeNamedDataSlot"]/*' />
        public static void FreeNamedDataSlot(String name)
        {
            m_LocalDataStoreMgr.FreeNamedDataSlot(name);
        }

        //=========================================================================
        // Retrieves the value from the specified slot on the current thread.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.GetData"]/*' />
        public static Object GetData(LocalDataStoreSlot slot)
        {
            m_LocalDataStoreMgr.ValidateSlot(slot);

            if (localDataStore != null) {
                return localDataStore.GetData(slot);
            }
            return null;
        }

        //=========================================================================
        // Sets the data in the specified slot on the currently running thread.
        //=========================================================================  
        //| <include path='docs/doc[@for="Thread.SetData"]/*' />
        public static void SetData(LocalDataStoreSlot slot, Object data)
        {
            // Create new DLS if one hasn't been created for this thread.
            if (localDataStore == null) {
                localDataStore = m_LocalDataStoreMgr.CreateLocalDataStore();
            }
            localDataStore.SetData(slot, data);
        }

        //=============================================================  

        internal Object ExceptionState
        {
            [NoHeapAllocation]
            get { return m_ExceptionStateInfo;}
            [NoHeapAllocation]
            set { m_ExceptionStateInfo = value;}
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
        //=========================================================================
        // Volatile Read & Write and MemoryBarrier methods.
        // Provides the ability to read and write values ensuring that the values
        // are read/written each time they are accessed.
        //=========================================================================  

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

        [MethodImplAttribute(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(32)]
        [NoHeapAllocation]
        private static unsafe extern Thread HalGetThread();

        [NoHeapAllocation]
        public static void Yield()
        {
            ThreadHandle.Yield();
        }

        [NoHeapAllocation]
        public bool IsStopped()
        {
            return (threadState == ThreadState.Stopped);
        }

        [PreInitRefCounts]
        static unsafe Thread()
        {
            threadIndexGenerator = 1;

            // Enable Thread.CurrentThread as soon as we can!
            initialThread = Magic.toThread(BootstrapMemory.Allocate(typeof(Thread)));
            initialThread.threadState = ThreadState.Running;
            initialThread.threadIndex = 0;

            // Allocate tables for thread management
            threadTable = (Thread[])
                BootstrapMemory.Allocate(typeof(Thread[]), maxThreads);

            // Initialize the thread and event tables
            threadTable[initialThread.threadIndex] = initialThread;
            initialThread.context = Processor.GetCurrentThreadContext();
            initialThread.context->threadIndex =
                unchecked((ushort) initialThread.threadIndex);
            initialThread.context->UpdateAfterGC(initialThread);

            Tracing.Log(Tracing.Debug, "InitialThread={0:x8}",
                        Magic.addressOf(initialThread));
        }

        internal static unsafe void FinishInitializeThread()
        {
            int threadIndex = initialThread.threadIndex;
            // Get the GC ready for initialThread
            Transitions.RuntimeInitialized();
            Transitions.ThreadStart();
            initialThread.processGcEvent = new AutoResetEvent(false);
            initialThread.autoEvent = new AutoResetEvent(false);
            initialThread.joinEvent = new ManualResetEvent(false);
            initialThread.singleQueueItem =
                new ThreadQueueItem [1] { new ThreadQueueItem(initialThread) };
            // Use CurrentThread to find our initial handle:
            VTable.Assert(initialThread == CurrentThread);
            initialThread.threadHandle = ThreadHandle.CurrentThread();
            // Instantiate the static variable that needs to be initialized
            m_LocalDataStoreMgr = new LocalDataStoreMgr();
            AddThread(threadIndex);
        }

        public TimeSpan ExecutionTime
        {
            get {
                TimeSpan t = ThreadHandle.GetExecutionTime(threadHandle);
                GC.KeepAlive(this);
                return t;
            }
        }

        internal static
        void VisitBootstrapData(GCs.ReferenceVisitor visitor)
        {
            visitor.VisitReferenceFields(Thread.initialThread);
            visitor.VisitReferenceFields(Thread.threadTable);
        }

        internal static unsafe void UpdateAfterGC()
        {
            // Update all the thread pointers in the thread contexts
            for (int i = 0; i < threadTable.Length; i++) {
                Thread thread = threadTable[i];
                if (thread != null) {
                    thread.context->UpdateAfterGC(thread);
                }
            }
        }

        // Cache for ABI synchronization
        private SyncHandle[] syncHandles;
        internal SyncHandle[] GetSyncHandles(int length)
        {
            if (syncHandles == null ||
                syncHandles.Length < length) {

                syncHandles = new SyncHandle[length + 8];
            }
            return syncHandles;
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
            for (int i=0; i<cache.Length; i++) {
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
            for (int i=0; i<cache.Length; i++) {
                cache[i] = new SyncHandle();
            }
            selectSyncHandlesStack.Push(cache);
        }



        // Given a frame's range in memory (its esp/ebp), check whether
        // the frame contains the top transition record.  If so,
        // prepare for making a transition from process mode back
        // to kernel mode.
        [AccessedByRuntime("referenced from halasm.asm")]
        [NoStackLinkCheckTrans] // We don't want to throw an exception here;
            // Therefore, we cannot risk allocating stack segments,
            // and we should only call other NoStackLinkCheck functions (XXX).
        internal static unsafe UIntPtr CheckKernelProcessBoundary(UIntPtr esp, UIntPtr ebp, Exception exn)
        {
            ThreadContext *context = Processor.GetCurrentThreadContext();
            CallStack.TransitionRecord *topMarker = context->kernelMarkers;
            CallStack.TransitionRecord *secondMarker = context->stackMarkers;
            UIntPtr topMarkerPtr = (UIntPtr) topMarker;
            // If the top marker is in our frame, we've reached a boundary:
            if (esp < topMarkerPtr && topMarkerPtr <= ebp) {
                context->uncaughtFlag = true;
                Thread.CurrentThread.lastUncaughtException = exn;
                Processor.GetCurrentThreadContext()->SetKernelMode();
                return 1;
            }
            else {
                return 0;
            }
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

        // Tell JoinAll not to block waiting for this thread to exit.
        // Some special threads (e.g. the finalizer thread) need to run
        // only as long as there are other threads running, and should
        // not be considered by JoinAll.
        [NoHeapAllocation]
        internal void SetIgnoredByJoinAll()
        {
            ignoredByJoinAll = true;
        }

#if DEBUG || true
        string debugName;
        public string DebugName
        {
            [NoHeapAllocation]
            get { return debugName; }

            [NoHeapAllocation]
            set { debugName = value; }
        }
#endif
    }

    // This class is designed to support queues whose enqueue,
    // dequeue, and remove operations do not allocate memory.
    // This feature is useful when writing code that needs to
    // do such operations with interrupts off.
    [CLSCompliant(false)]
    public class ThreadQueue
    {
        private ThreadQueueItem head = null;
        private ThreadQueueItem tail = null;

        [NoHeapAllocation]
        public void Enqueue(ThreadQueueItem item)
        {
            VTable.Assert(item.Next == null);
            VTable.Assert(item.Prev == null);
            VTable.Assert(item.Queue == null);

            item.Queue = this;
            item.Prev = tail;

            if (tail != null) {
                VTable.Assert(tail.Next == null);
                tail.Next = item;
            }
            else {
                VTable.Assert(head == null);
                head = item;
            }

            tail = item;
        }

        [NoHeapAllocation]
        public ThreadQueueItem Dequeue()
        {
            ThreadQueueItem item = head;

            if (item != null) {
                Remove(item);
            }

            return item;
        }

        [NoHeapAllocation]
        public void Remove(ThreadQueueItem item)
        {
            VTable.Assert(item.Queue == this);

            if (item.Next != null) {
                item.Next.Prev = item.Prev;
            }
            else {
                VTable.Assert(item == tail);
                tail = item.Prev;
            }

            if (item.Prev != null) {
                item.Prev.Next = item.Next;
            }
            else {
                VTable.Assert(item == head);
                head = item.Next;
            }

            item.Next = null;
            item.Prev = null;
            item.Queue = null;
        }

        [NoHeapAllocation]
        public bool IsEmpty()
        {
            return (head == null);
        }
    }

    [CLSCompliant(false)]
    public class ThreadQueueItem
    {
        public readonly Thread Thread = null;

        public ThreadQueueItem Next = null;
        public ThreadQueueItem Prev = null;

        public ThreadQueue Queue = null;

        public ThreadQueueItem(Thread thread)
        {
            Thread = thread;
        }

        [NoHeapAllocation]
        public void Remove()
        {
            if (Queue != null) {
                Queue.Remove(this);
            }

            VTable.Assert(Next == null);
            VTable.Assert(Prev == null);
            VTable.Assert(Queue == null);
        }
    }
}
