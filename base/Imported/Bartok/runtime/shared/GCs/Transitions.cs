//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs
{
    using System.Runtime.CompilerServices;
    using System.Threading;

#if SINGULARITY
    using Microsoft.Singularity;
#endif
#if SINGULARITY_KERNEL
    using Microsoft.Singularity.Scheduling;
#endif

    [AccessedByRuntime("Referenced in halforgc.asm")]
    internal class Transitions
    {

        // Synchronization among threads for GC:
        //
        // We keep an integer for each thread.
        // The possible values are:

#if SINGULARITY_KERNEL
        // Thread is dormant or in unmanaged code and a GC would be ok
        [AccessedByRuntime("Referenced in halforgc.asm")]
        private const int DormantState      =   0x1;
        // Thread is running in managed code and not ready for GC
        [AccessedByRuntime("Referenced in halforgc.asm")]
        private const int MutatorState      =   0x2;
        // GC work is desired
        private const int GCRequest         =   0x4;
        // Thread is under GC control
        private const int GCControl         =   0x8;
        // Thread is dormant in the application space
        [AccessedByRuntime("Referenced in halforgc.asm")]
        private const int OtherDormantState =  0x10;
        // Thread is running in the application space
        [AccessedByRuntime("Referenced in halforgc.asm")]
        private const int OtherMutatorState =  0x20;
        // GC work is desired in the application space
        private const int OtherGCRequest    =  0x40;
        // Application thread is under GC control
        private const int OtherGCControl    =  0x80;
#else
        // Thread is dormant or in unmanaged code and a GC would be ok
        [AccessedByRuntime("Referenced in halforgc.asm")]
        private const int DormantState      =  0x10;
        // Thread is running in managed code and not ready for GC
        [AccessedByRuntime("Referenced in halforgc.asm")]
        private const int MutatorState      =  0x20;
        // GC work is desired.  Must be a power of 2.
        private const int GCRequest         =  0x40;
        // Thread is under GC control.  Must be a power of 2.
        private const int GCControl         =  0x80;
        // Thread is dormant in the kernel space
        [AccessedByRuntime("Referenced in halforgc.asm")]
        private const int OtherDormantState =   0x1;
        // Thread is running in the kernel space
        [AccessedByRuntime("Referenced in halforgc.asm")]
        private const int OtherMutatorState =   0x2;
#endif // SINGULARITY_KERNEL

        internal static bool        fInitializedRuntime;

        internal static void RuntimeInitialized() {
            fInitializedRuntime = true;
        }

#if SINGULARITY_KERNEL
        [Inline]
        internal static unsafe
        void InitializeStatusWord(ref ThreadContext threadContext)
        {
            int oldValue, newValue;
            do {
                oldValue = threadContext.gcStates;
                newValue = ((oldValue|DormantState|OtherDormantState)&
                            ~(MutatorState|GCRequest|GCControl|
                              OtherMutatorState|OtherGCRequest|OtherGCControl));
            } while (!CompareAndSwap(ref threadContext.gcStates,
                                     newValue, oldValue));
        }
#endif

        // Code outside of the GC will move threads between
        // MutatorState and DormantState.  This should be done with
        // the TakeMutatorControl and TakeDormantControl methods.  The
        // garbage collectors can request that they be notified when
        // threads go dormant.  They do this by calling the
        // MakeGCRequests method.  The TakeMutatorControl and
        // TakeDormantControl methods are then supposed to do the
        // right thing.

        [Inline]
        private static bool CompareAndSwap(ref int word,
                                           int newValue,
                                           int oldValue)
        {
            return (Interlocked.CompareExchange(ref word, newValue, oldValue)
                    == oldValue);
        }

        #region Transition Methods (Methods corresponding to macro transitions)

        // To be called when a thread is created
        internal static void NewThreadNotification(int newThreadIndex,
                                                   bool initial)
        {
#if SINGULARITY_PROCESS
            if (initial) {
                VTable.Assert(InMutatorState(newThreadIndex));
                return;
            }
#endif
            VTable.Assert(InDormantState(newThreadIndex));
        }

        // To be called when a thread is terminated/terminating
        internal static void DeadThreadNotification(int deadThreadIndex)
        {
            VTable.Assert(Thread.threadTable[deadThreadIndex] == null);
            VTable.Assert(InDormantState(deadThreadIndex));
            if (Transitions.HasGCRequest(deadThreadIndex)) {
                GC.ThreadDormantGCNotification(deadThreadIndex);
            }
        }

#if SINGULARITY
#if SINGULARITY_KERNEL
        // To be called at the beginning of a thread
        internal static unsafe void ThreadStart() {
            ThreadContext *currentThreadContext =
                Processor.GetCurrentThreadContext();
            TakeInitialMutatorControl(currentThreadContext);
        }
#else
        // To be called at the beginning of a thread
        internal static unsafe void ThreadStart() {
            ThreadContext *currentThreadContext =
                Processor.GetCurrentThreadContext();
            // The thread has been started in the kernel.  We need
            // to ensure that the transition to application space
            // is completed properly.
            EnsureMutatorControlNoGC(currentThreadContext);
        }
#endif

#else // SINGULARITY

        // To be called at the beginning of a thread
        internal static void ThreadStart(int currentThreadIndex) {
            VTable.Assert(InDormantState(currentThreadIndex));
            TakeInitialMutatorControl(currentThreadIndex);
        }

#endif // SINGULARITY

        // To be called at the end of a thread
        internal static void ThreadEnd(int currentThreadIndex) {
            VTable.Assert(InMutatorState(currentThreadIndex));
            TakeDormantControl(currentThreadIndex);
        }

#if SINGULARITY

        [AccessedByRuntime("called from halforgc.asm")]
        [NoStackLinkCheckTrans] // This is called from __pushStackMark, which cannot tolerate an 
                                // ABI call to allocate a new stack
        internal static unsafe
        void LeaveManagedSpace(ThreadContext *currentThreadContext)
        {
            TransferMutatorControl(currentThreadContext);
        }

        // To be used for returning from calls to outside managed space
        [AccessedByRuntime("called from halforgc.asm")]
        [NoStackLinkCheckTrans] // This is called from __popStackMark, which cannot tolerate an 
                                // ABI call to allocate a new stack
        [Inline]
        internal static unsafe
        void ReturnToManagedSpace(ThreadContext *currentThreadContext)
        {
            EnsureMutatorControl(currentThreadContext);
        }

#if SINGULARITY_KERNEL

        [AccessedByRuntime("called from halforgc.asm")]
        internal static unsafe
        void SuspendThread(ThreadContext *currentThreadContext)
        {
            TakeDormantControl(currentThreadContext);
        }

        [AccessedByRuntime("called from halforgc.asm")]
        internal static unsafe
        void ReviveThread(ThreadContext *currentThreadContext)
        {
            TakeMutatorControl(currentThreadContext);
        }

#endif // SINGULARITY_KERNEL

#else // SINGULARITY

        // To be used for calls to outside managed space
        [AccessedByRuntime("called from halforgc.asm")]
        [Inline]
        [ManualRefCounts]
        internal static void LeaveManagedSpace(Thread currentThread) {
            TakeDormantControl(currentThread.threadIndex);
        }

        // To be used for returning from calls to outside managed space
        [AccessedByRuntime("called from halforgc.asm")]
        [Inline]
        internal static Thread ReturnToManagedSpace(int currentThreadIndex) {
            TakeMutatorControl(currentThreadIndex);
            return Thread.threadTable[currentThreadIndex];
        }

#endif // SINGULARITY

        // For the LoadFunction stub for PInvoke methods
        [RequiredByBartok]
        internal static void EnterLoadFunctionStub() {
            TakeMutatorControl(Thread.GetCurrentThreadIndex());
        }

        // For the LoadFunction stub for PInvoke methods
        [RequiredByBartok]
        internal static void LeaveLoadFunctionStub() {
            TakeDormantControl(Thread.GetCurrentThreadIndex());
        }

        #endregion

        internal static void MakeGCRequests(int excludedThreadIndex) {
            int limit = Thread.threadTable.Length;
            for (int i = 0; i < limit; i++) {
                if (Thread.threadTable[i] != null &&
                    i != excludedThreadIndex) {
                    MakeGCRequest(i);
                }
            }
        }

        #region Helper Functions (Independent of where statusWord is)

        [Inline]
        [NoHeapAllocation]
        private static bool fInDormantState(int statusWord) {
            return ((statusWord & DormantState) != 0);
        }

        [Inline]
        [NoHeapAllocation]
        private static bool fInMutatorState(int statusWord) {
            return ((statusWord & MutatorState) != 0);
        }

        [Inline]
        [NoHeapAllocation]
        private static bool fHasGCRequest(int statusWord) {
            return ((statusWord & GCRequest) != 0);
        }

        [Inline]
        [NoHeapAllocation]
        private static bool fUnderGCControl(int statusWord) {
            return ((statusWord & GCControl) != 0);
        }

        [Inline]
        private static void TakeDormantControl(ref int statusWord,
                                               int threadIndex)
        {
            VTable.Assert(fInMutatorState(statusWord));
            VTable.Deny(fInDormantState(statusWord));
            int oldValue, newValue;
            do {
                oldValue = statusWord;
                newValue = (oldValue|DormantState) & ~MutatorState;
            } while (!CompareAndSwap(ref statusWord, newValue, oldValue));
            if (fHasGCRequest(newValue)) {
                GC.ThreadDormantGCNotification(threadIndex);
            }
        }

        [Inline]
        private static void TakeDormantControlNoGC(ref int statusWord) {
            VTable.Assert(fInMutatorState(statusWord));
            VTable.Deny(fInDormantState(statusWord));
            int oldValue, newValue;
            do {
                oldValue = statusWord;
                newValue = (oldValue|DormantState) & ~MutatorState;
            } while (!CompareAndSwap(ref statusWord, newValue, oldValue));
        }

        [Inline]
        private static void TransferMutatorControl(ref int statusWord,
                                                   int threadIndex)
        {
            if (!CompareAndSwap(ref statusWord,
                                DormantState|OtherMutatorState,
                                MutatorState|OtherDormantState)) {
                TakeDormantControl(ref statusWord, threadIndex);
            }
        }

        [Inline]
        private static void EnsureMutatorControl(ref int statusWord,
                                                 int currentThreadIndex)
        {
            if (!fInMutatorState(statusWord)) {
                TakeMutatorControl(ref statusWord, currentThreadIndex);
            }
            VTable.Deny(fInDormantState(statusWord));
            VTable.Deny(fUnderGCControl(statusWord));
        }

        [Inline]
        private static void EnsureMutatorControlNoGC(ref int statusWord,
                                                     int currentThreadIndex)
        {
            if (!fInMutatorState(statusWord)) {
                TakeMutatorControlNoGC(ref statusWord, currentThreadIndex);
            }
            VTable.Deny(fInDormantState(statusWord));
            VTable.Deny(fUnderGCControl(statusWord));
        }

#if SINGULARITY
        [AccessedByRuntime("referenced from halasm.asm")]
        [NoStackLinkCheckTrans]
        internal static unsafe void RestoreMutatorControlIfNeeded()
        {
            ThreadContext *currentThreadContext =
                Processor.GetCurrentThreadContext();
            if (!Transitions.InMutatorState(currentThreadContext)) {
                // NOTE: There is a window where OtherMutatorControl may be
                // set simultaneously with OtherGCRequest.  When clearing
                // OtherMutatorControl and setting OtherDormantControl, the
                // normal thing to do is to check for a GC request, but in
                // this case it doesn't matter as this code is only run
                // when an kernel exception is supposed to pass over an
                // application stack segment.
                int oldValue, newValue;
                bool consumedSignal = false;
                int threadIndex = currentThreadContext->threadIndex;
                do {
                    oldValue = currentThreadContext->gcStates;
                    if (fUnderGCControl(oldValue)) {
                        Thread.WaitForGCEvent(threadIndex);
                        consumedSignal = true;
                    }
                    newValue = ((oldValue|MutatorState|OtherDormantState) &
                                ~(DormantState|OtherMutatorState));
                } while (!CompareAndSwap(ref currentThreadContext->gcStates,
                                         newValue, oldValue));
                if (consumedSignal) {
                    Thread.SignalGCEvent(threadIndex);
                }
            }
        }
#endif

        [Inline]
        private static void TakeMutatorControl(ref int statusWord,
                                               int currentThreadIndex)
        {
            if (!SwitchToMutatorState(ref statusWord)) {
                TakeMutatorControlSlow(ref statusWord, currentThreadIndex);
            }
            VTable.Assert(fInMutatorState(statusWord));
            VTable.Deny(fInDormantState(statusWord));
            VTable.Deny(fUnderGCControl(statusWord));
        }

        [Inline]
        private static void TakeMutatorControlNoGC(ref int statusWord,
                                                   int currentThreadIndex)
        {
            if (!SwitchToMutatorState(ref statusWord)) {
                TakeMutatorControlSlowNoGC(ref statusWord, currentThreadIndex);
            }
            VTable.Assert(fInMutatorState(statusWord));
            VTable.Deny(fInDormantState(statusWord));
            VTable.Deny(fUnderGCControl(statusWord));
        }

        private static void TakeInitialMutatorControl(ref int statusWord,
                                                      int currentThreadIndex)
        {
            if (!SwitchToMutatorState(ref statusWord)) {
                TakeInitialMutatorControlSlow(ref statusWord,
                                              currentThreadIndex);
            }
            VTable.Assert(fInMutatorState(statusWord));
            VTable.Deny(fInDormantState(statusWord));
            VTable.Deny(fUnderGCControl(statusWord));
        }

        [NoInline]
        // [StackLinkCheck] Removed due to call from ReturnToManagedSpace
        private static void TakeMutatorControlSlow(ref int statusWord,
                                                   int currentThreadIndex)
        {
            TakeMutatorControlSlow(ref statusWord, currentThreadIndex,
                                   true, true);
        }

        [NoInline]
        // [StackLinkCheck] Removed due to call from LeaveManagedSpace
        private static void TakeMutatorControlSlowNoGC(ref int statusWord,
                                                       int currentThreadIndex)
        {
            TakeMutatorControlSlow(ref statusWord, currentThreadIndex,
                                   false, true);
        }

        private static
        void TakeInitialMutatorControlSlow(ref int statusWord,
                                           int currentThreadIndex)
        {
            TakeMutatorControlSlow(ref statusWord, currentThreadIndex,
                                   false, false);
        }

        private static void TakeMutatorControlSlow(ref int statusWord,
                                                   int currentThreadIndex,
                                                   bool allowGC,
                                                   bool preserveSignals)
        {
            bool consumedSignal = false;
            while (true) {
                if (SwitchToMutatorState(ref statusWord)) {
                    break;
                }
                if (SwitchToMutatorStateWithGCRequest(ref statusWord)) {
                    if (allowGC) {
                        Thread currentThread =
                            Thread.threadTable[currentThreadIndex];
                        if (currentThread != null) {
                            GC.InvokeCollection(currentThread);
                        }
                    }
                    break;
                }
                if (fUnderGCControl(statusWord)) {
                    Thread.WaitForGCEvent(currentThreadIndex);
                    consumedSignal = true;
                }
            }
            if (consumedSignal && preserveSignals) {
                Thread.SignalGCEvent(currentThreadIndex);
            }
        }

        [Inline]
        private static bool SwitchToMutatorState(ref int statusWord) {
            VTable.Deny(fInMutatorState(statusWord),
                        "Thread is already under mutator control");
            VTable.Assert(fInDormantState(statusWord));
            int oldValue = statusWord & ~(GCRequest|GCControl);
            int newValue = (oldValue|MutatorState) & ~DormantState;
            return CompareAndSwap(ref statusWord, newValue, oldValue);
        }

        [Inline]
        private static
        bool SwitchToMutatorStateWithGCRequest(ref int statusWord)
        {
            int oldValue = ((statusWord|DormantState|GCRequest) & ~GCControl);
            int newValue = (oldValue|MutatorState) & ~DormantState;
            return CompareAndSwap(ref statusWord, newValue, oldValue);
        }

        [Inline]
        private static bool TakeGCControl(ref int statusWord) {
            int oldValue, newValue;
            do {
                oldValue = statusWord;
                if (!fInDormantState(oldValue) ||
                    !fHasGCRequest(oldValue) ||
                    fUnderGCControl(oldValue)) {
                    return false;
                }
                newValue = oldValue|GCControl;
            } while (!CompareAndSwap(ref statusWord, newValue, oldValue));
            return true;
        }

        [Inline]
        private static void ReleaseGCControl(ref int statusWord,
                                             int threadIndex)
        {
            // There is only one possible transition out of this state.
            int oldValue, newValue;
            do {
                oldValue = statusWord;
                VTable.Assert(fInDormantState(oldValue));
                VTable.Assert(fHasGCRequest(oldValue));
                VTable.Assert(fUnderGCControl(oldValue));
                newValue = (oldValue& ~(GCRequest|GCControl));
            } while (!CompareAndSwap(ref statusWord, newValue, oldValue));
            Thread.SignalGCEvent(threadIndex);
        }

        private static void MakeGCRequest(ref int statusWord,
                                          int threadIndex)
        {
#if SINGULARITY_KERNEL
            if (Scheduler.IsIdleThread(threadIndex)) {
                return;
            }
#endif
            int oldStatus, newStatus;
            do {
                oldStatus = statusWord;
                newStatus = oldStatus|GCRequest;
            } while (!CompareAndSwap(ref statusWord, newStatus, oldStatus));
        }

        private static void ClearGCRequest(ref int statusWord,
                                           int threadIndex)
        {
            VTable.Assert(fHasGCRequest(statusWord));
            VTable.Assert(fInMutatorState(statusWord));
            int oldStatus, newStatus;
            do {
                oldStatus = statusWord;
                newStatus = (oldStatus & ~GCRequest);
            } while (!CompareAndSwap(ref statusWord, newStatus, oldStatus));
        }

        #endregion

#if SINGULARITY

        [Inline]
        private static unsafe
        ThreadContext *GetCurrentThreadContext(int currentThreadIndex) {
            VTable.Assert(GetThreadContext(currentThreadIndex) ==
                          Processor.GetCurrentThreadContext());
            return Processor.GetCurrentThreadContext();
        }

        [Inline]
        private static unsafe
        ThreadContext *GetThreadContext(int threadIndex) {
            Thread thread = Thread.threadTable[threadIndex];
            if (thread == null) {
                return null;
            } else {
#if SINGULARITY_KERNEL
                fixed (ThreadContext *result = &thread.context) {
                    return result;
                }
#else
                return thread.context;
#endif
            }
        }

#endif

        #region Dependent (Methods depending on location of the status word)

#if SINGULARITY

        [NoBarriers]
        [PreInitRefCounts]
        internal static void Initialize()
        {
        }

        // To be used for callbacks into managed space
        [RequiredByBartok]
        [Inline]
        internal static unsafe void EntryIntoManagedSpace() {
            ThreadContext *currentThreadContext =
                Processor.GetCurrentThreadContext();
            EnsureMutatorControl(currentThreadContext);
        }

        // To be used for returning from a callback into managed space
        [RequiredByBartok]
        [Inline]
        internal static unsafe void ReturnFromManagedSpace() {
            ThreadContext *currentThreadContext =
                Processor.GetCurrentThreadContext();
#if SINGULARITY_KERNEL
            // In Singularity kernel this function is the exit point of a kernel ABI.
            // If the thread is requested to be aborted, we stop it right here
            currentThreadContext->thread.ProcessAbortIfRequested(AbortRequestSource.ABIExit);
#endif
            TransferMutatorControl(currentThreadContext);
        }

        // To be used for returning from a callback into managed space
        // from another managed space that doesn't want the automatic
        // transition back to its mutator state.
        [RequiredByBartok]
        [Inline]
        internal static unsafe void ReturnFromManagedSpaceNoCallerTransition()
        {
            ThreadContext *currentThreadContext =
                Processor.GetCurrentThreadContext();
#if SINGULARITY_KERNEL
            // In Singularity kernel this function is the exit point of a kernel ABI.
            // If the thread is requested to be aborted, we stop it right here
            currentThreadContext->thread.ProcessAbortIfRequested(AbortRequestSource.ABINoGCExit);
#endif
            TakeDormantControl(currentThreadContext);
        }

        [Inline]
        internal static unsafe bool InDormantState(int threadIndex) {
            ThreadContext *threadContext = GetThreadContext(threadIndex);
            return (threadContext == null ||
                    fInDormantState(threadContext->gcStates));
        }

        [Inline]
        internal static unsafe bool InMutatorState(int threadIndex) {
            ThreadContext *threadContext = GetThreadContext(threadIndex);
            return InMutatorState(threadContext);
        }

        [Inline]
        [NoHeapAllocation]
        internal static unsafe bool InMutatorState(ThreadContext *threadContext)
        {
            return (threadContext != null &&
                    fInMutatorState(threadContext->gcStates));
        }

        [Inline]
        internal static unsafe bool HasGCRequest(int threadIndex) {
            ThreadContext *threadContext = GetThreadContext(threadIndex);
            return (threadContext != null &&
                    fHasGCRequest(threadContext->gcStates));
        }

        [Inline]
        internal static unsafe bool UnderGCControl(int threadIndex) {
            ThreadContext *threadContext = GetThreadContext(threadIndex);
            return (threadContext != null &&
                    fUnderGCControl(threadContext->gcStates));
        }

        [Inline]
        internal static unsafe void TakeDormantControl(int threadIndex)
        {
            ThreadContext *threadContext = GetThreadContext(threadIndex);
            TakeDormantControl(ref threadContext->gcStates, threadIndex);
        }

        [Inline]
        internal static unsafe
        void TakeDormantControl(ThreadContext *threadContext)
        {
            TakeDormantControl(ref threadContext->gcStates,
                               threadContext->threadIndex);
        }

        [Inline]
        internal static unsafe
        void TakeDormantControlNoGC(int currentThreadIndex)
        {
            ThreadContext *threadContext =
                GetCurrentThreadContext(currentThreadIndex);
            TakeDormantControlNoGC(ref threadContext->gcStates);
        }

        [Inline]
        internal static unsafe
        void TakeMutatorControl(int currentThreadIndex)
        {
            ThreadContext *threadContext =
                GetCurrentThreadContext(currentThreadIndex);
            TakeMutatorControl(threadContext);
        }

        [Inline]
        internal static unsafe
        void TakeMutatorControlNoGC(int currentThreadIndex)
        {
            ThreadContext *threadContext =
                GetCurrentThreadContext(currentThreadIndex);
            TakeMutatorControlNoGC(threadContext);
        }

        [Inline]
        internal static unsafe
        void TakeMutatorControl(ThreadContext *threadContext)
        {
            TakeMutatorControl(ref threadContext->gcStates,
                               threadContext->threadIndex);
        }

        [Inline]
        internal static unsafe
        void TakeMutatorControlNoGC(ThreadContext *threadContext)
        {
            TakeMutatorControlNoGC(ref threadContext->gcStates,
                                   threadContext->threadIndex);
        }

        internal static unsafe
        void TakeInitialMutatorControl(ThreadContext *threadContext)
        {
            TakeInitialMutatorControl(ref threadContext->gcStates,
                                      threadContext->threadIndex);
        }

        [Inline]
        internal static unsafe
        void TransferMutatorControl(ThreadContext *currentThreadContext)
        {
            TransferMutatorControl(ref currentThreadContext->gcStates,
                                   currentThreadContext->threadIndex);
        }

        [Inline]
        internal static unsafe
        void EnsureMutatorControl(ThreadContext *currentThreadContext)
        {
            EnsureMutatorControl(ref currentThreadContext->gcStates,
                                 currentThreadContext->threadIndex);
        }

        [Inline]
        internal static unsafe
        void EnsureMutatorControlNoGC(ThreadContext *currentThreadContext)
        {
            EnsureMutatorControlNoGC(ref currentThreadContext->gcStates,
                                     currentThreadContext->threadIndex);
        }

        [Inline]
        internal static unsafe
        void EnsureDormantControl(int currentThreadIndex) {
            ThreadContext *threadContext =
                GetCurrentThreadContext(currentThreadIndex);
            if (!fInDormantState(threadContext->gcStates)) {
                TakeDormantControlNoGC(ref threadContext->gcStates);
            }
        }

        [Inline]
        internal static unsafe bool TakeGCControl(int threadIndex) {
            ThreadContext *threadContext = GetThreadContext(threadIndex);
            return (threadContext != null &&
                    TakeGCControl(ref threadContext->gcStates));
        }

        [Inline]
        internal static unsafe void ReleaseGCControl(int threadIndex) {
            ThreadContext *threadContext = GetThreadContext(threadIndex);
            if (threadContext != null) {
                ReleaseGCControl(ref threadContext->gcStates, threadIndex);
            }
        }

        [Inline]
        internal static unsafe void MakeGCRequest(int threadIndex) {
            ThreadContext *threadContext = GetThreadContext(threadIndex);
            if (threadContext != null) {
                MakeGCRequest(ref threadContext->gcStates, threadIndex);
            }
        }

        [Inline]
        internal static unsafe void ClearGCRequest(int threadIndex) {
            ThreadContext *threadContext = GetThreadContext(threadIndex);
            if (threadContext != null) {
                ClearGCRequest(ref threadContext->gcStates, threadIndex);
            }
        }

#else

        private static int[]       gcReadyTable;

        [NoBarriers]
        [PreInitRefCounts]
        internal static void Initialize()
        {
            // gcReadyTable = new int[Thread.maxThreads];
            gcReadyTable = (int[])
                GCs.BootstrapMemory.Allocate(typeof(int[]), Thread.maxThreads);
            for (int i = 0; i < gcReadyTable.Length; i++) {
                gcReadyTable[i] = DormantState;
            }
        }

        // To be used for callbacks into managed space
        [RequiredByBartok]
        [Inline]
        internal static void EntryIntoManagedSpace() {
            int currentThreadIndex = Thread.GetCurrentThreadIndex();
            TakeMutatorControl(currentThreadIndex);
        }

        // To be used for returning from a callback into managed space
        [RequiredByBartok]
        [Inline]
        internal static void ReturnFromManagedSpace() {
            TakeDormantControl(Thread.GetCurrentThreadIndex());
        }

        [RequiredByBartok]
        [Inline]
        internal static void ReturnFromManagedSpaceNoCallerTransition() {
            TakeDormantControl(Thread.GetCurrentThreadIndex());
        }

        [Inline]
        internal static bool InDormantState(int threadIndex) {
            return fInDormantState(gcReadyTable[threadIndex]);
        }

        [Inline]
        internal static bool InMutatorState(int threadIndex) {
            return fInMutatorState(gcReadyTable[threadIndex]);
        }

        [Inline]
        internal static bool HasGCRequest(int threadIndex) {
            return fHasGCRequest(gcReadyTable[threadIndex]);
        }

        [Inline]
        internal static bool UnderGCControl(int threadIndex) {
            return fUnderGCControl(gcReadyTable[threadIndex]);
        }

        [Inline]
        internal static void TakeDormantControl(int currentThreadIndex) {
            TakeDormantControl(ref gcReadyTable[currentThreadIndex],
                               currentThreadIndex);
        }

        [Inline]
        internal static void TakeDormantControlNoGC(int currentThreadIndex) {
            TakeDormantControlNoGC(ref gcReadyTable[currentThreadIndex]);
        }

        [Inline]
        internal static void TakeMutatorControl(int currentThreadIndex) {
            TakeMutatorControl(ref gcReadyTable[currentThreadIndex],
                               currentThreadIndex);
        }

        [Inline]
        internal static void TakeMutatorControlNoGC(int currentThreadIndex) {
            TakeMutatorControlNoGC(ref gcReadyTable[currentThreadIndex],
                                   currentThreadIndex);
        }

        internal static void TakeInitialMutatorControl(int currentThreadIndex)
        {
            TakeInitialMutatorControl(ref gcReadyTable[currentThreadIndex],
                                      currentThreadIndex);
        }

        [Inline]
        internal static bool TakeGCControl(int threadIndex) {
            return TakeGCControl(ref gcReadyTable[threadIndex]);
        }

        [Inline]
        internal static void ReleaseGCControl(int threadIndex) {
            ReleaseGCControl(ref gcReadyTable[threadIndex], threadIndex);
        }

        [Inline]
        internal static void MakeGCRequest(int threadIndex) {
            MakeGCRequest(ref gcReadyTable[threadIndex], threadIndex);
        }

        [Inline]
        internal static void ClearGCRequest(int threadIndex) {
            ClearGCRequest(ref gcReadyTable[threadIndex], threadIndex);
        }

#endif

        #endregion

    }

}
