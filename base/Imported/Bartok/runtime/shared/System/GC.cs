//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to the Bartok Depot and propagated to the Singularity Depot.   */
/*******************************************************************/


namespace System
{
    using Microsoft.Bartok.Runtime;
    using System.GCs;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

#if SINGULARITY
    using Microsoft.Singularity;
#endif

    // The GC has only static members and doesn't require the serializable
    // keyword.
    [CCtorIsRunDuringStartup]
    [RequiredByBartok]
    [AccessedByRuntime("referenced in {hal,brt}{asm,forgc}.asm")]
#if SINGULARITY
    [CLSCompliant(false)]
#endif
    public sealed class GC
    {
        // This is a compiler intrinsic whose value is controlled by
        // /StageControl.HeapSizeConfigurable.
        internal static extern bool HeapSizeConfigurable {
           [Intrinsic]
           get;
        }
        // The *initial* maximum heap size, used if
        // HeapSizeConfigurable is true.
        internal static int MaxHeapPages = 96;

        // Bartok runtime "magic" function
        // It saves the callee-save registers in a transition record and
        // calls System.GC.CollectBody(thread, generation)
        [ManualRefCounts]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.GCFRIEND)]
        [StackBound(128)]
        private static extern void CollectBodyTransition(Thread thread,
                                                         int generation);
#if SINGULARITY_KERNEL
        internal static uint        perfCounter = 6;
#else
        internal static uint        perfCounter = 5;
#endif

        [TrustedNonNull]
        internal static Collector   installedGC;

        private  static bool        isProfiling;

        // Flag to indicate to the collector that it should perform a
        // retrace in a stop-the-world mode after finishing a mostly
        // normal trace.  This allows us to measure the cost of various
        // barriers by disabling them.  Currently only recognized by CONCMS.
        internal static bool        enableSTWRetrace;

        [RequiredByBartok]
        private  static Object      dummyGlobal; // Used by KeepAlive

        [AccessedByRuntime("referenced in halasm.asm/brtasm.asm")]
        internal static int         allocationGCInhibitCount = 0;

        [Intrinsic]
        internal static GCType gcType;

        [Intrinsic]
        internal static WBType wbType;

        [Intrinsic]
        internal static RemSetType remsetType;

        [Intrinsic]
        internal static CopyScanType copyscanType;

#if !SINGULARITY                // Needed before Bartok runtime is initialized
        [NoStackLinkCheck]
#endif
        [PreInitRefCounts]
        internal static void ConstructHeap() {
            PageTable.Initialize();

            MemoryManager.Initialize();
#if OS_WINCE
            UIntPtr heap_commit_size = new UIntPtr(1 << 16);
#elif SINGULARITY
            UIntPtr heap_commit_size = new UIntPtr(1 << 16);
#else
            UIntPtr heap_commit_size = new UIntPtr(1 << 20);
#endif
            UIntPtr os_commit_size = MemoryManager.OperatingSystemCommitSize;
            VTable.Assert(os_commit_size > UIntPtr.Zero);
            VTable.Assert(heap_commit_size >= os_commit_size);
            UIntPtr bootstrapSize;
            if (UIntPtr.Size == 8) {
                if (gcType == GCType.ConcurrentMSCollector) {
                     // increase bootstrap size so that
                     // the concurrent mark sweep collector will run on
                     // 64-bit Windows
                     bootstrapSize = (UIntPtr) 1<<16;
                } else {
                     bootstrapSize = (UIntPtr) 1<<15;
                }
            } else {
                bootstrapSize = (UIntPtr) 1<<14;
            }
            if (bootstrapSize < os_commit_size) {
                bootstrapSize = os_commit_size;
            }
            BootstrapMemory.Initialize(bootstrapSize);
            StaticData.Initialize();
            PageManager.Initialize(os_commit_size, heap_commit_size);
            CallStack.Initialize();
        }

        // Called after the GC is up, but before multi-threading is enabled.
        internal static void FinishInitializeThread()
        {
            PageManager.FinishInitializeThread();
        }

        // NB: This is called from VTable.Initialize()
        [PreInitRefCounts]
        static GC() // Class Constructor (cctor)
        {
            GC.Initialize();
            switch(gcType) {
#if !SINGULARITY || ADAPTIVE_COPYING_COLLECTOR
              case GCType.AdaptiveCopyingCollector: {
                  AdaptiveCopyingCollector.Initialize();
                  GC.installedGC = AdaptiveCopyingCollector.instance;
                  break;
              }
#endif
#if !SINGULARITY || MARK_SWEEP_COLLECTOR
              case GCType.MarkSweepCollector: {
                  MarkSweepCollector.Initialize();
                  GC.installedGC = MarkSweepCollector.instance;
                  break;
              }
#endif
#if !SINGULARITY || TABLE_MARK_SWEEP_COLLECTOR
              case GCType.TableMarkSweepCollector: {
                  SimpleMarkSweepCollector.Initialize();
                  GC.installedGC = SimpleMarkSweepCollector.instance;
                  break;
              }
#endif
#if !SINGULARITY || SEMISPACE_COLLECTOR
              case GCType.SemispaceCollector: {
                  SemispaceCollector.Initialize();
                  GC.installedGC = SemispaceCollector.instance;
                  break;
              }
#endif
#if !SINGULARITY || SLIDING_COLLECTOR
              case GCType.SlidingCollector: {
                  SlidingCollector.Initialize();
                  GC.installedGC = SlidingCollector.instance;
                  break;
              }
#endif
#if !SINGULARITY || CONCURRENT_MS_COLLECTOR
              case GCType.ConcurrentMSCollector: {
                  ConcurrentMSCollector.Initialize();
                  GC.installedGC = ConcurrentMSCollector.instance;
                  break;
              }
#endif
#if !SINGULARITY || ATOMIC_RC_COLLECTOR
              case GCType.AtomicRCCollector: {
                  AtomicRCCollector.Initialize();
                  GC.installedGC = AtomicRCCollector.instance;
                  break;
              }
#endif
#if !SINGULARITY
              case GCType.ReferenceCountingCollector: {
                  ReferenceCountingCollector.Initialize();
                  GC.installedGC = ReferenceCountingCollector.instance;
                  break;
              }
#endif
#if !SINGULARITY
              case GCType.DeferredReferenceCountingCollector: {
                  DeferredReferenceCountingCollector.Initialize();
                  GC.installedGC = DeferredReferenceCountingCollector.instance;
                  break;
              }
#endif
#if !SINGULARITY || NULL_COLLECTOR
              case GCType.NullCollector: {
                  VTable.Assert(wbType == 0, "No need for a write barrier");
                  GC.installedGC =
                      (NullCollector)
                      BootstrapMemory.Allocate(typeof(NullCollector));
                  break;
              }
#endif
#if !SINGULARITY
              case GCType.CoCoMSCollector: {
                  CoCoMSCollector.Initialize();
                  GC.installedGC = CoCoMSCollector.instance;
                  break;
              }
#endif
              default: {
                  VTable.NotReached("Unknown GC type: "+gcType);
                  break;
              }
            }
            GC.installedGC.NewThreadNotification(Thread.initialThread, true);
            GC.installedGC.ThreadStartNotification(Thread.initialThread.threadIndex);
        }

        [NoBarriers]
        [PreInitRefCounts]
        private static void Initialize()
        {
            VTable.Assert(GC.allocationGCInhibitCount == 0);
            GC.allocationGCInhibitCount = 1;
            Transitions.Initialize();
            Barrier.Initialize();
        }

#if !SINGULARITY
        private static DateTime LogMessage(String message)
        {
            DateTime currentTime = System.DateTime.Now;
            System.Text.StringBuilder sb = new System.Text.StringBuilder();
            String hourString = currentTime.Hour.ToString();
            if (hourString.Length == 1) {
                sb.Append('0');
            }
            sb.Append(hourString);
            sb.Append(':');
            String minuteString = currentTime.Minute.ToString();
            if (minuteString.Length == 1) {
                sb.Append('0');
            }
            sb.Append(minuteString);
            sb.Append(':');
            String secondString = currentTime.Second.ToString();
            if (secondString.Length == 1) {
                sb.Append('0');
            }
            sb.Append(secondString);
            sb.Append('.');
            String milliString = currentTime.Millisecond.ToString();
            if (milliString.Length < 3) {
                sb.Append('0');
            }
            if (milliString.Length < 2) {
                sb.Append('0');
            }
            sb.Append(milliString);
            sb.Append(":  ");
            sb.Append(message);
            Console.Out.WriteLine(sb.ToString());
            return currentTime;
        }
#endif

        // This empty class allows us to easily spot the HeapCritialSection
        // mutex when debugging.
        private class HeapMonitor
        {
        }

        internal static void CheckForNeededGCWork(Thread currentThread) {
            installedGC.CheckForNeededGCWork(currentThread);
        }

#if SINGULARITY
        // This is a Singularity special not in the CLR
        public static void Verify()
        {
            DebugStub.WriteLine("Calling VerifyHeap()");
            bool oldGCVerify = VTable.enableGCVerify;
            VTable.enableGCVerify = true;
            Collect();
            VTable.enableGCVerify = oldGCVerify;
            DebugStub.WriteLine("Verification finished.");
        }

        public static void PerformanceCounters(out int collectorCount,
                                               out long collectorMillis,
                                               out long collectorBytes)
        {
            collectorCount  = BaseCollector.gcTotalCount;
            collectorMillis = BaseCollector.gcTotalTime;
            collectorBytes  = BaseCollector.gcTotalBytes;
        }
#endif

        // Garbage Collect all generations.
        [ManualRefCounts]
        public static void Collect()
        {
            installedGC.Collect(Thread.CurrentThread, MaxGeneration);
        }

        public static void Collect(int generation)
        {
            if (generation < 0) {
                throw new ArgumentOutOfRangeException(
                    "generation",
                    "Argument should be positive!");
            }
            installedGC.Collect(Thread.CurrentThread, generation);
        }

        // This method is to be used by various runtime routines that
        // need to trigger a collection.  If there are different kinds
        // of collection, most likely a minor collection will be
        // performed.
        internal static void InvokeCollection(Thread currentThread)
        {
            installedGC.Collect(currentThread,
                                (int)SpecialGeneration.InvokeCollection);
        }

        // This method is to be used by various runtime routines that
        // need to trigger a collection.  If there are different kinds
        // of collections, most likely a major collection will be
        // performed.
        internal static void InvokeMajorCollection(Thread currentThread)
        {
            installedGC.Collect(currentThread,
                                (int)SpecialGeneration.InvokeMajorCollection);
        }

        // This method is to be used by various garbage collector routines
        // that need to trigger a scanning for roots of the call stacks
        // of the program threads.  Calling this method is not meant
        // to trigger a new garbage collection cycle.
        internal static void InvokeStackScanOnly(Thread currentThread)
        {
            installedGC.Collect(currentThread,
                                (int)SpecialGeneration.InvokeStackScanOnly);
        }

        // This method is to be used by various garbage collector routines
        // that need to trigger an update of all references on the call
        // stacks of the program threads.  Calling this method is not meant
        // to trigger a new garbage collection cycle.
        internal static void InvokeStackFixupOnly(Thread currentThread)
        {
            installedGC.Collect(currentThread,
                                (int)SpecialGeneration.InvokeStackFixupOnly);
        }

        internal static void CollectTransition(Thread currentThread,
                                               int generation)
        {
            CollectBodyTransition(currentThread, generation);
        }

        // DO NOT REMOVE THE StackLinkCheck ATTRIBUTE FROM THIS
        // FUNCTION!
        //
        // It is called from native code System.GC.CollectBodyTransition
        // that only has an attribute for the amount of stack space that
        // the native code requires.
        [StackLinkCheck]
        [ManualRefCounts]
        [AccessedByRuntime("called from halforgc.asm/brtforgc.asm")]
        private static unsafe Thread CollectBody(Thread currentThread,
                                                 int generation)
        {
            // NOTE: Refrain from creating any GC safe points in this
            // method.  That includes allocation and system calls,
            // which in turn includes print statements.  Putting a GC
            // safe point before the call to the collector may cause
            // infinite recursion.  Putting a GC safe point after the
            // call to the collector may cause recursion when other
            // threads are triggering collections before the current
            // thread exits this method. (Bjarne)
            int currentThreadIndex = currentThread.threadIndex;
            installedGC.CollectStoppable(currentThreadIndex, generation);
            return Thread.threadTable[currentThreadIndex];
        }

        [RequiredByBartok]
        [AccessedByRuntime("called from brtasm.asm")]
        [Inline]
        [ManualRefCounts]
        internal static Object AllocateObject(VTable vtable)
        {
            return AllocateObject(vtable, Thread.CurrentThread);
        }

        [RequiredByBartok]
        [NoInline]
        [CalledRarely]
        [ManualRefCounts]
        internal static Object AllocateObjectNoInline(VTable vtable)
        {
            return AllocateObject(vtable);
        }

        [RequiredByBartok]
        [Inline]
        [ManualRefCounts]
        internal static Object AllocateObject(VTable vtable,
                                              Thread currentThread)
        {
            VTable.Deny(Transitions.UnderGCControl(currentThread.threadIndex));
            return installedGC.AllocateObject(vtable, currentThread);
        }

        [RequiredByBartok]
        [NoInline]
        [CalledRarely]
        [ManualRefCounts]
        internal static Object AllocateObjectNoInline(VTable vtable,
                                                      Thread currentThread)
        {
            return AllocateObject(vtable, currentThread);
        }

        [RequiredByBartok]
        [Inline]
        [ManualRefCounts]
        internal static Object AllocateObject(VTable vtable,
                                              UIntPtr numBytes,
                                              uint baseAlignment,
                                              Thread currentThread)
        {
            VTable.Deny(Transitions.UnderGCControl(currentThread.threadIndex));
            return installedGC.AllocateObject(vtable,
                                              numBytes,
                                              baseAlignment,
                                              currentThread);
        }

        // Currently only used by MDIL as the compiler explicitly adds the
        // RegisterCandidate call in normal builds.  In the future, however, we
        // would probably like to have this detail expressed in C# rather than
        // in the compiler sources.
        [RequiredByBartok]
        [NoInline]
        [ManualRefCounts]
        internal static Object AllocateFinalizableObject(VTable vtable) {
            Object obj = AllocateObject(vtable);
            Finalizer.RegisterCandidate(obj);
            return obj;
        }

        [RequiredByBartok]
        [Inline]
        [ManualRefCounts]
        internal static Array AllocateVector(VTable vtable, int numElements)
        {
            return AllocateVector(vtable, numElements, Thread.CurrentThread);
        }

        [Inline]
        [ManualRefCounts]
        internal static Array AllocateVector(VTable vtable,
                                             int numElements,
                                             Thread currentThread)
        {
            VTable.Deny(Transitions.UnderGCControl(currentThread.threadIndex));
            return installedGC.AllocateVector(vtable, numElements,
                                              currentThread);
        }

        [RequiredByBartok]
        [Inline]
        [ManualRefCounts]
        internal static Array AllocateArray(VTable vtable, int rank,
                                            int totalElements)
        {
            return AllocateArray(vtable, rank, totalElements,
                                 Thread.CurrentThread);
        }

        [Inline]
        [ManualRefCounts]
        internal static Array AllocateArray(VTable vtable, int rank,
                                            int totalElements,
                                            Thread currentThread)
        {
            VTable.Deny(Transitions.UnderGCControl(currentThread.threadIndex));
            return installedGC.AllocateArray(vtable, rank, totalElements,
                                             currentThread);
        }

        [RequiredByBartok]
        [Inline]
        [ManualRefCounts]
        internal static String AllocateString(int stringLength)
        {
            return AllocateString(stringLength, Thread.CurrentThread);
        }

        [Inline]
        [ManualRefCounts]
        internal static String AllocateString(int stringLength,
                                              Thread currentThread)
        {
            VTable.Deny(Transitions.UnderGCControl(currentThread.threadIndex));
            return installedGC.AllocateString(stringLength, currentThread);
        }

        public static int GetGeneration(Object obj)
        {
            return installedGC.GetGeneration(obj);
        }

        public static int MaxGeneration {
            get { return installedGC.MaxGeneration; }
        }

        internal enum SpecialGeneration {
            InvokeCollection = -1,
            InvokeMajorCollection = -2,
            // Not all collectors use these next two values.
            InvokeStackScanOnly = -3,
            InvokeStackFixupOnly = -4
        }

        internal static bool IsUserCollectionRequest(int gen)
        {
            return gen >= 0;
        }

        internal static bool IsInternalCollectionRequest(int gen)
        {
            return gen == (int)SpecialGeneration.InvokeCollection
                || gen == (int)SpecialGeneration.InvokeMajorCollection;
        }

        internal static bool IsRealCollectionRequest(int gen)
        {
            return gen >= 0
                || gen == (int)SpecialGeneration.InvokeCollection
                || gen == (int)SpecialGeneration.InvokeMajorCollection;
        }

        [NoInline]
        [RequiredByBartok]
        public static void KeepAlive(Object obj)
        {
            dummyGlobal = obj;
            dummyGlobal = null;
        }

        public static void WaitForPendingFinalizers()
        {
            Finalizer.WaitForPending();
        }

        public static long GetTotalMemory(bool forceFullCollection)
        {
            long size = installedGC.TotalMemory;
            if (!forceFullCollection) {
                return size;
            }
            // If we force a full collection, we will run the finalizers on all
            // existing objects and do a collection until the value stabilizes.
            // The value is "stable" when either the value is within 5% of the
            // previous call to installedGC.TotalMemory, or if we have been sitting
            // here for more than x times (we don't want to loop forever here).
            for (int reps = 0; reps < 8; reps++) {
                WaitForPendingFinalizers();
                Collect();
                long newSize = installedGC.TotalMemory;
                long bound = size / 20;  // 5%
                long diff = newSize - size;
                size = newSize;
                if (diff >= -bound && diff <= bound) {
                    break;
                }
            }
            return size;
        }

        public static void SuppressFinalize(Object obj)
        {
            if (obj == null) {
                throw new ArgumentNullException("obj");
            }
            Finalizer.SuppressCandidate(obj);
        }

        internal static void nativeSuppressFinalize(Object obj) {
            Finalizer.SuppressCandidate(obj);
        }

        public static void ReRegisterForFinalize(Object obj)
        {
            if (obj == null) {
                throw new ArgumentNullException("obj");
            }
            Finalizer.RegisterCandidate(obj);
        }

        public static int GetGeneration(WeakReference wo)
        {
            Object obj = wo.Target;
            if (obj == null) {
                throw new ArgumentException("wo", "target already collected");
            }
            return GetGeneration(obj);
        }

        public static void SetProfiler(GCProfiler profiler)
        {
            installedGC.SetProfiler(profiler);
            isProfiling = true;
        }

        public static bool IsProfiling
        {
            get {
                return isProfiling;
            }
        }

        internal static void ProfileAllocation(Object obj)
        {
            if (isProfiling) {
                installedGC.ProfileAllocation(obj);
            }
        }

        private static void SetCleanupCache()
        {
            // REVIEW: will not ever clean up these caches (such as Assembly
            // strong names)
        }

        internal static void EnableHeap()
        {
            VTable.Assert(GC.allocationGCInhibitCount == 1);
            GC.allocationGCInhibitCount = 0;
            CollectorStatistics.Initialize();
            CollectorStatistics.Event(GCEvent.CreateHeap);
            GC.installedGC.EnableHeap();
            Finalizer.StartFinalizerThread();
        }

        internal static void Shutdown()
        {
            if(installedGC != null) {
                installedGC.Shutdown();
            }
        }

        // Called on VM shutdown.
        internal static void DestructHeap()
        {
            if (installedGC != null) {
                installedGC.DestructHeap();
            }
        }

        internal static void NewThreadNotification(Thread newThread,
                                                   bool initial)
        {
            GC.installedGC.NewThreadNotification(newThread, initial);
        }

        internal static void DeadThreadNotification(Thread deadThread)
        {
            GC.installedGC.DeadThreadNotification(deadThread);
        }

        internal static void ThreadStartNotification(int currentThreadIndex)
        {
            GC.installedGC.ThreadStartNotification(currentThreadIndex);
        }

        internal static void ThreadEndNotification(Thread dyingThread)
        {
            GC.installedGC.ThreadEndNotification(dyingThread);
        }

        internal static void ThreadDormantGCNotification(int threadIndex)
        {
            GC.installedGC.ThreadDormantGCNotification(threadIndex);
        }

    }

}
