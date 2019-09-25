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

    using Microsoft.Bartok.Runtime;

    using System.Threading;
    using System.Runtime.CompilerServices;

#if SINGULARITY
    using Microsoft.Singularity;
#endif

#if SINGULARITY_KERNEL
    using Microsoft.Singularity.Scheduling;
#endif

    [NoCCtor]
    internal abstract class BaseCollector : Collector
    {

        [Inline]
        protected bool IsValidGeneration(int generation)
        {
            return ((generation >= MinGeneration) &&
                    (generation <= MaxGeneration));
        }

#region Heap Lifetime Events

        internal override void Shutdown()
        {
        }

        internal override void DestructHeap()
        {
            PrintGCTiming();
            PrintAllocations();
            CollectorStatistics.Event(GCEvent.DestroyHeap);
            CollectorStatistics.Summary();
        }

#endregion

#region Notifications

        internal override void NewThreadNotification(Thread newThread,
                                                     bool initial)
        {
            Transitions.NewThreadNotification(newThread.threadIndex, initial);
        }

        internal override void DeadThreadNotification(Thread deadThread)
        {
        }

        internal override void ThreadStartNotification(int currentThreadIndex)
        {
#if !SINGULARITY
            Thread currentThread = Thread.threadTable[currentThreadIndex];
            PageManager.MarkThreadStack(currentThread);
#endif
        }

        internal override void ThreadEndNotification(Thread currentThread)
        {
        }

        internal override void ThreadDormantGCNotification(int threadIndex)
        {
        }

#endregion

#region Allocation

        [ManualRefCounts]
        [Inline]
        internal override Object AllocateObject(VTable vtable,
                                                Thread currentThread)
        {
            return AllocateObject(vtable,
                                  ObjectLayout.ObjectSize(vtable),
                                  vtable.baseAlignment,
                                  currentThread);
        }

        [ManualRefCounts]
        [Inline]
        internal override Object AllocateObject(VTable vtable,
                                                UIntPtr numBytes,
                                                uint baseAlignment,
                                                Thread currentThread)
        {
            UIntPtr objectAddr =
                AllocateObjectMemory(numBytes, baseAlignment,
                                     currentThread);
            Object result = Magic.fromAddress(objectAddr);
            this.CreateObject(result, vtable, currentThread);
            return result;
        }

        [ManualRefCounts]
        internal override Array AllocateVector(VTable vtable,
                                               int numElements,
                                               Thread currentThread)
        {
            UIntPtr numBytes =
                ObjectLayout.ArraySize(vtable, unchecked((uint)numElements));
            UIntPtr vectorAddr =
                AllocateObjectMemory(numBytes, vtable.baseAlignment,
                                     currentThread);
            Array result = Magic.toArray(Magic.fromAddress(vectorAddr));
            CreateObject(result, vtable, currentThread);
            result.InitializeVectorLength(numElements);
            return result;
        }

        [ManualRefCounts]
        internal override  Array AllocateArray(VTable vtable,
                                               int rank,
                                               int totalElements,
                                               Thread currentThread)
        {
            UIntPtr numBytes =
                ObjectLayout.ArraySize(vtable, unchecked((uint)totalElements));
            UIntPtr arrayAddr =
                AllocateObjectMemory(numBytes, vtable.baseAlignment,
                                     currentThread);
            Array result = Magic.toArray(Magic.fromAddress(arrayAddr));
            CreateObject(result, vtable, currentThread);
            result.InitializeArrayLength(rank, totalElements);
            return result;
        }

        [ManualRefCounts]
        internal override String AllocateString(int stringLength,
                                                Thread currentThread)
        {
            VTable vtable =
                Magic.toRuntimeType(typeof(System.String)).classVtable;
            UIntPtr numBytes =
                ObjectLayout.StringSize(vtable,
                                        unchecked((uint) (stringLength+1)));
            UIntPtr stringAddr =
                AllocateObjectMemory(numBytes, unchecked((uint) UIntPtr.Size),
                                     currentThread);
            String result = Magic.toString(Magic.fromAddress(stringAddr));
            CreateObject(result, vtable, currentThread);
            result.InitializeStringLength(stringLength);
            return result;
        }

        [ManualRefCounts]
        [AssertDevirtualize]
        [Inline]
        protected virtual void CreateObject(Object obj, VTable vtable,
                                            Thread currentThread)
        {
            Barrier.InitObject(obj, vtable);
        }

#endregion

#region Profiling

        internal override void SetProfiler(GCProfiler profiler) {
            if (GcProfiler != null) {
                throw new InvalidOperationException("Only one GCProfiler can be active in a process");
            }
            ProfileRoots = new ProfileRootsDelegate(ProfileScanRoots);
            ProfileObjects = new ProfileObjectsDelegate(ProfileScanObjects);

            GcProfiler = profiler;
        }

        // A profiler can request a scan of all Roots, passing in a
        // visitor for callback.
        private void ProfileScanRoots(NonNullReferenceVisitor visitor) {
            CallStack.ScanStacks(visitor, visitor);
            Thread.VisitBootstrapData(visitor);
#if SINGULARITY_KERNEL
            Kernel.VisitSpecialData(visitor);
#endif
            MultiUseWord.VisitStrongRefs(visitor,
                                         false /* Don't use shadows */);
            StaticData.ScanStaticData(visitor);
        }

        // A profiler can request a scan of all Objects in the heap,
        // passing in a visitor for callback.
        private
        void ProfileScanObjects(SegregatedFreeList.ObjectVisitor visitor)
        {
#if !SINGULARITY
            VTable.Assert((System.GC.installedGC as MarkSweepCollector != null)
                          || (System.GC.installedGC as ConcurrentMSCollector != null)
                          || (System.GC.installedGC as ReferenceCountingCollector != null)
                          || (System.GC.installedGC as DeferredReferenceCountingCollector != null),
                          "ProfileScanObjects is only valid for MarkSweep, ConcurrentMS, " 
                          + "ReferenceCounting, and DeferredReferenceCounting collectors");
#endif
            SegregatedFreeList.VisitAllObjects(visitor);
        }

        internal override void ProfileAllocation(Object obj)
        {
            if (GC.IsProfiling && !HeapDamaged) {
                UIntPtr size = ObjectLayout.Sizeof(obj);
                GcProfiler.NotifyAllocation(Magic.addressOf(obj),
                                            obj.GetType(), size);
            }
        }

        protected static GCProfiler GcProfiler;
        protected static ProfileRootsDelegate ProfileRoots;
        protected static ProfileObjectsDelegate ProfileObjects;
        protected static bool HeapDamaged;

#endregion

#region Accounting

        private  static UIntPtr     newBytesSinceGC;
        internal static long        gcTotalBytes;
        internal static int         gcTotalCount;
        internal static long        gcTotalTime;
        private  static long        maxPauseTime;
        private  static long        pauseCount;

        // Abstraction violation.  Use only for debugging!
        internal static UIntPtr DebugNewBytesSinceGC {
            get { return newBytesSinceGC; }
        }

        internal static bool NewBytesSinceGCExceeds(UIntPtr limit)
        {
            return newBytesSinceGC >= limit;
        }

        internal static void IncrementNewBytesSinceGC(UIntPtr increment)
        {
            newBytesSinceGC += increment;
        }

        internal static void StartGCCycle()
        {
            gcTotalBytes += (long) newBytesSinceGC;
            newBytesSinceGC = UIntPtr.Zero;
            gcTotalCount++;
        }

        internal static void RegisterPause(int pauseTicks)
        {
            gcTotalTime += pauseTicks;
            if (maxPauseTime < pauseTicks) {
                maxPauseTime = pauseTicks;
            }
            pauseCount++;
        }

        internal virtual void RegisterHeapSize(ulong heapSize)
        {
        }

        internal virtual void RegisterNewObject(ulong objectSize)
        {
        }

        internal virtual void PrintGCTiming()
        {
            if (VTable.enableGCTiming || VTable.enableFinalGCTiming) {
#if SINGULARITY
                DebugStub.WriteLine("Total GC Time (ms): {0}",
                                    __arglist(gcTotalTime));
#else
                Console.Error.WriteLine("Total GC Time (ms): "+gcTotalTime);
                Console.Error.WriteLine("Max. Pause Time (ms): "+maxPauseTime);
                if (BaseCollector.pauseCount != 0) {
                    Console.Error.WriteLine("Avg. Pause Time (ms): "+
                                            gcTotalTime/pauseCount);
                } else {
                    Console.Error.WriteLine("Avg. Pause Time (ms): 0");
                }
#endif
            }
        }

        internal virtual void PrintAllocations()
        {
        }

#endregion

#region Helper functions

        internal static void AllThreadRendezvous(int currentThreadIndex)
        {
            Transitions.MakeGCRequests(currentThreadIndex);
            for (int i = 0; i < Thread.threadTable.Length; i++) {
                if (Thread.threadTable[i] == null ||
                    i == currentThreadIndex) {
                    continue;
                }
                CollectorStatistics.Event(GCEvent.StopThread, i);
                while (!Transitions.TakeGCControl(i) &&
                       !Transitions.UnderGCControl(i) &&
                       Transitions.HasGCRequest(i) &&
                       Thread.threadTable[i] != null) {
                    // NOTE: there is no code in this loop that could
                    // cause a signal on an event to be consumed.
                    Thread.WaitForGCEvent(currentThreadIndex);
                }
            }
        }

        internal static void AllThreadRelease(int currentThreadIndex)
        {
            for (int i = 0; i < Thread.threadTable.Length; i++) {
#if SINGULARITY_KERNEL
                if (Scheduler.IsIdleThread(i)) {
                    continue;
                }
#endif
                if (i == currentThreadIndex) {
                    if (Transitions.HasGCRequest(i)) {
                        Transitions.ClearGCRequest(i);
                    }
                } else if (Transitions.UnderGCControl(i)) {
                    Transitions.ReleaseGCControl(i);
                }
                // Signal all threads to ensure that the GC process didn't
                // accidentally "gobble" an event signal that was meant for
                // something else.
                if (Thread.threadTable[i] != null) {
                    Thread.SignalGCEvent(i);
                }
            }
        }

#endregion
    }

}
