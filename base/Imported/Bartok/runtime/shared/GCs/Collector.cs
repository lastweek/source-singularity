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
    using System.Runtime.CompilerServices;
    using System.Threading;

    [NoCCtor]
    [RequiredByBartok]
    internal abstract class Collector
    {
        // Helper methods for GC.cs
        internal abstract void Collect(Thread currentThread, int generation);
        internal abstract void CollectStoppable(int currentThreadIndex,
                                                int generation);
        internal abstract void CheckForNeededGCWork(Thread currentThread);
        internal abstract int CollectionGeneration(int gen);
        internal abstract int GetGeneration(Object obj);
        internal abstract int MaxGeneration { get; }
        internal abstract int MinGeneration { get; }        
        internal abstract long TotalMemory { get; }
        // Creation and destruction of heaps
        internal abstract void EnableHeap();
        internal abstract void Shutdown();
        internal abstract void DestructHeap();
        // Verification of the heap
        internal abstract void VerifyHeap(bool beforeCollection);
        // Object visitation methods
        internal abstract UIntPtr FindObjectAddr(UIntPtr interiorPtr);
        internal abstract void VisitObjects(ObjectLayout.ObjectVisitor objectVisitor,
                                            UIntPtr lowAddr,
                                            UIntPtr highAddr);
        // Transition methods
        internal abstract void NewThreadNotification(Thread newThread,
                                                     bool initial);
        internal abstract void DeadThreadNotification(Thread deadThread);
        internal abstract void ThreadStartNotification(int currentThreadIndex);
        internal abstract void ThreadEndNotification(Thread currentThread);
        internal abstract void ThreadDormantGCNotification(int threadIndex);
        internal abstract bool IsOnTheFlyCollector {get;}
        // Profiling methods.
        internal virtual void SetProfiler(GCProfiler profiler) { }
        internal virtual  void ProfileAllocation(Object obj)  { }
        // Allocation of objects
        [AssertDevirtualize]
        internal abstract UIntPtr AllocateObjectMemory(UIntPtr numBytes,
                                                       uint alignment,
                                                       Thread currentThread);
        internal abstract Object AllocateObject(VTable vtable,
                                                Thread currentThread);
        internal abstract Object AllocateObject(VTable vtable,
                                                UIntPtr numBytes,
                                                uint baseAlignment,
                                                Thread currentThread);
        internal abstract Array AllocateVector(VTable vtable,
                                               int numElements,
                                               Thread currentThread);
        internal abstract Array AllocateArray(VTable vtable,
                                              int rank, int totalElements,
                                              Thread currentThread);
        internal abstract String AllocateString(int stringLength,
                                                Thread currentThread);
    }        

}
