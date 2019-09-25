//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


namespace System.GCs {

    using Microsoft.Bartok.Runtime;
    using System.Threading;
    using System.Runtime.CompilerServices;

    internal unsafe class BootstrapMemory : Allocator
    {

        // WARNING: don't initialize any static fields in this class
        // without manually running the class constructor at startup!

        private static UIntPtr allocPtr;
        private static UIntPtr limitPtr;

        [PreInitRefCounts]
#if !SINGULARITY                // Needed before Bartok runtime is initialized
        [NoStackLinkCheck]
#endif
        [NoBarriers]
        internal static void Initialize(UIntPtr systemMemorySize) {
            allocPtr = MemoryManager.AllocateMemory(systemMemorySize);
            limitPtr = allocPtr + systemMemorySize;
            if(GC.gcType != GCType.NullCollector) {
                PageManager.SetStaticDataPages(allocPtr, systemMemorySize);
#if !SINGULARITY
                PageTable.SetProcess(PageTable.Page(allocPtr),
                                     PageTable.PageCount(systemMemorySize));
#endif
            }
        }

        [NoBarriers]
        private static UIntPtr AllocateBlock(UIntPtr bytes, uint alignment)
        {
            UIntPtr startPtr =
                Allocator.AlignedAllocationPtr(allocPtr, limitPtr, alignment);
            allocPtr = startPtr + bytes;
            if (allocPtr > limitPtr) {
                VTable.DebugPrint("Out of BootstrapMemory");
                VTable.DebugBreak();
            }
            return startPtr + PreHeader.Size;
        }

        [NoBarriers]
        [ManualRefCounts]
#if !SINGULARITY                // Needed before Bartok runtime is initialized
        [NoStackLinkCheckTrans]
#endif
        internal static Object Allocate(VTable vtable) {
            UIntPtr numBytes = ObjectLayout.ObjectSize(vtable);
            UIntPtr objectAddr = AllocateBlock(numBytes, vtable.baseAlignment);
            Object result = Magic.fromAddress(objectAddr);
#if REFERENCE_COUNTING_GC
            uint refState = vtable.isAcyclicRefType ?
                (ReferenceCountingCollector.
                acyclicFlagMask | 2) : 2;
            result.REF_STATE = refState &
                ~ReferenceCountingCollector.countingONFlagMask;
#elif DEFERRED_REFERENCE_COUNTING_GC
            uint refState = vtable.isAcyclicRefType ?
                (DeferredReferenceCountingCollector.
                 acyclicFlagMask |
                 DeferredReferenceCountingCollector.
                 markFlagMask) :
                DeferredReferenceCountingCollector.
                markFlagMask;
            result.REF_STATE = refState &
                ~DeferredReferenceCountingCollector.countingONFlagMask;
#endif
            Barrier.BootstrapInitObject(result, vtable);
            return result;
        }

        [NoBarriers]
        [ManualRefCounts]
#if !SINGULARITY                // Needed before Bartok runtime is initialized
        [NoStackLinkCheckTrans]
#endif
        internal static Object Allocate(VTable vtable, uint count) {
            UIntPtr numBytes = ObjectLayout.ArraySize(vtable, count);
            UIntPtr objectAddr = AllocateBlock(numBytes, vtable.baseAlignment);
            Array result = Magic.toArray(Magic.fromAddress(objectAddr));
#if REFERENCE_COUNTING_GC
            uint refState = vtable.isAcyclicRefType ?
                (ReferenceCountingCollector.
                acyclicFlagMask | 2) : 2;
            result.REF_STATE = refState &
                ~ReferenceCountingCollector.countingONFlagMask;
#elif DEFERRED_REFERENCE_COUNTING_GC
            uint refState = vtable.isAcyclicRefType ?
                (DeferredReferenceCountingCollector.
                 acyclicFlagMask |
                 DeferredReferenceCountingCollector.
                 markFlagMask) :
                DeferredReferenceCountingCollector.
                markFlagMask;
            result.REF_STATE = refState &
                ~DeferredReferenceCountingCollector.countingONFlagMask;
#endif
            Barrier.BootstrapInitObject(result, vtable);
            result.InitializeVectorLength((int) count);
            return result;
        }

        [NoBarriers]
        [PreInitRefCounts]
#if !SINGULARITY
        [NoStackLinkCheckTrans]
#endif
        internal static Object Allocate(Type t) {
            return Allocate(Magic.toRuntimeType(t));
        }

        [NoBarriers]
        [PreInitRefCounts]
#if !SINGULARITY
        [NoStackLinkCheckTrans]
#endif
        internal static Object Allocate(Type t, uint count) {
            return Allocate(Magic.toRuntimeType(t), count);
        }

        [NoBarriers]
        [PreInitRefCounts]
#if !SINGULARITY
        [NoStackLinkCheckTrans]
#endif
        internal static Object Allocate(RuntimeType t) {
            return Allocate(t.classVtable);
        }

        [NoBarriers]
        [PreInitRefCounts]
#if !SINGULARITY
        [NoStackLinkCheckTrans]
#endif
        internal static Object Allocate(RuntimeType t, uint count) {
            return Allocate(t.classVtable, count);
        }

        internal static void Truncate() {
            UIntPtr allocLimit = PageTable.PagePad(allocPtr);
            UIntPtr unusedSize = limitPtr - allocLimit;
            if(GC.gcType != GCType.NullCollector) {
                PageManager.ReleaseUnusedPages(PageTable.Page(allocLimit),
                                               PageTable.PageCount(unusedSize),
                                               true);
            }
            limitPtr = allocLimit;
        }

    }

}
