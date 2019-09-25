////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MemoryReservations.cs - Reservations and tracking of memory for
//                                  Heap, Stacks, SIP's, and Kernel.
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using System.GCs;

using Microsoft.Singularity;

namespace Microsoft.Singularity.Memory
{
    [NoCCtor]
    [CLSCompliant(false)]
    public class MemoryReservations {

        //
        // This class provides one place for memory reservation policy
        // and is used by the different memory managers in the system
        // (FlatPages, Paging allocator, etc.)
        //
        // Memory reservation policy is covered by SDN42 - Handling OutOfMemory
        //
        // Summary of the policy:
        //
        // We ensure there is enough memory for kernel stacks by implementing a per
        // thread kernel stack reservation. We receive notifications of thread create
        // and destroy so this reservation may be tracked in real time.
        //
        // A basic reservation is available for the kernel heap.
        //
        // Allocations for SIP's that exceed the reservations provided above, fail.
        //
        // The reservation policy ensures that we can reliably "fail-fast" the SIP
        // without crashing the kernel due to OOM for stack or heap.
        //
        // The memory managers must live under some strict constraints in regards to
        // allocations themselves, stack linking, no access to managed pointers that
        // could mutate, etc. The methods in this class
        // must adhere to these constraints.
        //

        /////////////////////////////////////
        // CONSTANTS
        /////////////////////////////////////

        // Note: These should be passed in from memory manager during initialize()
        private const ulong kernelStackReservationPerThread = (4096*4); // 16k

        private const ulong kernelStackInitialThreads = 10;

        // Set enough stack reservation for an initial 10 threads
        private const ulong initialKernelStackReservation = kernelStackInitialThreads * kernelStackReservationPerThread;

        private const ulong initialKernelHeapReservation = 1024*512;

        private const ulong initialUserStackReservation = 1024*128;


        /////////////////////////////////////
        // STATIC FIELDS
        /////////////////////////////////////

        //
        // These counters serve two purposes:
        //
        // 1: Provide resource usage monitoring information
        //
        // 2: Provide for memory reservations. In order to provide
        //    for memory reservations reliably in an MP environment, they
        //    are only manipulated while holding the pageLock.
        //

        //
        // This represents total memory allocated and freed
        //
        private static ulong allocatedBytes;
        private static ulong allocatedCount;
        private static ulong freedBytes;
        private static ulong freedCount;

        //
        // This represents the real time count of user (SIP) allocated
        // memory
        //
        private static ulong userAllocatedBytes;
        private static ulong userAllocatedCount;
        private static ulong userFreedBytes;
        private static ulong userFreedCount;

        //
        // These represent kernel and SIP stack usage
        //
        private static ulong stackAllocatedBytes;
        private static ulong stackAllocatedCount;
        private static ulong stackFreedBytes;
        private static ulong stackFreedCount;

        private static ulong userStackAllocatedBytes;
        private static ulong userStackAllocatedCount;
        private static ulong userStackFreedBytes;
        private static ulong userStackFreedCount;

        //
        // This value is updated as threads are created and destroyed
        // and represents the amount that available memory can not
        // drop below without possibly running into a kernel stack OOM.
        //
        private static ulong kernelStackReservation;

        //
        // This represents a kernel heap reservation
        //
        private static ulong kernelHeapReservation;

        //
        // This represents a reservation to allow SIP stacks
        // to be allocated once SIP heap reservations have been
        // exceeded, but not kernel stack+heap reservations.
        //
        // This allows a SIP to continue executing after a SIP
        // allocations are failed to allow the SIP to exit and cleanup.
        //
        // (Ideally, we should not need to rely on allowing further SIP
        //  thread execution for cleanup, but this is a later stage
        //  )
        //
        private static ulong userStackReservation;

        /////////////////////////////////////
        // PUBLIC METHODS
        /////////////////////////////////////

        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void Initialize()
        {
            allocatedBytes = 0;
            allocatedCount = 0;
            freedBytes = 0;
            freedCount = 0;

            userAllocatedBytes = 0;
            userAllocatedCount = 0;
            userFreedBytes = 0;
            userFreedCount = 0;

            stackAllocatedBytes = 0;
            stackAllocatedCount = 0;
            stackFreedBytes = 0;
            stackFreedCount = 0;

            userStackAllocatedBytes = 0;
            userStackAllocatedCount = 0;
            userStackFreedBytes = 0;
            userStackFreedCount = 0;

            kernelStackReservation = initialKernelStackReservation;
            kernelHeapReservation =  initialKernelHeapReservation;

            userStackReservation = initialUserStackReservation;

            return;
        }

        //
        // This returns true if an allocation should fail based on the memory
        // reservation policy and currently available memory.
        //
        // This is called under the lock of the calling memory manager to ensure
        // a consistent view in a multithreaded environment.
        //
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static bool MemoryReservationExceeded(
            ulong availableMemory,
            uint tag,
            bool kernelAllocation,
            UIntPtr size)
        {
             //
             // The owner information is not reliable for determining kernel
             // or SIP allocation when the page type is stack, so the logic
             // is a little extra complicated here.
             //
             if ((tag & MemoryManager.TypeMask) == (uint)PageType.Stack) {

                 //
                 // Stack pages use the kernelAllocation flag to determine
                 // whether the allocation is for the SIP or the kernel stack
                 //
                 if (kernelAllocation) {
                     return false;
                 }
                 else {
                     if (availableMemory < (kernelStackReservation + kernelHeapReservation + size)) {
                         //DebugStub.Break();
                         //DebugStub.WriteLine("CheckMemoryReservation: Failing allocation request for SIP stack due to reservations\n");
                         return true;
                     }
                     else {
                         return false;
                     }
                 }
             }
             else if ((tag & MemoryManager.ProcessPageMask) != MemoryManager.KernelPage) {

                 // process tag is reliable for non-stack allocations

                 //
                 // User heap allocation must be under any outstanding reservations
                 // for the kernel, or SIP stack.
                 //
                 if (availableMemory < (kernelStackReservation + kernelHeapReservation + userStackReservation + size)) {
                     //DebugStub.Break();
                     //DebugStub.WriteLine("CheckMemoryReservation: Failing allocation request for SIP heap due to reservations\n");
                     return true;
                 }
                 else {
                     return false;
                 }
             }
             else {
                 // Kernel heap allocation
                 return false;
             }
        }

        //
        // These are called by the memory manager in order to keep an accurate view
        // of memory reservations in real time. They are called under the memory
        // managers lock.
        //
        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void ThreadCreateNotification()
        {
            kernelStackReservation += kernelStackReservationPerThread;
        }

        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void ThreadDestroyNotification()
        {
            kernelStackReservation -= kernelStackReservationPerThread;
        }

        //
        // Allocation tracking
        //
        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void AllocationForHeap(ulong size)
        {
            allocatedBytes += size;
            allocatedCount++;
        }

        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void AllocationForStack(ulong size)
        {
            stackAllocatedBytes += size;
            stackAllocatedCount++;

            allocatedBytes += size;
            allocatedCount++;
        }

        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void SIPAllocationForHeap(ulong size)
        {
            userAllocatedBytes += size;
            userAllocatedCount++;

            allocatedBytes += size;
            allocatedCount++;
        }

        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void SIPAllocationForStack(ulong size)
        {
            userStackAllocatedBytes += size;
            userStackAllocatedCount++;

            allocatedBytes += size;
            allocatedCount++;
        }

        //
        // Free tracking
        //
        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void FreeForHeap(ulong size)
        {
            freedBytes += size;
            freedCount++;
        }

        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void FreeForStack(ulong size)
        {
            stackFreedBytes += size;
            stackFreedCount++;

            freedBytes += size;
            freedCount++;
        }

        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void SIPFreeForHeap(ulong size)
        {
            userFreedBytes += size;
            userFreedCount++;

            freedBytes += size;
            freedCount++;
        }

        [Inline]
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void SIPFreeForStack(ulong size)
        {
            userStackFreedBytes += size;
            userStackFreedCount++;

            freedBytes += size;
            freedCount++;
        }

        //
        // Statistics gathering methods
        //
        // Calling under a lock is not required unless you want an accurate view
        //
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void GetUsageStatistics(out ulong allocatedCount,
                                               out ulong allocatedBytes,
                                               out ulong freedCount,
                                               out ulong freedBytes,
                                               out ulong kernelHeapReservationArg)
         {
             allocatedCount = MemoryReservations.allocatedCount;
             allocatedBytes = MemoryReservations.allocatedBytes;
             freedCount = MemoryReservations.freedCount;
             freedBytes = MemoryReservations.freedBytes;
             kernelHeapReservationArg = MemoryReservations.kernelHeapReservation;
         }

        //
        // Return user (SIP) memory statistics
        //
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void GetUserStatistics(out ulong allocatedCountArg,
                                               out ulong allocatedBytesArg,
                                               out ulong freedCountArg,
                                               out ulong freedBytesArg)
        {
             allocatedCountArg = userAllocatedCount;
             allocatedBytesArg = userAllocatedBytes;
             freedCountArg = userFreedCount;
             freedBytesArg = userFreedBytes;
        }

        //
        // Return stack usage as raw counters
        //
        [NoHeapAllocation]
        [NoStackLinkCheck]
        internal static void GetStackUsage(
            out ulong kernelStackCount,
            out ulong kernelStackReturnCount,
            out ulong kernelStackBytes,
            out ulong kernelStackReturnBytes,
            out ulong kernelStackReservationArg,
            out ulong userStackCount,
            out ulong userStackReturnCount,
            out ulong userStackBytes,
            out ulong userStackReturnBytes,
            out ulong userStackReservation
            )
        {
            kernelStackCount = stackAllocatedCount;
            kernelStackReturnCount = stackFreedCount;

            kernelStackBytes = stackAllocatedBytes;
            kernelStackReturnBytes = stackFreedBytes;

            kernelStackReservationArg = kernelStackReservation;

            userStackCount = userStackAllocatedCount;
            userStackReturnCount = userStackFreedCount;

            userStackBytes = userStackAllocatedBytes;
            userStackReturnBytes = userStackFreedBytes;

            userStackReservation = 0;

            return;
        }
    }
}

