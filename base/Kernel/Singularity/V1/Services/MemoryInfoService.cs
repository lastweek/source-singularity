////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MemoryInfoService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Memory;

namespace Microsoft.Singularity.V1.Services
{
    public struct MemoryInfoService
    {

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe int MemoryUsageInfo(
            ulong *totalMemoryFree,
            ulong *totalMemoryInUse,
            ulong *kernelHeapInUse,
            ulong *kernelStackInUse,
            ulong *totalSIPHeapInUse,
            ulong *totalSIPStackInUse,
            ulong *kernelStackReservation,
            ulong *kernelHeapReservation
            )
        {
            ulong allocatedCount = 0;
            ulong allocatedBytes = 0;
            ulong freedCount = 0;
            ulong freedBytes = 0;

            ulong userAllocatedCount = 0;
            ulong userAllocatedBytes = 0;
            ulong userFreedCount = 0;
            ulong userFreedBytes = 0;
            ulong kernelHeapReservationLocal = 0;

            *totalMemoryFree = MemoryManager.GetFreePhysicalMemory();
            *totalMemoryInUse = MemoryManager.GetUsedPhysicalMemory();

            //
            // Get general memory info
            //
            MemoryManager.GetUsageStatistics(
                 out allocatedCount,
                 out allocatedBytes,
                 out freedCount,
                 out freedBytes,
                 out kernelHeapReservationLocal
                 );

            //
            // Get SIP (user) memory usage
            //
            MemoryManager.GetUserStatistics(
                 out userAllocatedCount,
                 out userAllocatedBytes,
                 out userFreedCount,
                 out userFreedBytes
                 );

            // Kernel heap is total heap in use - SIP heap in use
            *kernelHeapInUse = (allocatedBytes - freedBytes) - (userAllocatedBytes - userFreedBytes);
            *kernelHeapReservation = kernelHeapReservationLocal;

            *totalSIPHeapInUse = userAllocatedBytes - userFreedBytes;

            // Stack Information
            ulong kernelStackCount = 0;
            ulong kernelStackReturnCount = 0;
            ulong kernelStackBytes = 0;
            ulong kernelStackReturnBytes = 0;
            ulong kernelStackReservationLocal = 0;
            ulong SIPStackCount = 0;
            ulong SIPStackReturnCount = 0;
            ulong SIPStackBytes = 0;
            ulong SIPStackReturnBytes = 0;
            ulong SIPStackReservation = 0;

            MemoryManager.GetStackUsage(
                out kernelStackCount,
                out kernelStackReturnCount,
                out kernelStackBytes,
                out kernelStackReturnBytes,
                out kernelStackReservationLocal,
                out SIPStackCount,
                out SIPStackReturnCount,
                out SIPStackBytes,
                out SIPStackReturnBytes,
                out SIPStackReservation
                );

            *totalSIPStackInUse = SIPStackBytes - SIPStackReturnBytes;
            *kernelStackInUse = kernelStackBytes - kernelStackReturnBytes;
            *kernelStackReservation = kernelStackReservationLocal;

            return 0;
        }
    }
}

