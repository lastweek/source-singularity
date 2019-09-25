////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: StackService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity.V1.Services
{
    [AccessedByRuntime("referenced from halstack.asm")]
    public struct StackService
    {
        [ExternalEntryPoint]
        public static void WalkStack()
        {
            Stacks.WalkStack(Isa.GetFramePointer());
        }

        [ExternalEntryPoint]
        [NoHeapAllocation]
        [CLSCompliant(false)]
        public static unsafe void GetUsageStatisticsImpl(ulong *gets, ulong *returns)
        {
            GetUsageStatistics(out *gets, out *returns);
        }

        // The ABI service MemoryUsageInfo provides more comprehensive information
        [NoHeapAllocation]
        [CLSCompliant(false)]
        public static void GetUsageStatistics(out ulong gets, out ulong returns)
        {
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

            // Just summary information
            gets = kernelStackCount + SIPStackCount;
            returns = kernelStackReturnCount + SIPStackReturnCount;
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        [NoStackLinkCheckTrans]
        public static UIntPtr AllocateStackSegmentAbi(UIntPtr growSize) 
        {
            return Stacks.GetSipStackSegment(growSize);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        [NoStackLinkCheckTrans]
        [NoStackOverflowCheck]
        public static void FreeStackSegmentAbi() 
        {
            // First, set threadRecord->activeStackLimit to the proper
            // value for the previous (now current) stack segment.  This
            // ensures that subsequent stack checks are done using the
            // correct stack segment limit.
            Stacks.ActivatePreviousStackSegmentLimit();
            Stacks.ReturnSipStackSegment();
        }

        [CLSCompliant(false)]
        [AccessedByRuntime("called from halstack.asm")]
        [NoStackLinkCheckTrans]
        public static UIntPtr AllocateStackSegment(UIntPtr growSize) 
        {
            return Stacks.GetKernelStackSegment(growSize);
        }

        [CLSCompliant(false)]
        [AccessedByRuntime("called from halstack.asm")]
        [NoStackLinkCheckTrans]
        [NoStackOverflowCheck]
        public static void FreeStackSegment() 
        {
            // First, set threadRecord->activeStackLimit to the proper
            // value for the previous (now current) stack segment.  This
            // ensures that subsequent stack checks are done using the
            // correct stack segment limit.
            Stacks.ActivatePreviousStackSegmentLimit();
            Stacks.ReturnKernelStackSegment();
        }

        [ExternalEntryPoint]
        public static void StackOverflowImpl()
        {
            //
            // This is called when a SIP has a stack overflow so
            // that it can fail fast.
            //

            Stacks.StackOverflowForSIP();
        }
    }
}
