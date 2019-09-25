////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   StackService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Microsoft.Singularity.V1.Services
{
    [AccessedByRuntime("called from halstack.asm")]
    public struct StackService
    {
        [OutsideGCDomain]
        [StackBound(1088)]
        public static extern void WalkStack();

        [NoHeapAllocation]
        public static void GetUsageStatistics(
            out ulong gets,
            out ulong returns)
        {
            unsafe {
                fixed (ulong * getsPtr = &gets, returnsPtr = &returns) {
                    GetUsageStatisticsImpl(getsPtr, returnsPtr);
                }
            }
        }

        [OutsideGCDomain]
        [StackBound(1170)]
        public static extern unsafe void GetUsageStatisticsImpl(
            ulong * gets,
            ulong * returns);

        [NoHeapAllocation]
        public static void StackOverflow()
        {
            unsafe {
                StackOverflowImpl();
            }
        }

        [NoHeapAllocation]
        [AccessedByRuntime("called from halstack.asm")]
        [NoStackLinkCheckTrans]
        public static UIntPtr AllocateStackSegment(UIntPtr growSize)
        {
            UIntPtr stack = AllocateStackSegmentAbi(growSize);
            if (stack == 0) {

                // We end up here if the SIP stack allocation failed, so we must
                // invoke a kernel handler that will exit the current SIP.

                StackOverflowImpl(); // will not return.
            }

            return stack;
        }
        
        [NoHeapAllocation]
        [AccessedByRuntime("called from halstack.asm")]
        [NoStackLinkCheckTrans]
        [NoStackOverflowCheck]
        public static void FreeStackSegment()
        {
            FreeStackSegmentAbi();
        }

        // It is important that the following three ABI calls do not do the
        // usual GC boundary checks.  The methods are called in situations
        // where there is very little room on the current stack segment.
        // The code to perform a GC or collaborate with a GC cycle is
        // likely to cause stack growth that exceeds the available space.

        [OutsideGCDomain]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1170)]
        public static extern UIntPtr AllocateStackSegmentAbi(UIntPtr growSize);

        [OutsideGCDomain]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1170)]
        public static extern void FreeStackSegmentAbi();

        [OutsideGCDomain]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1170)]
        public static extern void StackOverflowImpl();
   }
}
