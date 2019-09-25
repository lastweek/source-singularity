////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PageTableService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.V1.Services
{
    public struct PageTableService
    {
        //private readonly int id;

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe uint * GetPageTable();

#if UINTPTR_SUPPORT_IN_ABI
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern UIntPtr GetPageCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern UIntPtr GetBaseAddress();
#endif

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern uint GetProcessTag();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern UIntPtr Allocate(UIntPtr bytes);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern UIntPtr AllocateIOMemory(UIntPtr limit,
                                                      UIntPtr bytes,
                                                      UIntPtr alignment);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern UIntPtr AllocateExtend(UIntPtr addr,
                                                    UIntPtr bytes);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Free(UIntPtr addr,
                                       UIntPtr bytes);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void FreeIOMemory(UIntPtr addr,
                                               UIntPtr bytes);

        [NoHeapAllocation]
        public static bool Query(UIntPtr queryAddr,
                                 out UIntPtr regionAddr,
                                 out UIntPtr regionSize)
        {
            unsafe {
                fixed (UIntPtr * regionAddrPtr = &regionAddr,
                                 regionSizePtr = &regionSize) {
                    return QueryImpl(queryAddr, regionAddrPtr, regionSizePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool QueryImpl(UIntPtr queryAddr,
                                                   UIntPtr * regionAddr,
                                                   UIntPtr * regionSize);

        [NoHeapAllocation]
        public static void GetUsageStatistics(out ulong allocatedCount,
                                              out ulong allocatedBytes,
                                              out ulong freedCount,
                                              out ulong freedBytes)
        {
            unsafe {
                fixed (ulong * allocatedCountPtr = &allocatedCount,
                               allocatedBytesPtr = &allocatedBytes,
                               freedCountPtr = &freedCount,
                               freedBytesPtr = &freedBytes) {
                    GetUsageStatisticsImpl(allocatedCountPtr,
                        allocatedBytesPtr, freedCountPtr, freedBytesPtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe void GetUsageStatisticsImpl(
            ulong * allocatedCount,
            ulong * allocatedBytes,
            ulong * freedCount,
            ulong * freedBytes);

        //////////////////////////////////////////////////////////////////////
        //
#if !UINTPTR_SUPPORT_IN_ABI
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern uint GetPageCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern uint GetBaseAddress();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern uint Allocate(uint bytes);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern uint AllocateIOMemory(uint limit,
                                                   uint bytes,
                                                   uint alignment);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern uint AllocateExtend(uint addr,
                                                 uint bytes);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Free(uint addr,
                                       uint bytes);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void FreeIOMemory(uint addr,
                                               uint bytes);

        [NoHeapAllocation]
        public static bool Query(uint queryAddr,
                                 out uint regionAddr,
                                 out uint regionSize)
        {
            unsafe {
                fixed (uint * regionAddrPtr = &regionAddr,
                              regionSizePtr = &regionSize) {
                    return QueryImpl(queryAddr, regionAddrPtr, regionSizePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool QueryImpl(uint queryAddr,
                                                   uint * regionAddr,
                                                   uint * regionSize);
#endif
    }
}
