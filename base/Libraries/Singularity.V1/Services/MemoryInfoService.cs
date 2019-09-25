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

using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.V1.Services
{
    //
    // Design Issue: Singularity SysCalls should be generated from a description
    //       since there is tricky code here to ensure proper locking
    //       objects and validation of parameters occur.
    //
    public struct MemoryInfoService
    {
        //
        // System call boundary must be unsafe to pass pointers
        // to basic types across the GC domains. But this should not be
        // directly accessable to application programs, but behind a
        // trusted safe wrapper that validates parameters and 
        // enforces type safety.
        //
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1170)] // How do we get these values?
        [MethodImpl(MethodImplOptions.InternalCall)]
        internal static extern unsafe int MemoryUsageInfo(
            ulong *totalMemoryFree,
            ulong *totalMemoryInUse,
            ulong *kernelHeapInUse,
            ulong *kernelStackInUse,
            ulong *totalSIPHeapInUse,
            ulong *totalSIPStackInUse,
            ulong *kernelStackReservation,
            ulong *kernelHeapReservation
            );

        //
        // The signature offered to our caller is safe
        //
        public static int MemoryUsageInfo(
            out ulong totalMemoryFree,
            out ulong totalMemoryInUse,
            out ulong kernelHeapInUse,
            out ulong kernelStackInUse,
            out ulong totalSIPHeapInUse,
            out ulong totalSIPStackInUse,
            out ulong kernelStackReservation,
            out ulong kernelHeapReservation
            )
        {
            int retval;

            // This keeps unsafe blocks well contained
            unsafe {

                //
                // Note: Would it be more efficient to declare local stack
                //       variables and reference these under fixed rather
                //       than locking the caller supplied references which
                //       may point to class fields and involve more complicated
                //       GC interactions?
                //
                fixed (ulong* 
                       ptotalMemoryFree = &totalMemoryFree,
                       ptotalMemoryInUse = &totalMemoryInUse,
                       pkernelHeapInUse = &kernelHeapInUse,
                       pkernelStackInUse = &kernelStackInUse,
                       ptotalSIPHeapInUse = &totalSIPHeapInUse,
                       ptotalSIPStackInUse = &totalSIPStackInUse,
                       pkernelStackReservation = &kernelStackReservation,
                       pkernelHeapReservation = &kernelHeapReservation
                       ) {

                    retval = MemoryInfoService.MemoryUsageInfo(
                         ptotalMemoryFree,
                         ptotalMemoryInUse,
                         pkernelHeapInUse,
                         pkernelStackInUse,
                         ptotalSIPHeapInUse,
                         ptotalSIPStackInUse,
                         pkernelStackReservation,
                         pkernelHeapReservation
                         );
                }
            }

            return retval;
        }
    }
}
