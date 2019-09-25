///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: SharedHeapService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using Microsoft.Singularity.V1.Types;

namespace Microsoft.Singularity.V1.Services
{
    public struct SharedHeapService
    {
        public struct AllocationOwnerId {
            // No fields visible to ABI callers.
        }
#if !ROUTE_INDIRECTION_THROUGH_KERNEL
        [StructLayout(LayoutKind.Sequential)]
        public struct Allocation {
            public UIntPtr data;  // Address of the allocated memory region.
            public UIntPtr size;  // Size of above in bytes.
            public UIntPtr type;  // Type information.
            private UIntPtr next;  // Next on owner's list.
            private UIntPtr prev;  // Previous on owner's list.
            public int owner;
        }

#if DEBUG
        [Inline]
        [NoHeapAllocation]
        public static unsafe UIntPtr GetData(Allocation *allocation)
        {
            // CANNOT CHECK THE OWNER HERE UNLESS WE MAKE CURRENTPROCESS visible
            // to this compilation
            //
            // Check owner!
            //            if (allocation->owner != Thread.CurrentProcess.ProcessId) {
            //                DebugStub.Break();
            //            }
            return allocation->data;
        }
#else
        [Inline]
        [NoHeapAllocation]
        public static unsafe UIntPtr GetData(Allocation *allocation)
        {
            return allocation->data;
        }

#endif
        [Inline]
        [NoHeapAllocation]
        public static unsafe UIntPtr GetSize(Allocation *allocation)
        {
            return allocation->size;
            // return (allocation != null) ? allocation->size : UIntPtr.Zero;
        }

        [Inline]
        [NoHeapAllocation]
        public static unsafe UIntPtr GetType(Allocation *allocation)
        {
            return allocation->type;
        }

        [Inline]
        [NoHeapAllocation]
        public static unsafe void SetOwnerProcessId(Allocation *allocation,
                                                    int processId)
        {
            allocation->owner = processId;
        }

#else // ROUTE_INDIRECTION_THROUGH_KERNEL

        public struct Allocation {
            // No fields visible to ABI callers.
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe UIntPtr GetData(Allocation *allocation);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe UIntPtr GetSize(Allocation *allocation);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe UIntPtr GetType(Allocation *allocation);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe UIntPtr SetOwnerProcessId(Allocation *allocation,
                                                              int processId);

#endif // ROUTE_INDIRECTION_THROUGH_KERNEL

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe Allocation *Allocate(UIntPtr size,
                                                         SystemType type,
                                                         uint alignment);

        /// <returns>true if last reference was freed</returns>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool Free(Allocation *allocation);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe Allocation *Share(Allocation *allocation,
                                                      UIntPtr startOffset,
                                                      UIntPtr endOffset);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe Allocation *Split(Allocation *allocation,
                                                      UIntPtr offset);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe void Truncate(Allocation *allocation,
                                                  UIntPtr offset);

#if NOT_YET
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe void TransferTo(
            Allocation *allocation,
            AllocationOwnerId newOwner);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe void TransferFrom(
            Allocation *allocation,
            AllocationOwnerId oldOwner);
#endif

    }

}
