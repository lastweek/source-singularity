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
using System.Threading;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.V1.Types;

namespace Microsoft.Singularity.V1.Services
{
    [CLSCompliant(false)]
    public struct SharedHeapService
    {
        public struct Allocation {
            // No fields visible to ABI callers.
        }

        [ExternalEntryPoint]
        [NoHeapAllocation]
        public static unsafe UIntPtr GetData(Allocation *allocation)
        {
            return SharedHeap.Allocation.GetData(
                (SharedHeap.Allocation *)allocation);
        }

        [ExternalEntryPoint]
        [NoHeapAllocation]
        public static unsafe UIntPtr GetSize(Allocation *allocation)
        {
            return SharedHeap.Allocation.GetSize(
                (SharedHeap.Allocation *)allocation);
        }

        [ExternalEntryPoint]
        [NoHeapAllocation]
        public static unsafe UIntPtr GetType(Allocation *allocation)
        {
            return SharedHeap.Allocation.GetType(
                (SharedHeap.Allocation *)allocation);
        }

        [ExternalEntryPoint]
        public static unsafe Allocation *Allocate(UIntPtr size,
                                                  SystemType type,
                                                  uint alignment)
        {
            return (Allocation *)SharedHeap.CurrentProcessSharedHeap.Allocate(
                size, type.id, alignment,
                SharedHeap.CurrentProcessSharedHeap.DataOwnerId);
        }

        /// <returns>true if last reference was freed</returns>
        [ExternalEntryPoint]
        public static unsafe bool Free(Allocation *allocation)
        {
            return SharedHeap.CurrentProcessSharedHeap.Free(
                                   (SharedHeap.Allocation *)allocation,
                                   SharedHeap.CurrentProcessSharedHeap.DataOwnerId);
        }

        [ExternalEntryPoint]
        public static unsafe Allocation *Share(Allocation *allocation,
                                               UIntPtr startOffset,
                                               UIntPtr endOffset)
        {
            return (Allocation *)SharedHeap.CurrentProcessSharedHeap.Share(
                (SharedHeap.Allocation *)allocation,
                SharedHeap.CurrentProcessSharedHeap.DataOwnerId,
                startOffset,
                endOffset);
        }

        [ExternalEntryPoint]
        public static unsafe Allocation *Split(Allocation *allocation,
                                               UIntPtr offset)
        {
            return (Allocation *)SharedHeap.CurrentProcessSharedHeap.Split(
                (SharedHeap.Allocation *)allocation,
                SharedHeap.CurrentProcessSharedHeap.DataOwnerId,
                offset);
        }

        [ExternalEntryPoint]
        public static unsafe void Truncate(Allocation *allocation,
                                           UIntPtr newLength)
        {
            SharedHeap.CurrentProcessSharedHeap.Truncate(
                (SharedHeap.Allocation *)allocation,
                newLength
                );
        }

        internal static unsafe void SetOwnerProcessId(
            Allocation *allocation,
            int newOwnerProcessId)
        {
            SharedHeap.Allocation.SetOwnerProcessId(
                (SharedHeap.Allocation *)allocation,
                newOwnerProcessId);
        }

        internal static unsafe void SetType(
            Allocation *allocation,
            UIntPtr type)
        {
            SharedHeap.Allocation.SetType(
                (SharedHeap.Allocation *)allocation,
                type);
        }

#if NOT_YET
        [ExternalEntryPoint]
        public static unsafe void TransferTo(
            Allocation *allocation,
            AllocationOwnerId newOwner)
        {
            return SharedHeap.TransferOwnership(
                (SharedHeap.Allocation *)allocation,
                SharedHeap.CurrentProcessSharedHeap.DataOwnerId,
                newOwner);
        }

        [ExternalEntryPoint]
        public static unsafe void TransferFrom(
            Allocation *allocation,
            AllocationOwnerId oldOwner)
        {
            return SharedHeap.TransferOwnership(
                (SharedHeap.Allocation *)allocation,
                oldOwner,
                SharedHeap.CurrentProcessSharedHeap.DataOwnerId);
        }
#endif

    }
}
