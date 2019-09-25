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

    [NoCCtor]
    internal abstract class Allocator
    {

        [Inline]
        [NoHeapAllocation]
        internal static unsafe void WriteAlignment(UIntPtr addr)
        {
            *(UIntPtr*)addr = ALIGNMENT_TOKEN;
        }

        [Inline]
        [NoHeapAllocation]
        internal static unsafe bool IsAlignmentMarkerAddr(UIntPtr addr)
        {
            return (*(UIntPtr*)addr == ALIGNMENT_TOKEN);
        }

        [Inline]
        [NoHeapAllocation]
        internal static unsafe bool IsAlignment(UIntPtr obj)
        {
            return *(UIntPtr*)(obj - PreHeader.Size) == ALIGNMENT_TOKEN;
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr SkipAlignment(UIntPtr obj)
        {
            while (IsAlignment(obj)) {
                obj += UIntPtr.Size;
            }
            return obj;
        }
      
        // Pads the allocation to the appropriate alignment.
        [Inline]
        internal static UIntPtr AlignedAllocationPtr(UIntPtr startAddr,
                                                     UIntPtr limitAddr,
                                                     uint alignment)
        {
            if (alignment > UIntPtr.Size) {
                uint alignmentMask = alignment - 1;
                int offset = PreHeader.Size + PostHeader.Size;
                while (((startAddr + offset) & alignmentMask) != 0 &&
                       startAddr < limitAddr) {
                    Allocator.WriteAlignment(startAddr);
                    startAddr += UIntPtr.Size;
                }
            }
            return startAddr;
        }

        [Inline]
        internal static UIntPtr AlignedObjectPtr(UIntPtr startAddr,
                                                 uint alignment)
        {
            if (alignment > UIntPtr.Size) {
                uint alignmentMask = alignment - 1;
                int offset = PostHeader.Size;
                while (((startAddr + offset) & alignmentMask) != 0) {
                    Allocator.WriteAlignment(startAddr- PreHeader.Size);
                    startAddr += UIntPtr.Size;
                }
            }
            return startAddr;
        }

        private static UIntPtr ALIGNMENT_TOKEN
        {
            [Inline]
            [NoHeapAllocation]
            get { return ~((UIntPtr)3u); }
        }

        // REVIEW: Consider moving to BartokObject --Bjarne
        [NoHeapAllocation]
        internal static unsafe
        UIntPtr * GetObjectVTableAddress(UIntPtr potentialObject)
        {
            UIntPtr vtableAddr = potentialObject + Magic.OffsetOfVTable;
            return (UIntPtr *) vtableAddr;
        }

        // REVIEW: Consider moving to BartokObject --Bjarne
        [NoHeapAllocation]
        internal static unsafe UIntPtr GetObjectVTable(UIntPtr potentialObject)
        {
            return *GetObjectVTableAddress(potentialObject);
        }

        // REVIEW: Consider moving to BartokObject --Bjarne
        [NoHeapAllocation]
        internal static unsafe void SetObjectVTable(UIntPtr potentialObject,
                                                    UIntPtr vtable)
        {
            *GetObjectVTableAddress(potentialObject) = vtable;
        }

        // REVIEW: Consider moving to BartokObject --Bjarne
        [NoHeapAllocation]
        internal static bool IsZeroVTable(UIntPtr addr)
        {
            return GetObjectVTable(addr) == UIntPtr.Zero;
        }

    }

}
