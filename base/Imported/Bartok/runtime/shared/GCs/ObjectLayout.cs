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

    internal class ObjectLayout
    {

        // Tags on GC information provided by compiler.
        internal const uint SPARSE_TAG              = 0x1;
        internal const uint DENSE_TAG               = 0x3;
        internal const uint PTR_VECTOR_TAG          = 0x5;
        internal const uint OTHER_VECTOR_TAG        = 0x7;
        internal const uint PTR_ARRAY_TAG           = 0x9;
        internal const uint OTHER_ARRAY_TAG         = 0xb;
        internal const uint STRING_TAG              = 0xd;
        internal const uint RESERVED_TAG            = 0xf;

        internal abstract class ObjectVisitor {
            // Must return the size of the visited object.
            internal abstract UIntPtr Visit(Object obj);
        }

        // Returns object size in bytes
        [NoBarriers]
        [ManualRefCounts]
        [NoHeapAllocation]
        [Inline]
        internal static UIntPtr ObjectSize(VTable vtable)
        {
            uint baseLength = unchecked((uint)vtable.baseLength);
            VTable.Assert(Util.UIntPtrPad((UIntPtr) baseLength) == baseLength);
            return (UIntPtr)baseLength;
        }

        // Returns string size in bytes
        [NoBarriers]
        [ManualRefCounts]
        [NoHeapAllocation]
        [Inline]
        internal static unsafe UIntPtr StringSize(VTable vtable,
                                                  uint arrayLength)
        {
            uint baseLength = unchecked((uint) vtable.baseLength);
            uint size = (baseLength + sizeof(char)*arrayLength);
            return Util.UIntPtrPad((UIntPtr) size);
        }

        // Returns array size in bytes
        [NoBarriers]
        [ManualRefCounts]
        [NoInline]
        [NoHeapAllocation]
        [Inline]
        internal static UIntPtr ArraySize(VTable vtable, uint numElements)
        {
            UIntPtr baseLength = (UIntPtr)
                unchecked((uint) vtable.baseLength);
            UIntPtr elementSize = (UIntPtr)
                unchecked((uint) vtable.arrayElementSize);
            UIntPtr size = baseLength + elementSize * numElements;
            return Util.UIntPtrPad(size);
        }

        // Returns object size in bytes
        [ManualRefCounts]
        [NoHeapAllocation]
        [Inline]
        internal unsafe static UIntPtr Sizeof(Object obj) {
            return ObjectSize(Magic.addressOf(obj), obj.vtable);
        }

        [ManualRefCounts]
        [NoHeapAllocation]
        internal unsafe static UIntPtr ObjectSize(UIntPtr objectBase,
                                                  VTable vtable)
        {
            uint objectTag =
                unchecked((uint) vtable.pointerTrackingMask) & 0xf;
            switch (objectTag) {
              case SPARSE_TAG:
              case DENSE_TAG: {
                  return ObjectSize(vtable);
              }
              case PTR_VECTOR_TAG:
              case OTHER_VECTOR_TAG: {
                  uint length = *(uint*) (objectBase + PostHeader.Size);
                  return ArraySize(vtable, length);
              }
              case PTR_ARRAY_TAG:
              case OTHER_ARRAY_TAG: {
                  uint length =
                      *(uint*)(objectBase + PostHeader.Size + sizeof(uint));
                  return ArraySize(vtable, length);
              }
              case STRING_TAG: {
                  uint length = *(uint*) (objectBase + PostHeader.Size);
                  return StringSize(vtable, length);
              }
              case RESERVED_TAG: {
                  VTable.Assert(false, "RESERVED_TAG was used!");
                  return UIntPtr.Zero;
              }
              default: {
                  // escape case
                  return ObjectSize(vtable);
              }
            }
        }

    }

}
