//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs {

    using System.Runtime.CompilerServices;

    internal unsafe abstract class UniversalWriteBarrier : RefWriteBarrier
    {

        [Inline]
        protected override void CopyStructImpl(Object srcObj,
                                               Object dstObj,
                                               VTable vtable,
                                               UIntPtr srcPtr,
                                               UIntPtr dstPtr)
        {
            CopyStructWithBarrier(vtable, srcPtr, dstPtr);
        }

        [Inline]
        protected override void CloneImpl(Object srcObject, Object dstObject)
        {
            CloneWithBarrier(srcObject, dstObject);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        protected override void ArrayZeroImpl(Array array,
                                              int offset,
                                              int length)
        {
            ArrayZeroWithBarrier(array, offset, length);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        protected override void ArrayCopyImpl(Array srcArray, int srcOffset,
                                              Array dstArray, int dstOffset,
                                              int length)
        {
            ArrayCopyWithBarrier(srcArray, srcOffset,
                                 dstArray, dstOffset,
                                 length);
        }

    }

}
