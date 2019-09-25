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

    using Microsoft.Bartok.Runtime;
    using System.Runtime.CompilerServices;
    using System.Threading;

    //[NoBarriers]
    internal unsafe class EmptyWriteBarrier : RefWriteBarrier
    {

        internal static EmptyWriteBarrier instance;
        
        [NoBarriers]
        internal static new void Initialize() {
            EmptyWriteBarrier.instance =  (EmptyWriteBarrier)
                BootstrapMemory.Allocate(typeof(EmptyWriteBarrier));
        }

        [Inline]
        protected override void CopyStructImpl(Object srcObj,
                                               Object dstObj,
                                               VTable vtable,
                                               UIntPtr srcPtr,
                                               UIntPtr dstPtr)
        {
            CopyStructNoBarrier(vtable, srcPtr, dstPtr);
        }

        [NoBarriers]
        [Inline]
        protected override Object AtomicSwapImpl(ref Object reference,
                                                 Object value,
                                                 int mask)
        {
            return Interlocked.Exchange(ref reference, value);
        }

        [NoBarriers]
        [Inline]
        protected override
        Object AtomicCompareAndSwapImpl(ref Object reference,
                                        Object newValue,
                                        Object comparand,
                                        int mask)
        {
            return Interlocked.CompareExchange(ref reference,
                                               newValue,
                                               comparand);
        }

        [Inline]
        protected override void CloneImpl(Object srcObject, Object dstObject)
        {
            CloneNoBarrier(srcObject, dstObject);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        protected override void ArrayZeroImpl(Array array,
                                              int offset,
                                              int length)
        {
            ArrayZeroNoBarrier(array, offset, length);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        [Inline]
        protected override void ArrayCopyImpl(Array srcArray, int srcOffset,
                                              Array dstArray, int dstOffset,
                                              int length)
        {
            ArrayCopyNoBarrier(srcArray, srcOffset,
                               dstArray, dstOffset,
                               length);
        }

        [Inline]
        protected override void WriteImpl(UIntPtr *location,
                                          Object value,
                                          int mask)
        {
            *location = Magic.addressOf(value);
        }

        [Inline]
        [NoBarriers]
        protected override void WriteImplByRef(ref Object location,
                                               Object value,
                                               int mask)
        {
            location = value;
        }

    }

}
