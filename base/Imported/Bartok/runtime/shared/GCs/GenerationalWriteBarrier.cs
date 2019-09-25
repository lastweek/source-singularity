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
    internal unsafe class GenerationalWriteBarrier : RefWriteBarrier
    {

        internal static GenerationalWriteBarrier instance;

        [NoBarriers]
        internal static new void Initialize() {
            GenerationalWriteBarrier.instance = (GenerationalWriteBarrier)
                BootstrapMemory.Allocate(typeof(GenerationalWriteBarrier));
        }

        [Inline]
        [NoBarriers]
        protected override void StoreStaticFieldImpl(ref Object staticField,
                                                     Object value,
                                                     int mask)
        {
            // No need to perform a ReferenceCheck here!
            staticField = value;
        }

        protected override void CopyStructImpl(Object srcObj,
                                               Object dstObj,
                                               VTable vtable,
                                               UIntPtr srcPtr,
                                               UIntPtr dstPtr)
        {
            CopyStructWithBarrier(vtable, srcPtr, dstPtr);
        }

        [Inline]
        protected override Object AtomicSwapImpl(ref Object reference,
                                                 Object value,
                                                 int mask)
        {
            UIntPtr *ptr=Magic.toPointer(ref reference);
            UIntPtr resultAddr =
                Interlocked.Exchange(ptr,
                                     Magic.addressOf(value));
            ReferenceCheck(ptr, value);
            return Magic.fromAddress(resultAddr);
        }

        [Inline]
        protected override
        Object AtomicCompareAndSwapImpl(ref Object reference,
                                        Object newValue,
                                        Object comparand,
                                        int mask)
        {
            UIntPtr *ptr=Magic.toPointer(ref reference);
            UIntPtr resultAddr =
                Interlocked.CompareExchange(ptr,
                                            Magic.addressOf(newValue),
                                            Magic.addressOf(comparand));
            ReferenceCheck(ptr, newValue);
            return Magic.fromAddress(resultAddr);
        }

        [Inline]
        protected override void CloneImpl(Object srcObject, Object dstObject)
        {
            CloneNoBarrier(srcObject, dstObject);
            ReferenceCheck(dstObject);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        protected override void ArrayZeroImpl(Array array,
                                              int offset,
                                              int length)
        {
            ArrayZeroNoBarrier(array, offset, length);
        }

        // 'offset' is not relative to the lower bound, but is a count
        // of elements from the first element in the array.
        protected override void ArrayCopyImpl(Array srcArray, int srcOffset,
                                              Array dstArray, int dstOffset,
                                              int length)
        {
            if ((length > 1000) || ((length << 2) >= dstArray.Length)) {
                ArrayCopyNoBarrier(srcArray, srcOffset,
                                   dstArray, dstOffset,
                                   length);
                ReferenceCheck(dstArray);
            } else {
                ArrayCopyWithBarrier(srcArray, srcOffset,
                                     dstArray, dstOffset,
                                     length);
            }
        }

        [Inline]
        protected override void WriteImpl(UIntPtr *location,
                                          Object value,
                                          int mask)
        {
            WriteImplNoMask(location, value);
        }

        [RequiredByBartok]
        [Inline]
        private static void WriteImplNoMask(UIntPtr *location,
                                            Object value)
        {
            *location = Magic.addressOf(value);
            ReferenceCheck(location, value);
        }

        [Inline]
        protected override void WriteImplByRef(ref Object location,
                                               Object value,
                                               int mask)
        {
            WriteImpl(Magic.toPointer(ref location), value, mask);
        }

        [Inline]
        private static void ReferenceCheck(Object obj) {
            PageType pageType =
                PageTable.Type(PageTable.Page(Magic.addressOf(obj)));
            if (GenerationalGCData.MAX_GENERATION == PageType.Owner1) {
                if (pageType == PageType.Owner1) {
                    GenerationalGCData.
                        installedRemSet.RecordClonedObject(obj);
                }
            } else {
                if (pageType != GenerationalGCData.nurseryGeneration) {
                    GenerationalGCData.
                        installedRemSet.RecordClonedObject(obj);
                }
            }
        }

        [Inline]
        private static void ReferenceCheck(UIntPtr *addr, Object value)
        {
            PageType addrType = PageTable.Type(PageTable.Page((UIntPtr) addr));
            if (GenerationalGCData.MAX_GENERATION == PageType.Owner1) {
                if (addrType != PageType.Owner1) {
                    return;
                } else {
                    ReferenceCheck(addrType, addr, value);
                }
            } else {
                if (PageTable.IsLiveGcPage(addrType)){
                    ReferenceCheck(addrType, addr, value);
                }
            }
        }

        [NoInline]
        private static void ReferenceCheck(PageType addrType, UIntPtr *addr,
                                           Object value) {
            VTable.Assert(PageTable.IsGcPage(addrType));

            if (GC.remsetType == RemSetType.Cards) {
               GenerationalGCData.
                    installedRemSet.RecordReference(addr, value);
               return;
            }
            
            UIntPtr valueAddr = Magic.addressOf(value);
            PageType valType = PageTable.Type(PageTable.Page(valueAddr));
            if (PageTable.IsGcPage(valType) && (addrType > valType)){
                GenerationalGCData.
                    installedRemSet.RecordReference(addr, value);
            }
        }

    }

}
