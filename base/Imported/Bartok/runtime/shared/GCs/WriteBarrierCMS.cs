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
    using System.Threading;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    //[NoBarriers]
    internal unsafe class WriteBarrierCMS : UniversalWriteBarrier
    {

        internal static WriteBarrierCMS instance;

        [StructLayout(LayoutKind.Sequential)]
        struct FakeObjectBytes
        {
            public PreHeader preBytes;
            public PostHeader postBytes;
        }
        private static FakeObjectBytes memoryForFakeObject;

        [NoBarriers]
        [NoHeapAllocation]
        internal static WriteBarrierCMS MakeEarlyInstance()
        {
            // We need a write barrier even if we haven't set up enough of the
            // memory system to support allocating from bootstrap memory yet.
            VTable vtable =
                ((RuntimeType) typeof(WriteBarrierCMS)).classVtable;
            UIntPtr numBytes = ObjectLayout.ObjectSize(vtable);
            if (numBytes > (UIntPtr) sizeof(FakeObjectBytes)) {
                return null;    // too big to allocate in memoryForFakeObject
            }
            UIntPtr fakeObjectAddr;
            fixed (PostHeader *middlePtr = & memoryForFakeObject.postBytes) {
                fakeObjectAddr = (UIntPtr) middlePtr;
            }
            Object result = Magic.fromAddress(fakeObjectAddr);
            *result.VTableFieldAddr = Magic.addressOf(vtable);
            return (WriteBarrierCMS) result;
        }

        [PreInitRefCounts]
        [NoBarriers]
        internal static new void Initialize() {
            if (WriteBarrierCMS.instance == null) {
                WriteBarrierCMS.instance = (WriteBarrierCMS)
                    BootstrapMemory.Allocate(typeof(WriteBarrierCMS));
            }
        }

        // NOTE: this code uses ForceInline instead of Inline to indicate that
        // inlining should occur even if the caller is huge.  In general, this
        // attribute should be used with great care.  DO NOT USE IT ELSEWHERE
        // IN THE RUNTIME UNLESS YOU ARE WILLING TO DOCUMENT YOUR USE IN
        // IrSimpleInliner.cs AND Attributes.cs!  AND NEVER USE IT IN
        // APPLICATION OR OS CODE!

        [ForceInline]
        protected override bool AllowFastPathImpl()
        {
            return CMSMarking.referenceCheckIsFast;
        }

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        protected override Object AtomicSwapImpl(ref Object reference,
                                                 Object value,
                                                 int mask)
        {
            CMSMarking.ReferenceCheck(ref reference, value, mask);
            UIntPtr resultAddr =
                Interlocked.Exchange(Magic.toPointer(ref reference),
                                     Magic.addressOf(value));
            return Magic.fromAddress(resultAddr);
        }

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        protected override
        Object AtomicCompareAndSwapImpl(ref Object reference,
                                        Object newValue,
                                        Object comparand,
                                        int mask)
        {
            CMSMarking.ReferenceCheck(ref reference, newValue, mask);
            UIntPtr resultAddr =
                Interlocked.CompareExchange(Magic.toPointer(ref reference),
                                            Magic.addressOf(newValue),
                                            Magic.addressOf(comparand));
            return Magic.fromAddress(resultAddr);
        }

        [Inline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        protected override void CloneImpl(Object srcObject, Object dstObject)
        {
            // There is no need to keep track of initial writes, so do nothing!
            CloneNoBarrier(srcObject, dstObject);
        }

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        protected override void WriteImpl(UIntPtr *location,
                                          Object value,
                                          int mask)
        {
            CMSMarking.ReferenceCheck(location, value, mask);
            *location = Magic.addressOf(value);
        }

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        protected override void WriteImplByRef(ref Object location,
                                               Object value,
                                               int mask)
        {
            CMSMarking.ReferenceCheck(ref location, value, mask);
            location = value;
        }
    }
}
