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
    using Microsoft.Bartok.Options;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

    internal unsafe class BrooksCMSBarrierTest: UniversalWriteBarrier {
        internal static BrooksCMSBarrierTest instance;

        internal static bool allowFastPath;

        [NoBarriers]
        internal static new void Initialize()
        {
            BrooksCMSBarrierTest.instance =
                (BrooksCMSBarrierTest)
                BootstrapMemory.Allocate(typeof(BrooksCMSBarrierTest));
        }

        [RequiredByBartok]
        [MixinConditional("BrooksCMSBarrierTest")]
        [Mixin(typeof(PreHeader))]
        internal struct BrooksPreHeader {
            internal MultiUseWord muw;
            [SelfPoint]
            internal Object forward;
        }

        [MixinConditional("BrooksCMSBarrierTest")]
        [Mixin(typeof(Object))]
        internal class BrooksObject: System.Object {
            internal new BrooksPreHeader preHeader;
        }

        internal static BrooksObject MixinObject(Object o) {
            return (BrooksObject)o;
        }

        [NoBarriers]
        internal static Object Forward(Object o)
        {
            Object result=MixinObject(o).preHeader.forward;
            VTable.Assert(result == o);
            return result;
        }

        [NoBarriers]
        internal static Object ForwardNullable(Object o)
        {
            if (o==null) {
                return null;
            } else {
                return Forward(o);
            }
        }

        [NoBarriers]
        [Inline]
        protected override Object ForwardImpl(Object o, int mask)
        {
            if ((mask&BarrierMask.PathSpec.AllowFast)!=0) {
                return o;
            } else {
                if ((mask&BarrierMask.Forward.Nullable)!=0 && o == null) {
                    return null;
                } else {
                    return Forward(o);
                }
            }
        }

        [ForceInline]
        [NoBarriers]
        protected override bool AllowFastPathImpl()
        {
            return allowFastPath;
        }

        [ForceInline]
        [NoBarriers]
        protected override void InitObjectImpl(Object o, VTable vtable)
        {
            MyInitObject(o, vtable);
        }

        internal static new void BootstrapInitObjectImpl(Object o,
                                                         VTable vtable)
        {
            MyInitObject(o, vtable);
        }

        [ForceInline]
        [NoBarriers]
        private static void MyInitObject(Object o, VTable vtable)
        {
            MixinObject(o).preHeader.forward = o;
            o.vtable = vtable;
        }

        [ForceInline]
        [NoBarriers]
        protected override Object AtomicSwapImpl(ref Object reference,
                                                 Object value,
                                                 int mask)
        {
            CMSMarking.ReferenceCheck(ref reference, value, 0);
            UIntPtr resultAddr =
                Interlocked.Exchange(Magic.toPointer(ref reference),
                                     Magic.addressOf(value));
            return Magic.fromAddress(resultAddr);
        }

        [ForceInline]
        [NoBarriers]
        protected override Object AtomicCompareAndSwapImpl(ref Object loc,
                                                           Object newVal,
                                                           Object comp,
                                                           int mask)
        {
            CMSMarking.ReferenceCheck(ref loc, newVal, 0);
            newVal = ForwardNullable(newVal);
            for (;;) {
                Object oldVal = loc;
                Object commitVal;
                if (oldVal == comp ||
                    ForwardNullable(oldVal) == ForwardNullable(comp)) {
                    commitVal = newVal;
                } else {
                    // still CAS but only to get a memory barrier
                    commitVal = oldVal;
                }
                if (Interlocked.CompareExchange(ref loc,
                                                commitVal, oldVal)
                    == oldVal) {
                    return oldVal;
                }
            }
        }

        [ForceInline]
        [NoBarriers]
        protected override bool EqImpl(Object a, Object b, int mask)
        {
            if ((mask&BarrierMask.PathSpec.AllowFast)!=0) {
                return a == b;
            } else {
                return a == b || ForwardNullable(a) == ForwardNullable(b);
            }
        }

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        protected override void WriteImpl(UIntPtr *location,
                                          Object value,
                                          int mask)
        {
            CMSMarking.ReferenceCheck(location, value, 0);
            *location = Magic.addressOf(value);
        }

        [ForceInline]
        [NoBarriers]
        [NoStackLinkCheckTrans]
        protected override void WriteImplByRef(ref Object location,
                                               Object value,
                                               int mask)
        {
            CMSMarking.ReferenceCheck(ref location, value, 0);
            location = value;
        }
    }
}

