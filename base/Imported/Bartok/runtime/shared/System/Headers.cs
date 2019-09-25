//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


// The header part of an object is split into a PreHeader and a
// PostHeader component.  The PreHeader component is the part of the
// object residing in memory preceding the pointer to the object and
// the PostHeader component is the part at and after the pointer to
// the object.
//
// The StageControl.ObjectHeaderKind option controls which kind of
// header to use.  However, this option provides only basic control.
// Fields can be added to the headers outside the control of this
// StageControl option by using the mixin mechanism.
//
// The "Default" header kind has a MultiUseWord in the PreHeader and a
// VTable in the PostHeader.  The "PostRC" header kind has a
// MultiUseWord in the PreHeader and a refState followed by a VTable
// in the PostHeader.

namespace Microsoft.Bartok.Runtime {

    using Microsoft.Bartok.Options;

    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using Interlocked = System.Threading.Interlocked;

    [RequiredByBartok]
    internal struct PreHeader
    {
        [Intrinsic]
        internal static int Size;
    }

    [RequiredByBartok]
#if SINGULARITY
    [AccessedByRuntime("Accessed from halexn.cpp")]
#endif
    internal struct PostHeader
    {
        [Intrinsic]
        internal static int Size;
    }

    [MixinConditional("ObjectHeaderDefault")]
    [MixinConditional("ObjectHeaderPostRC")]
    [Mixin(typeof(PreHeader))]
    [RequiredByBartok]
    internal struct PreHeaderDefault /* : PreHeader */
    {
        internal MultiUseWord muw;
    }

    [MixinConditional("ObjectHeaderDefault")]
    [Mixin(typeof(PostHeader))]
    [RequiredByBartok]
    internal struct PostHeaderDefault /* : PostHeader */
    {

#if SINGULARITY
        [AccessedByRuntime("accessed from halexn.cpp")]
#else
        [RequiredByBartok]
#endif
        [NoBarriers]
        internal VTable vtableObject;
    }

    [RequiredByBartok]
    [MixinConditional("ObjectHeaderPostRC")]
    [Mixin(typeof(PostHeader))]
    [StructLayout(LayoutKind.Sequential)]
    internal struct PostHeaderRC /* : PostHeader */
    {
        [CompilerInitField(2)]
        internal uint refState;

#if !SINGULARITY
        [RequiredByBartok]
#endif
        [NoBarriers]
        internal VTable vtableObject;

    }

    // This class does not add any fields, nor should it ever be
    // referenced by any other code.  Its sole purpose is to add
    // implementations of the get_vtable, set_vtable, and
    // get_VTableFieldAddr methods to all objects.
    [MixinConditional("ObjectHeaderDefault")]
    [Mixin(typeof(System.Object))]
    internal class ObjectPostVTable
    {
#if SINGULARITY
        [AccessedByRuntime("Accessed from halexn.cpp")]
#endif
        [RequiredByBartok]
        internal new PostHeaderDefault postHeader;

        internal new VTable vtable {
            [Inline]
            get { return this.postHeader.vtableObject; }
            [Inline]
            set { this.postHeader.vtableObject = value; }
        }

        internal unsafe new UIntPtr* VTableFieldAddr {
            [ManualRefCounts]
            [NoBarriers]
            get { return Magic.toPointer(ref this.postHeader.vtableObject); }
        }

    }

    // This class does not add any fields, nor should it ever be
    // referenced by any other code.  Its sole purpose is to add
    // implementations of the get_vtable, set_vtable, and
    // get_VTableFieldAddr methods to all objects.
    [MixinConditional("ObjectHeaderPostRC")]
    [Mixin(typeof(System.Object))]
    internal class ObjectPostVTableRC
    {
        [RequiredByBartok]
        internal new PostHeaderRC postHeader;

        internal new VTable vtable {
            [Inline]
            get { return this.postHeader.vtableObject; }
            [Inline]
            set { this.postHeader.vtableObject = value; }
        }

        internal unsafe new UIntPtr* VTableFieldAddr {
            [ManualRefCounts]
            [NoBarriers]
            get { return Magic.toPointer(ref this.postHeader.vtableObject); }
        }

    }

    // This class does not add any fields, nor should it ever be
    // referenced by any other code.  Its sole purpose is to declare
    // that all objects have get_muw, set_muw, and compareExchangeMUW
    // methods when the object header includes a MultiUseWord field.
    [MixinConditional("ObjectHeaderDefault")]
    [MixinConditional("ObjectHeaderPostRC")]
    [Mixin(typeof(System.Object))]
    internal class ObjectMUW {

        internal extern MultiUseWord muw {
            [Inline]
            get;
            [Inline]
            set;
        }

        [Inline]
        internal extern UIntPtr CompareExchangeMUW(UIntPtr newValue,
                                                   UIntPtr oldValue);

    }

    // This class does not add any fields, nor should it ever be
    // referenced by any other code.  Its sole purpose is to add
    // implementations of the get_muw, set_muw, and compareExchangeMUW
    // methods to all objects when they have a MultiUseWord field.
    [MixinConditional("ObjectHeaderDefault")]
    [MixinConditional("ObjectHeaderPostRC")]
    [Mixin(typeof(ObjectMUW))]
    internal class ObjectPreMUW : ObjectMUW {

        internal new PreHeaderDefault preHeader;

        internal new MultiUseWord muw {
            [Inline]
            get { return this.preHeader.muw; }
            [Inline]
            set { this.preHeader.muw = value; }
        }

        [Inline]
        internal new UIntPtr CompareExchangeMUW(UIntPtr newValue,
                                                UIntPtr oldValue)
        {
            return Interlocked.CompareExchange(ref this.preHeader.muw.value,
                                               newValue, oldValue);
        }

    }

}
