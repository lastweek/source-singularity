//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


// Provides a number of "magic" casting functions needed by trusted components
// of the runtime.

namespace Microsoft.Bartok.Runtime {

    using System;
    using System.Runtime.CompilerServices;
    using System.Threading;

    internal sealed class Magic {

        // Returns the offset of the vtable from the base of an object.
        // The base is the beginning of the PostHeader.
        // Typically callers should access Object's vtable property directly,
        // but this is used by a few places that may be abusing the vtable slot
        // to hold values of type UIntPtr.
        internal static extern UIntPtr OffsetOfVTable {
            [NoHeapAllocation]
            [Intrinsic]
            get;
        }

        // Cast an object to a UIntPtr, equivalent to MSIL conv.u.
        [Intrinsic]
        [NoHeapAllocation]
        internal static extern UIntPtr addressOf(Object o);

        // The toPointer family of methods cast a managed pointer to T to an
        // unmanaged pointer to T.  Exceptions are the Object and VTable
        // versions which return UIntPtr* instead since Object* and VTable*
        // are illegal.  These are equivalent to MSIL conv.u.
        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern UIntPtr *toPointer(ref Object o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern bool *toPointer(ref bool o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern char *toPointer(ref char o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern float *toPointer(ref float o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern double *toPointer(ref double o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern sbyte *toPointer(ref sbyte o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern short *toPointer(ref short o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern int *toPointer(ref int o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern long *toPointer(ref long o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern IntPtr *toPointer(ref IntPtr o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern byte *toPointer(ref byte o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern ushort *toPointer(ref ushort o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern uint *toPointer(ref uint o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern ulong *toPointer(ref ulong o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern UIntPtr *toPointer(ref UIntPtr o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static unsafe extern UIntPtr *toPointer(ref VTable o);

        // Cast a UIntPtr to an object.  This has no MSIL instruction
        // equivalent.  This is used, for example, at the birth point of an
        // object.
        [Intrinsic]
        [NoHeapAllocation]
        internal static extern Object fromAddress(UIntPtr v);

        // The various toXXX methods are unchecked (and therefore unsafe)
        // downcasts.  They are used in places where vtables may be invalid (and
        // hence checked casts would fail).  Uses as hand-optimizations should
        // be avoided when possible.
        [Intrinsic]
        [NoHeapAllocation]
        internal static extern Thread toThread(Object o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static extern Monitor toMonitor(Object o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static extern EMU toEMU(Object o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static extern VTable toVTable(Object o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static extern Array toArray(Object o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static extern UIntPtr[] toUIntPtrVector(Array a);

        [Intrinsic]
        [NoHeapAllocation]
        internal static extern String toString(Object o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static extern RuntimeType toRuntimeType(Object o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static extern Type toType(Object o);

        [Intrinsic]
        [NoHeapAllocation]
        internal static extern uint[] toUIntArray(Object o);

        [Intrinsic]
        internal static extern WeakReference toWeakReference(Object o);

        // Performs an indirect call on the pointer 'p'.
        // This is equivalent to MSIL calli on the signature ()->void.
        [Intrinsic]
        internal static extern void calli(System.UIntPtr p);

        // Performs an indirect call on the pointer 'p' with argument 'v'.
        // This is equivalent to MSIL calli on the signature (UIntPtr)->void.
        [Intrinsic]
        internal static extern void calli(System.UIntPtr p, System.UIntPtr v);

        // Calls the Finalize method on an object.  This is needed for the
        // finalizer implementation because C# will not allow direct calls to
        // finalizers.
        [Intrinsic]
        internal static extern void callFinalizer(Object o);

        // These are very dangerous utilties that essentially do
        //
        // [o + offset] = data
        //
        // They are currently used for undoing heap stores collected in the
        // tryall/atomic logs.  Any other use should be cleared by at least the
        // Bartok team.
        [Intrinsic]
        internal static extern void SetAt(Object o, UIntPtr offset,
                                          UIntPtr data);
        [Intrinsic]
        internal static extern void SetAt(Object o, UIntPtr offset,
                                          Object data);
    }
    
}

