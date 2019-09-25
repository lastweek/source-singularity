// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    // TypedReference is basically only ever seen on the call stack, and in param arrays.
    //  These are blobs that must be dealt with by the compiler.
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    //| <include path='docs/doc[@for="TypedReference"]/*' />
    [CLSCompliant(false)] // TODO put this back in, System.Runtime.CompilerServices.NotInGCHeap]
    [StructLayout(LayoutKind.Sequential)]
    public struct TypedReference
    {
        // Bartok will override type of Value to be void& [TracedPointer(void)]
        [RequiredByBartok]
        private IntPtr Value;
        [RequiredByBartok]
        private RuntimeType Type;


        internal TypedReference(IntPtr value, RuntimeType type) {
            this.Value = value;
            this.Type = type;
        }

        [RequiredByBartok]
        internal static TypedReference MakeRefAny(IntPtr value, RuntimeType type)
        {
            TypedReference tr = new TypedReference(value, type);
            return tr;
        }

        [RequiredByBartok]
        internal static RuntimeTypeHandle RefAnyType(TypedReference tr) {
            return new RuntimeTypeHandle(tr.Type);
        }

        [RequiredByBartok]
        internal static IntPtr RefAnyValue(TypedReference tr, RuntimeType type)
        {
            if (tr.Type != type) {
                throw new InvalidCastException();
            }

            return RefAnyValueUnsafe(tr);
        }

        [RequiredByBartok]
        internal static IntPtr RefAnyValueUnsafe(TypedReference tr)
        {
            return tr.Value;
        }

        public static Object ToObject(TypedReference value) {
            throw new Exception("System.TypedReference.ToObject not implemented in Bartok!");
        }

        //| <include path='docs/doc[@for="TypedReference.GetHashCode"]/*' />
        public override int GetHashCode()
        {
            if (Type == null)
                return 0;
            else
                return __reftype(this).GetHashCode();
        }

        //| <include path='docs/doc[@for="TypedReference.Equals"]/*' />
        public override bool Equals(Object o)
        {
            throw new NotSupportedException("NotSupported_NYI");
        }
    }
}
