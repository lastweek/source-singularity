/*
// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: Marshal
//
// Purpose: This class contains methods that are mainly used to marshal
//          between unmanaged and managed types.
//
//=============================================================================  

namespace System.Runtime.InteropServices
{

    using Microsoft.Bartok.Runtime;
    using System;
    using System.Runtime.CompilerServices;

    //========================================================================
    // All public methods, including PInvoke, are protected with linkchecks.
    // Remove the default demands for all PInvoke methods with this global
    // declaration on the class.
    //========================================================================

    //| <include path='docs/doc[@for="Marshal"]/*' />
    public sealed class Marshal
    {
        //====================================================================
        // SizeOf()
        //====================================================================
        //| <include path='docs/doc[@for="Marshal.SizeOf"]/*' />
        // TODO PORTING: For 64 bit port, Ati considered making SizeOf return an IntPtr instead of an Int.  Consider making that change AND updating ECALL method sig.
        public static int SizeOf(Object structure)
        {
            VTable vtable = structure.vtable;
            if (vtable.arrayOf == StructuralType.None) {
                if (vtable.Equals("string".vtable)) {
                    throw new Exception("SizeOf not implemented for string objects");
                }
                else {
                    return vtable.marshalSize;
                }
            }
            else {
                int elementSize = vtable.arrayElementSize;
                int elementMask = elementSize - 1;
                int numElements = ((Array) structure).Length;
                return ((int)vtable.baseLength +
                        numElements * elementSize +
                        elementMask) & ~elementMask;
            }
        }

        //| <include path='docs/doc[@for="Marshal.SizeOf1"]/*' />
        public static int SizeOf(Type t)
        {
            RuntimeType runtimeType = (RuntimeType) t;
            VTable vtable = runtimeType.classVtable;
            if (vtable.arrayOf == StructuralType.None &&
                !t.Equals("string".GetType())) {
                return vtable.marshalSize;
            }
            else {
                throw new Exception("SizeOf not implemented for type "+t);
            }
        }

        ///
        /// Used by the shared heap to allocate structs.
        ///
        public static int StructSize(Type t)
        {
            RuntimeType runtimeType = (RuntimeType) t;
            VTable vtable = runtimeType.classVtable;
            if (vtable.arrayOf == StructuralType.None &&
                !t.Equals("string".GetType())) {
                return vtable.arrayElementSize;
            }
            else {
                throw new Exception("SizeOf not implemented for type "+t);
            }
        }
    }
}
*/
