// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    using System;
    using System.Runtime.CompilerServices;
    //  This value type is used for constructing System.ArgIterator.
    //
    //  SECURITY : m_ptr cannot be set to anything other than null by untrusted
    //  code.
    //
    //  This corresponds to EE VARARGS cookie.

    //| <include path='docs/doc[@for="RuntimeArgumentHandle"]/*' />
    public unsafe partial struct RuntimeArgumentHandle {
        // Bartok will override type of m_ptr to be VarargList&
        // [TracedPointer(VarargList)].
         private VarargList* m_ptr;

        [RequiredByBartok]
        [NoHeapAllocation]
        // Bartok will override type of arguments to be VarargList&
        // [TracedPointer(VarargList)].
        internal static RuntimeArgumentHandle Arglist
        (VarargList* arguments) {
            RuntimeArgumentHandle h;
            h.m_ptr = arguments;
            return h;
        }
    }
}
