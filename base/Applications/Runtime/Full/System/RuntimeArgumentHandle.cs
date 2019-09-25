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
        internal IntPtr Pointer {
            [NoHeapAllocation]
            get { return (IntPtr) (UIntPtr) m_ptr; }
        }
    }
}
