// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    using System;
    using System.Reflection;
    using System.Runtime.CompilerServices;

    //  This value type is used for making classlib type safe.
    //
    //  SECURITY : m_ptr cannot be set to anything other than null by untrusted
    //  code.
    //
    //  This corresponds to EE MethodDesc.
    //| <include path='docs/doc[@for="RuntimeMethodHandle"]/*' />
    public struct RuntimeMethodHandle
    {
        private IntPtr m_ptr;

        //| <include path='docs/doc[@for="RuntimeMethodHandle.Value"]/*' />
        public IntPtr Value {
            get {
                return m_ptr;
            }
        }
    }
}
