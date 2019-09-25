// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    using Microsoft.Bartok.Runtime;

    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using System;
    //  This value type is used for making Type.GetTypeFromHandle() type safe.
    //
    //  SECURITY : m_ptr cannot be set to anything other than null by untrusted
    //  code.
    //
    //  This corresponds to EE TypeHandle.
    //| <include path='docs/doc[@for="RuntimeTypeHandle"]/*' />
    public struct RuntimeTypeHandle
    {
        internal RuntimeType m_ptr;

        // The CLR appears to do this in native code.  We add this constructor
        // so that we can do it from C#.  Note that by using "IntPtr" type we
        // are using the assumption that the GC will not move RuntimeType
        // objects.
        [NoHeapAllocation]
        internal RuntimeTypeHandle(RuntimeType type) {
            this.m_ptr = type;
        }

/*
        //| <include path='docs/doc[@for="RuntimeTypeHandle.Value"]/*' />
        public IntPtr Value {
            // BUGBUG: What if the handle is a field in a class?  --Bjarne
            [NoBarriers]
            [NoHeapAllocation]
            get {
                return m_ptr;
            }
        }
*/
    }
}
