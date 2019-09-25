// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

namespace System.Security
{
    // UnverifiableCodeAttribute:
    //  Indicates that the target module contains unverifiable code.
    //| <include path='docs/doc[@for="UnverifiableCodeAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Module, AllowMultiple = true, Inherited = false )]
    sealed public class UnverifiableCodeAttribute : System.Attribute
    {
    }
}
