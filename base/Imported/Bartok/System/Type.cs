// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Type is the root of all reflection and the Object that represents
//  a type inside the system.  Type is an abstract base class that allows multiple
//      implementations.  The system will always provide the subclass __RuntimeType.
//      In Reflection all of the __RuntimeXXX classes are created only once per object
//      in the system and support == comparisons.
//
namespace System
{

    using System;
    using System.Reflection;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="Type"]/*' />
    [CCtorIsRunDuringStartup]
    [RequiredByBartok]
    public abstract partial class Type
    {
    }
}
