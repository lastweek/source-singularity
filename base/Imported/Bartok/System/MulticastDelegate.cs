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

    //| <include path='docs/doc[@for="MulticastDelegate"]/*' />
    [RequiredByBartok]
    public abstract partial class MulticastDelegate : Delegate
    {
        // This is a pointer to a delegate that is logically the
        //  delegate before this one.
        [RequiredByBartok]
        private MulticastDelegate _prev;
    }
}
