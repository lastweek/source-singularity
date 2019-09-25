// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*=============================================================================
**
** Class: InvalidCastException
**
** Purpose: Exception class for bad cast conditions!
**
=============================================================================*/

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="InvalidCastException"]/*' />
    [RequiredByBartok]
    public partial class InvalidCastException : SystemException {
        //| <include path='docs/doc[@for="InvalidCastException.InvalidCastException"]/*' />
        [RequiredByBartok]
        public InvalidCastException()
            : base("Arg_InvalidCastException") {
        }
    }
}
