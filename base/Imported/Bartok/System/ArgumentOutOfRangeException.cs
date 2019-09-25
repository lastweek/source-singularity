// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*=============================================================================
**
** Class: ArgumentOutOfRangeException
**
** Purpose: Exception class for method arguments outside of the legal range.
**
=============================================================================*/

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    // The ArgumentOutOfRangeException is thrown when an argument
    // is outside the legal range for that argument.  This may often be caused
    // by
    //
    //| <include path='docs/doc[@for="ArgumentOutOfRangeException"]/*' />
    [RequiredByBartok]
    public partial class ArgumentOutOfRangeException : ArgumentException {
    }
}
