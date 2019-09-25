// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*=============================================================================
**
** Class: ArithmeticException
**
** Purpose: Exception class for bad arithmetic conditions!
**
=============================================================================*/

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    // The ArithmeticException is thrown when overflow or underflow
    // occurs.
    //
    //| <include path='docs/doc[@for="ArithmeticException"]/*' />
    [RequiredByBartok]
    public partial class ArithmeticException : SystemException
    {
    }
}
