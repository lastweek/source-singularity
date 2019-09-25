// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*=============================================================================
**
** Class: DivideByZeroException
**
** Purpose: Exception class for bad arithmetic conditions!
**
=============================================================================*/

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    [RequiredByBartok]
    //| <include path='docs/doc[@for="DivideByZeroException"]/*' />
    public partial class DivideByZeroException : ArithmeticException {
    }
}
