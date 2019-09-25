// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: ArithmeticException
//
// Purpose: Exception class for bad arithmetic conditions!
//
//=============================================================================  

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    // The ArithmeticException is thrown when overflow or underflow
    // occurs.
    //
    //| <include path='docs/doc[@for="ArithmeticException"]/*' />
    public partial class ArithmeticException : SystemException
    {
        // Creates a new ArithmeticException with its message string set to
        // the empty string, its HRESULT set to COR_E_ARITHMETIC,
        // and its ExceptionInfo reference set to null.
        //| <include path='docs/doc[@for="ArithmeticException.ArithmeticException"]/*' />
        public ArithmeticException()
            : base("Arg_ArithmeticException") {
        }

        // Creates a new ArithmeticException with its message string set to
        // message, its HRESULT set to COR_E_ARITHMETIC,
        // and its ExceptionInfo reference set to null.
        //
        //| <include path='docs/doc[@for="ArithmeticException.ArithmeticException1"]/*' />
        public ArithmeticException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="ArithmeticException.ArithmeticException2"]/*' />
        public ArithmeticException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
