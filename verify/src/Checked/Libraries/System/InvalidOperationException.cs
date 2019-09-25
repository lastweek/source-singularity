// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: InvalidOperationException
//
// Purpose: Exception class for denoting an object was in a state that
// made calling a method illegal.
//
//=============================================================================  
namespace System
{

    using System;

    //| <include path='docs/doc[@for="InvalidOperationException"]/*' />
    public class InvalidOperationException : SystemException
    {
        //| <include path='docs/doc[@for="InvalidOperationException.InvalidOperationException"]/*' />
        public InvalidOperationException()
            : base("Arg_InvalidOperationException") {
        }

        //| <include path='docs/doc[@for="InvalidOperationException.InvalidOperationException1"]/*' />
        public InvalidOperationException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="InvalidOperationException.InvalidOperationException2"]/*' />
        public InvalidOperationException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}

