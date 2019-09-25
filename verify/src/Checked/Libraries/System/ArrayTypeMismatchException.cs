// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: ArrayTypeMismatchException
//
// Purpose: The arrays are of different primitive types.
//
//=============================================================================  

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    // The ArrayMismatchException is thrown when an attempt to store
    // an object of the wrong type within an array occurs.
    //
    //| <include path='docs/doc[@for="ArrayTypeMismatchException"]/*' />
    public class ArrayTypeMismatchException : SystemException {

        [RequiredByBartok]
        public ArrayTypeMismatchException() : base() {
            throw null;
        }

        // Creates a new ArrayMismatchException with its message string set to
        // message, its HRESULT set to COR_E_ARRAYTYPEMISMATCH,
        // and its ExceptionInfo reference set to null.
        //
        //| <include path='docs/doc[@for="ArrayTypeMismatchException.ArrayTypeMismatchException1"]/*' />
        public ArrayTypeMismatchException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="ArrayTypeMismatchException.ArrayTypeMismatchException2"]/*' />
        public ArrayTypeMismatchException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
