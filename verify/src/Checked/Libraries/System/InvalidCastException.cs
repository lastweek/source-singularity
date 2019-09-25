// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: InvalidCastException
//
// Purpose: Exception class for bad cast conditions!
//
//=============================================================================  

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="InvalidCastException"]/*' />
    public partial class InvalidCastException : SystemException {

        [RequiredByBartok]
        public InvalidCastException() : base() {
            throw null;
        }

        //| <include path='docs/doc[@for="InvalidCastException.InvalidCastException1"]/*' />
        public InvalidCastException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="InvalidCastException.InvalidCastException2"]/*' />
        public InvalidCastException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
