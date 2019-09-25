// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  FormatException
//
// Purpose: Exception to designate an illegal argument to Format.
//
//===========================================================  
namespace System
{

    using System;
    //| <include path='docs/doc[@for="FormatException"]/*' />
    public class FormatException : SystemException {
        //| <include path='docs/doc[@for="FormatException.FormatException"]/*' />
        public FormatException()
            : base("Arg_FormatException") {
        }

        //| <include path='docs/doc[@for="FormatException.FormatException1"]/*' />
        public FormatException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="FormatException.FormatException2"]/*' />
        public FormatException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
