// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: ThreadStateException
//
// Purpose: An exception class to indicate that the Thread class is in an
//          invalid state for the method.
//
//=============================================================================  

namespace System.Threading
{
    using System;

    //| <include path='docs/doc[@for="ThreadStateException"]/*' />
    public class ThreadStateException : SystemException {
        //| <include path='docs/doc[@for="ThreadStateException.ThreadStateException"]/*' />
        public ThreadStateException()
            : base("Arg_ThreadStateException") {
        }

        //| <include path='docs/doc[@for="ThreadStateException.ThreadStateException1"]/*' />
        public ThreadStateException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="ThreadStateException.ThreadStateException2"]/*' />
        public ThreadStateException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
