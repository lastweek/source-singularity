// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: StackOverflowException
//
// Purpose: The exception class for stack overflow.
//
//=============================================================================  

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="StackOverflowException"]/*' />
    [AccessedByRuntime("referenced from halasm.asm/brtasm.asm")]
    public sealed class StackOverflowException : SystemException {
        //| <include path='docs/doc[@for="StackOverflowException.StackOverflowException"]/*' />
        [AccessedByRuntime("referenced from halasm.asm")]
        public StackOverflowException()
            : base("Arg_StackOverflowException") {
        }

        //| <include path='docs/doc[@for="StackOverflowException.StackOverflowException1"]/*' />
        public StackOverflowException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="StackOverflowException.StackOverflowException2"]/*' />
        public StackOverflowException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
