// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: OverflowException
//
// Purpose: Exception class for Arithmetic Overflows.
//
//=============================================================================  

namespace System
{

    using System;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="OverflowException"]/*' />
    [AccessedByRuntime("referenced from halasm.asm")]
    public partial class OverflowException : ArithmeticException {
        //| <include path='docs/doc[@for="OverflowException.OverflowException"]/*' />
        [AccessedByRuntime("referenced from halasm.asm")]
        public OverflowException()
            : base("Arg_OverflowException") {
        }

        //| <include path='docs/doc[@for="OverflowException.OverflowException1"]/*' />
        public OverflowException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="OverflowException.OverflowException2"]/*' />
        public OverflowException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
