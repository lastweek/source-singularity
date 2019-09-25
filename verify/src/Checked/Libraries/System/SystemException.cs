// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    using System;
    //| <include path='docs/doc[@for="SystemException"]/*' />
    public class SystemException : Exception
    {
        //| <include path='docs/doc[@for="SystemException.SystemException"]/*' />
        public SystemException()
            : base("Arg_SystemException") {
        }

        //| <include path='docs/doc[@for="SystemException.SystemException1"]/*' />
        public SystemException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="SystemException.SystemException2"]/*' />
        public SystemException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
