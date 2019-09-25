// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: NotSupportedException
//
// Purpose: For methods that should be implemented on subclasses.
//
//=============================================================================  

namespace System
{

    using System;

    //| <include path='docs/doc[@for="NotSupportedException"]/*' />
    public class NotSupportedException : SystemException
    {
        //| <include path='docs/doc[@for="NotSupportedException.NotSupportedException"]/*' />
        public NotSupportedException()
            : base("Arg_NotSupportedException") {
        }

        //| <include path='docs/doc[@for="NotSupportedException.NotSupportedException1"]/*' />
        public NotSupportedException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="NotSupportedException.NotSupportedException2"]/*' />
        public NotSupportedException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
