// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  EndOfStreamException
//
// Purpose: Exception to be thrown when reading past end-of-file.
//
//===========================================================  

using System;

namespace System.IO
{
    //| <include file='doc\EndOfStreamException.uex' path='docs/doc[@for="EndOfStreamException"]/*' />
    public class EndOfStreamException : IOException
    {
        //| <include file='doc\EndOfStreamException.uex' path='docs/doc[@for="EndOfStreamException.EndOfStreamException"]/*' />
        public EndOfStreamException()
            : base("Arg_EndOfStreamException") {
        }

        //| <include file='doc\EndOfStreamException.uex' path='docs/doc[@for="EndOfStreamException.EndOfStreamException1"]/*' />
        public EndOfStreamException(String message)
            : base(message) {
        }

        //| <include file='doc\EndOfStreamException.uex' path='docs/doc[@for="EndOfStreamException.EndOfStreamException2"]/*' />
        public EndOfStreamException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
