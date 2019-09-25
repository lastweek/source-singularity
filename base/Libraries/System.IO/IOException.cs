// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  IOException
//
// Purpose: Exception for a generic IO error.
//
//===========================================================  

using System;

namespace System.IO
{

    //| <include file='doc\IOException.uex' path='docs/doc[@for="IOException"]/*' />
    public class IOException : SystemException
    {
        //| <include file='doc\IOException.uex' path='docs/doc[@for="IOException.IOException"]/*' />
        public IOException()
            : base("Arg_IOException") {
        }

        //| <include file='doc\IOException.uex' path='docs/doc[@for="IOException.IOException1"]/*' />
        public IOException(String message)
            : base(message) {
        }

        //| <include file='doc\IOException.uex' path='docs/doc[@for="IOException.IOException2"]/*' />
        public IOException(String message, int hresult)
            : base(message) {
        }

        //| <include file='doc\IOException.uex' path='docs/doc[@for="IOException.IOException3"]/*' />
        public IOException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
