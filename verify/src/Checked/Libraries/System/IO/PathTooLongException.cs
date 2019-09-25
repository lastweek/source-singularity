// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  PathTooLongException
//
// Purpose: Exception for paths and/or filenames that are
// too long.
//
//===========================================================  

using System;

namespace System.IO
{

    //| <include file='doc\PathTooLongException.uex' path='docs/doc[@for="PathTooLongException"]/*' />
    public class PathTooLongException : IOException
    {
        //| <include file='doc\PathTooLongException.uex' path='docs/doc[@for="PathTooLongException.PathTooLongException"]/*' />
        public PathTooLongException()
            : base("IO.PathTooLong") {
        }

        //| <include file='doc\PathTooLongException.uex' path='docs/doc[@for="PathTooLongException.PathTooLongException1"]/*' />
        public PathTooLongException(String message)
            : base(message) {
        }

        //| <include file='doc\PathTooLongException.uex' path='docs/doc[@for="PathTooLongException.PathTooLongException2"]/*' />
        public PathTooLongException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
