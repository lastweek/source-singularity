// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  DirectoryNotFoundException
//
// Purpose: Exception for accessing a path that doesn't exist.
//
//===========================================================  
using System;

namespace System.IO
{
    //
    // Thrown when trying to access a file that doesn't exist on disk.
    // Note this is thrown for 2 HRESULTS: The Win32 errorcode-as-HRESULT
    // ERROR_PATH_NOT_FOUND (0x80070003) and STG_E_PATHNOTFOUND (0x80030003).
    // 
    //| <include file='doc\DirectoryNotFoundException.uex' path='docs/doc[@for="DirectoryNotFoundException"]/*' />
    public class DirectoryNotFoundException : IOException {
        //| <include file='doc\DirectoryNotFoundException.uex' path='docs/doc[@for="DirectoryNotFoundException.DirectoryNotFoundException"]/*' />
        public DirectoryNotFoundException()
            : base("Arg_DirectoryNotFoundException") {
        }

        //| <include file='doc\DirectoryNotFoundException.uex' path='docs/doc[@for="DirectoryNotFoundException.DirectoryNotFoundException1"]/*' />
        public DirectoryNotFoundException(String message)
            : base(message) {
        }

        //| <include file='doc\DirectoryNotFoundException.uex' path='docs/doc[@for="DirectoryNotFoundException.DirectoryNotFoundException2"]/*' />
        public DirectoryNotFoundException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
