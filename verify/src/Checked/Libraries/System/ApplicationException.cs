// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: ApplicationException
//
// Purpose: The base class for all "less serious" exceptions that must be
//          declared or caught.
//
//=============================================================================  

namespace System
{

    // The ApplicationException is the base class for nonfatal,
    // application errors that occur.  These exceptions are generated
    // (i.e., thrown) by an application, not the Runtime. Applications that need
    // to create their own exceptions do so by extending this class.
    // ApplicationException extends but adds no new functionality to
    // RecoverableException.
    //
    //| <include path='docs/doc[@for="ApplicationException"]/*' />
    public class ApplicationException : Exception {

        // Creates a new ApplicationException with its message string set to
        // the empty string, its HRESULT set to COR_E_APPLICATION,
        // and its ExceptionInfo reference set to null.
        //| <include path='docs/doc[@for="ApplicationException.ApplicationException"]/*' />
        public ApplicationException()
            : base("Arg_ApplicationException") {
        }

        // Creates a new ApplicationException with its message string set to
        // message, its HRESULT set to COR_E_APPLICATION,
        // and its ExceptionInfo reference set to null.
        //
        //| <include path='docs/doc[@for="ApplicationException.ApplicationException1"]/*' />
        public ApplicationException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="ApplicationException.ApplicationException2"]/*' />
        public ApplicationException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
