// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: ArgumentNullException
//
// Purpose: Exception class for null arguments to a method.
//
//=============================================================================  

namespace System
{

    using System;

    // The ArgumentException is thrown when an argument
    // is null when it shouldn't be.
    //
    //| <include path='docs/doc[@for="ArgumentNullException"]/*' />
    public class ArgumentNullException : ArgumentException
    {
        private static String _nullMessage = null;

        private static String NullMessage {
            get {
                // Don't bother with synchronization here.  A duplicated string
                // is not a major problem.
                if (_nullMessage == null)
                    _nullMessage = "ArgumentNull_Generic";
                return _nullMessage;
            }
        }

        // Creates a new ArgumentNullException with its message
        // string set to a default message explaining an argument was null.
        //| <include path='docs/doc[@for="ArgumentNullException.ArgumentNullException"]/*' />
        public ArgumentNullException()
            : base(NullMessage) {
            // Use E_POINTER - COM used that for null pointers.  Description is "invalid pointer"
        }

        //| <include path='docs/doc[@for="ArgumentNullException.ArgumentNullException1"]/*' />
        public ArgumentNullException(String paramName)
            : base(NullMessage, paramName) {
        }

        //| <include path='docs/doc[@for="ArgumentNullException.ArgumentNullException2"]/*' />
        public ArgumentNullException(String paramName, String message)
            : base(message, paramName) {

        }
    }
}
