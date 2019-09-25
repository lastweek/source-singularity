// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: TypeInitializationException
//
// Purpose: The exception class to wrap exceptions thrown by
//          a type's class initializer (.cctor).  This is sufficiently
//          distinct from a TypeLoadException, which means we couldn't
//          find the type.
//
//=============================================================================  
using System;

namespace System
{
    //| <include path='docs/doc[@for="TypeInitializationException"]/*' />
    public sealed class TypeInitializationException : SystemException {
        private String _typeName;

        // This exception is not creatable without specifying the
        //  inner exception.
        private TypeInitializationException()
            : base("TypeInitialization_Default") {
        }

        // This is called from within the runtime.  I believe this is necessary
        // for Interop only, though it's not particularly useful.
        private TypeInitializationException(String message) : base(message) {
        }

        //| <include path='docs/doc[@for="TypeInitializationException.TypeInitializationException"]/*' />
        public TypeInitializationException(String fullTypeName, Exception innerException)
            : base(String.Format("An exception occurred while initializing the type '{0}'.", fullTypeName), innerException) {
            _typeName = fullTypeName;
        }

        //| <include path='docs/doc[@for="TypeInitializationException.TypeName"]/*' />
        public String TypeName
        {
            get {
                if (_typeName == null) {
                    return String.Empty;
                }
                return _typeName;
            }
        }
    }
}
