// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    public class NotImplementedException : SystemException {
        public NotImplementedException()
            : base("Not implemented") {
        }

        public NotImplementedException(String message)
            : base(message) {
        }

        public NotImplementedException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
