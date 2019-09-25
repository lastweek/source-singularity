// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

namespace System
{
    public class ProcessCreateException : SystemException
    {
        public ProcessCreateException() : base("Arg_ProcessCreateException")
        {
        }

        public ProcessCreateException(String message) : base(message)
        {
        }

        public ProcessCreateException(String message, Exception innerException)
            : base(message, innerException)
        {
        }
    }
}
