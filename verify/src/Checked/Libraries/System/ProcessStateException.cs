// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

namespace System
{
    public class ProcessStateException : SystemException
    {
        public ProcessStateException() : base("Arg_ProcessStateException")
        {
        }

        public ProcessStateException(String message) : base(message)
        {
        }

        public ProcessStateException(String message, Exception innerException)
            : base(message, innerException)
        {
        }
    }
}
