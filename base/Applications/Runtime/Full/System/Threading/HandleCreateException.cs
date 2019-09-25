// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

namespace System.Threading
{
    public class HandleCreateException : SystemException
    {
        public HandleCreateException() : base("Arg_HandleCreateException")
        {
        }

        public HandleCreateException(String message) : base(message)
        {
        }

        public HandleCreateException(String message, Exception innerException)
            : base(message, innerException)
        {
        }
    }
}
