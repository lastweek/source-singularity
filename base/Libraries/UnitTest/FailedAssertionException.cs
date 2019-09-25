///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   FailedAssertionException.cs
//
//  Note:
//

namespace Microsoft.Singularity.UnitTest
{
    public sealed class FailedAssertionException : System.Exception
    {
        public FailedAssertionException(string userMessage)
            : base(userMessage)
        {
        }

        public FailedAssertionException(string userMessage,
                                        string /*!*/ conditionMessage)
            : base(string.Format("{0} {1}", userMessage, conditionMessage))
        {
        }
    }
}
