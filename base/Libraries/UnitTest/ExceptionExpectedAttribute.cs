///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

using System;

namespace Microsoft.Singularity.UnitTest
{
    // This annotation on an assembly indicates that the assembly should be treated
    // as a stand-alone test application.
    //
    [AttributeUsage(AttributeTargets.Method, AllowMultiple = true)]
    public sealed class ExceptionExpectedAttribute : Attribute
    {
        public ExceptionExpectedAttribute(System.Type exceptionType) {
        }

    }

}
