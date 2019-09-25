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
    [AttributeUsage(AttributeTargets.Method, AllowMultiple = false)]
    public sealed class TestAttribute : Attribute
    {
        public TestAttribute(string name) {
        }
    }

}
