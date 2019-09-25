///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TestAppAttribute
//
//  Note:
//

using System;

namespace Microsoft.Singularity.UnitTest
{
    // This annotation on an assembly indicates that the assembly should be treated
    // as a stand-alone test application, and executed as part of the indicated
    // group of tests.
    //
    [AttributeUsage(AttributeTargets.Assembly, AllowMultiple = true)]
    public sealed class TestAppAttribute : Attribute
    {
        public string TestGroup;
    }
}
