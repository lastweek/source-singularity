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
    // This annotation on a method indicates that the method should be invoked
    // to cleanup after running tests in the assembly.
    //
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class AssemblyCleanupAttribute : Attribute
    {
    }

}

