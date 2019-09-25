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
    // This method should be invoked to cleanup after testing a class.
    //
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class ClassCleanupAttribute : Attribute
    {
    }

}

