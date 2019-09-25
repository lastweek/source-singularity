// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
// Simple PE Loader for Singularity
//

namespace Microsoft.Singularity.Loader
{
    using System;

    internal class BadImageFormatException : SystemException
    {
        internal BadImageFormatException(String reason)
            : base(reason)
        {
        }
    }
}
