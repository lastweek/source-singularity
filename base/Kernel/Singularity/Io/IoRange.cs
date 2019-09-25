///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoRange.cs
//

using System;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public abstract class IoRange
    {
#if SINGULARITY_KERNEL
        public abstract uint RangeBase {
            get;
        }

        public abstract uint RangeLength {
            get;
        }
#endif
    }
}
