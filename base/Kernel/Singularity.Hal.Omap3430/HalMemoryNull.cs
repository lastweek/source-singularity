///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

namespace Microsoft.Singularity.Hal
{
    using System;

    [CLSCompliant(false)]
    internal class HalMemoryNull : HalMemory
    {
        internal HalMemoryNull()
        {
        }

        public override ProcessorAffinity[] GetProcessorAffinity()
        {
            return null;
        }

        public override MemoryAffinity[] GetMemoryAffinity()
        {
            return null;
        }

        public override bool PerProcessorAddressSpaceDisabled()
        {
            return true;
        }
    }
}
