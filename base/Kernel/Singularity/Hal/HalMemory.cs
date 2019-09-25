///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

using System;

namespace Microsoft.Singularity.Hal
{
    [CLSCompliant(false)]
    public abstract class HalMemory
    {
        public struct ProcessorAffinity
        {
            public uint domain;
            public uint apicId;
            public uint flagIgnore;
        }

        public struct MemoryAffinity
        {
            public uint  domain;
            public ulong baseAddress;
            public ulong endAddress;
            public ulong memorySize;
            public uint  flagIgnore;
            public uint  flagHotPluggable;
            public uint  flagNonVolatile;
        }

        public abstract ProcessorAffinity[] GetProcessorAffinity();
        public abstract MemoryAffinity[] GetMemoryAffinity();
        public abstract bool PerProcessorAddressSpaceDisabled();
    }
}
