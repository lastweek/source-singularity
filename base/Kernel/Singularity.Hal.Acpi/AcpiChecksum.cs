///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   AcpiChecksum.cs
//
//  Note:
//    Based on ACPI 3.0 Spec.

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using Microsoft.Singularity.Io;

    internal class AcpiChecksum
    {
        public static byte Compute(IoMemory region)
        {
            return Compute(region, 0, (uint) region.Length);
        }

        public static byte Compute(IoMemory region, uint offset, uint length)
        {
            byte sum  = 0;
            uint stop = offset + length;

            for (uint i = offset; i < stop; i++) {
                sum += region.Read8((int) i);
            }
            return sum;
        }
    }
}
