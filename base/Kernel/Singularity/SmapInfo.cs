///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   SmapInfo.sg
//
//  Note:
//       Section 14 System Address Map Interfaces,
//       ACPI revision 3.0, September 2, 2004

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity
{
    [StructLayout(LayoutKind.Sequential)]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from c++")]
    public struct SMAPINFO
    {
        [AccessedByRuntime("referenced from c++")]
        public const uint AddressTypeFree     = 1;
        [AccessedByRuntime("referenced from c++")]
        public const uint AddressTypeReserved = 2;
        [AccessedByRuntime("referenced from c++")]
        public const uint AddressTypeACPI     = 3;
        [AccessedByRuntime("referenced from c++")]
        public const uint AddressTypeNVS      = 4;
        [AccessedByRuntime("referenced from c++")]
        public const uint AddressTypeUnusable = 5;
        [AccessedByRuntime("referenced from c++")]
        public const uint AddressTypeKernelNonGc = 6;
        [AccessedByRuntime("referenced from c++")]
        public const uint AddressTypeKernelStack = 7;
        [AccessedByRuntime("referenced from c++")]
        public const uint AddressTypeMax      = 7;

        [AccessedByRuntime("referenced from c++")]
        public const uint ExtendedAttributeRangeEnabled = 1;
        [AccessedByRuntime("referenced from c++")]
        public const uint ExtendedAttributeRangeNV      = 2;

        [AccessedByRuntime("referenced from c++")]
        public ulong      addr;
        [AccessedByRuntime("referenced from c++")]
        public ulong      size;
        [AccessedByRuntime("referenced from c++")]
        public uint       type;
        [AccessedByRuntime("referenced from c++")]
        public uint       extendedAttributes;

        public enum AddressType : uint
        {
            Free     = AddressTypeFree,
            Reserved = AddressTypeReserved,
            ACPI     = AddressTypeACPI,
            NVS      = AddressTypeNVS,
            Unusable = AddressTypeUnusable,
            KernelNonGc = AddressTypeKernelNonGc,
            KernelStack = AddressTypeKernelStack,
            Max      = AddressTypeMax
        }
    }
}
