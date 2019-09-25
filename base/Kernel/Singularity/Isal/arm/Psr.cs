//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// This file defines an architecture-neutral encapsulation of the state which is saved
// during a thread context switch.

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Isal.Arm
{
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced in c++")]
    public struct Psr
    {
        [AccessedByRuntime("referenced in c++")]
        public const uint Negative              = 0x80000000;
        [AccessedByRuntime("referenced in c++")]
        public const uint Zero                  = 0x40000000;
        [AccessedByRuntime("referenced in c++")]
        public const uint Carry                 = 0x20000000;
        [AccessedByRuntime("referenced in c++")]
        public const uint Overflow              = 0x10000000;

        [AccessedByRuntime("referenced in c++")]
        public const uint DspOverflow           = 0x08000000;

        [AccessedByRuntime("referenced in c++")]
        public const uint Jazelle               = 0x01000000;
        [AccessedByRuntime("referenced in c++")]
        public const uint Thumb                 = 0x00000020;

        [AccessedByRuntime("referenced in c++")]
        public const uint GreaterThanOrEqualMask = 0x000F0000;
        [AccessedByRuntime("referenced in c++")]
        public const int GreaterThanOrEqualShift = 16;

        [AccessedByRuntime("referenced from C++")]
        public const uint GE3                   = 0x00080000;   // Greater than or equal [3].
        [AccessedByRuntime("referenced from C++")]
        public const uint GE2                   = 0x00040000;   // Greater than or equal [2].
        [AccessedByRuntime("referenced from C++")]
        public const uint GE1                   = 0x00020000;   // Greater than or equal [1].
        [AccessedByRuntime("referenced from C++")]
        public const uint GE0                   = 0x00010000;   // Greater than or equal [0].

        [AccessedByRuntime("referenced in c++")]
        public const uint BigEndian             = 0x00000200;

        [AccessedByRuntime("referenced in c++")]
        public const uint DisableDataAbort      = 0x00000100;
        [AccessedByRuntime("referenced in c++")]
        public const uint DisableIrq            = 0x00000080;
        [AccessedByRuntime("referenced in c++")]
        public const uint DisableFiq            = 0x00000040;

        [AccessedByRuntime("referenced from C++")]
        public const uint Reserve               = 0x06f0fc00;   // For future architectures.

        [AccessedByRuntime("referenced in c++")]
        public const uint ModeMask              = 0x0000001F;
    }
}
