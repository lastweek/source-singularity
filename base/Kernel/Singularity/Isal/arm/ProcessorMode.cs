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
    [AccessedByRuntime("referenced in c++", AllFields = true)]
    struct ProcessorMode
    {
        public const int User = 0x10;
        public const int Fiq = 0x11;
        public const int Irq = 0x12;
        public const int Supervisor = 0x13;
        public const int Abort = 0x17;
        public const int Undefined = 0x1b;
        public const int System = 0x1f;

        public const int Mask = 0x1f;
    }
}
