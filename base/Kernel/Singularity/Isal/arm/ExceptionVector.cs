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
    [CLSCompliant(false)]
    public struct ExceptionVector
    {
        public const uint LowAddress    = 0x00000000;
        public const uint HighAddress   = 0xFFFF0000;

        public const uint Reset                         = 0x00;
        public const uint UndefinedInstruction          = 0x01;
        public const uint SoftwareInterrupt             = 0x02;
        public const uint PrefetchAbort                 = 0x03;
        public const uint DataAbort                     = 0x04;
        public const uint Unused                        = 0x05;
        public const uint Irq                           = 0x06;
        public const uint Fiq                           = 0x07;
    }
}
