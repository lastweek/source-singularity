////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EVectors.cs
//
//  Note:
//

namespace Microsoft.Singularity.Isal.IX
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from C++", AllFields = true)]
    internal struct EVectors
    {
        // Interrupt Vector Assignments
        // 0..31 Intel defined
        internal const uint DivideError                 = 0;
        internal const uint SingleStep                  = 1;
        internal const uint Nmi                         = 2;
        internal const uint Breakpoint                  = 3;
        internal const uint OverflowException           = 4;
        internal const uint BoundRangeException         = 5;
        internal const uint IllegalInstruction          = 6;
        internal const uint CoprocessorNotAvailable     = 7;
        internal const uint DoubleFault                 = 8;
        internal const uint CoprocessorSegmentOverrun   = 9;
        internal const uint InvalidTss                  = 10;
        internal const uint SegmentNotPresent           = 11;
        internal const uint StackSegmentFault           = 12;
        internal const uint GeneralProtectionFault      = 13;
        internal const uint PageFault                   = 14;
        internal const uint IntelReserved               = 14;
        internal const uint FpuMathFault                = 16;
        internal const uint AlignmentCheck              = 17;
        internal const uint MachineCheck                = 18;
        internal const uint SseMathFault                = 19;

        // Reserved, but used by Singularity
        internal const uint FirstChanceException        = 29;
        internal const uint SecondChanceException       = 30;
        internal const uint DebuggerBreakRequest        = 31;

        // 32..255 User defined
        internal const uint BaseUserException           = 32;

        // Mapped for I/O interrupts.
        internal const uint IoBaseVector                = 0x60;
        internal const uint IoLastVector                = 0x9f;

        //
        internal const uint HaltApProcessors            = 36;
        internal const uint GCSynchronization           = 37;

        internal const uint SpuriousInterrupt           = 0xdf;
    }
}
