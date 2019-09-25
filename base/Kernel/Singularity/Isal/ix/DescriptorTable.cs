/////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// Segment table definition. Currently only used for intel architectures.

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Isal.IX
{
    [AccessedByRuntime("referenced in c++")]
    [CLSCompliant(false)]
    public struct DescriptorTable
    {
#if ISA_IX

        [AccessedByRuntime("referenced in c++")]
        public struct Gdt
        {
            [AccessedByRuntime("referenced in c++")]
            public Gdte     nul;    // Null segment
            [AccessedByRuntime("referenced in c++")]
            private Gdte    pv;     // 16-bit video, used in boot loader only
            // 0x10
            [AccessedByRuntime("referenced in c++")]
            private Gdte    rc;     // 16-bit code, used to align with RM code in boot loader
            [AccessedByRuntime("referenced in c++")]
            private Gdte    rd;     // 16-bit data, used to align with RM data in boot loader
            // 0x20
            [AccessedByRuntime("referenced in c++")]
            private Gdte    pc;     // 32-bit code
            [AccessedByRuntime("referenced in c++")]
            private Gdte    pd;     // 32-bit data
            // 0x30
            [AccessedByRuntime("referenced in c++")]
            private Gdte    lc;     // 64-bit code
            [AccessedByRuntime("referenced in c++")]
            private Gdte    ld;     // 64-bit data
            // 0x40
            [AccessedByRuntime("referenced in c++")]
            public Gdte     uc;     // User mode code - used in paging mode only
            [AccessedByRuntime("referenced in c++")]
            public Gdte     ud;     // User mode data - used in paging mode only
            // 0x50
            [AccessedByRuntime("referenced in c++")]
            public Gdte     pp;     // Kernel mode per-processor data
            [AccessedByRuntime("referenced in c++")]
            public Gdte     nn;     // Unused
            // 0x60
#if ISA_IX86
            [AccessedByRuntime("referenced in c++")]
            public Gdte        tss;        // Currently executing task segment
#elif ISA_IX64
            [AccessedByRuntime("referenced in c++")]
            public Gdte64      tss;        // Long mode 64-bit TSS
#endif
        }

        [AccessedByRuntime("referenced in c++")]
        public Gdt              gdt;

        [AccessedByRuntime("referenced in c++")]
        public Gdtp             gdtPtr;

#endif // ISA_IX
    }
};



