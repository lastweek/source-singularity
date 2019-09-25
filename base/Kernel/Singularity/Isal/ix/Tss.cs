////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Tss.cs
//
//  Note:
//

namespace Microsoft.Singularity.Isal.IX
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    // Task State Segment
    [AccessedByRuntime("referenced from c++")]
    [StructLayout(LayoutKind.Sequential, Pack=4)]
    [CLSCompliant(false)]
    internal struct TSS
    {
        [AccessedByRuntime("referenced in c++")]
        internal ushort     previous_tss;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     pad0;

        [AccessedByRuntime("referenced in c++")] 
        internal uint       esp0;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     ss0;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     pad1;

        [AccessedByRuntime("referenced in c++")] 
        internal uint       esp1;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     ss1;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     pad2;

        [AccessedByRuntime("referenced in c++")] 
        internal uint       esp2;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     ss2;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     pad3;

        [AccessedByRuntime("referenced in c++")] 
        internal uint       cr3;
        [AccessedByRuntime("referenced in c++")] 
        internal uint       eip;
        [AccessedByRuntime("referenced in c++")] 
        internal uint       eflags;

        [AccessedByRuntime("referenced in c++")] 
        internal uint       eax;
        [AccessedByRuntime("referenced in c++")] 
        internal uint       ecx;
        [AccessedByRuntime("referenced in c++")] 
        internal uint       edx;
        [AccessedByRuntime("referenced in c++")] 
        internal uint       ebx;
        [AccessedByRuntime("referenced in c++")] 
        internal uint       esp;
        [AccessedByRuntime("referenced in c++")] 
        internal uint       ebp;
        [AccessedByRuntime("referenced in c++")] 
        internal uint       esi;
        [AccessedByRuntime("referenced in c++")] 
        internal uint       edi;

        [AccessedByRuntime("referenced in c++")] 
        internal ushort     es;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     pades;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     cs;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     padcs;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     ss;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     padss;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     ds;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     padds;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     fs;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     padfs;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     gs;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     padgs;

        [AccessedByRuntime("referenced in c++")] 
        internal ushort     ldt;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     padldt;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     trap_bit;
        [AccessedByRuntime("referenced in c++")] 
        internal ushort     io_bitmap_offset;
    }
}
