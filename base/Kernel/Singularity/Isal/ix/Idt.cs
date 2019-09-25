//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//


using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Isal.IX
{
    // A lgdt pointer to the entries
    //
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from c++")]
    public struct Idtp
    {
#if ISA_IX64
        [AccessedByRuntime("referenced from c++")]
        internal ushort   pad1;
        [AccessedByRuntime("referenced from c++")]
        internal ushort   pad2;
#endif
        [AccessedByRuntime("referenced from c++")]
        public ushort     pad;
        [AccessedByRuntime("referenced from c++")]
        public ushort     limit;
#if ISA_IX86
        [AccessedByRuntime("referenced from c++")]
        public uint       addr;
#else
        [AccessedByRuntime("referenced from c++")]
        public ulong      addr;
#endif
    };

    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from c++")]
    public struct Idte
    {
        // An entry in the Interrupt Descriptor Table
        [AccessedByRuntime("referenced from c++")] 
        public ushort     offset_0_15;
        [AccessedByRuntime("referenced from c++")] 
        public ushort     selector;
        [AccessedByRuntime("referenced from c++")] 
        public byte       flags;
        [AccessedByRuntime("referenced from c++")] 
        public byte       access;
        [AccessedByRuntime("referenced from c++")] 
        public ushort     offset_16_31;
#if ISA_IX64
        [AccessedByRuntime("referenced from c++")] 
        internal uint     offset_32_63;
        [AccessedByRuntime("referenced from c++")] 
        internal uint     reserved;
#endif

        ///////////////////////////////////////// Interrupt Descriptor Tables.
        //
        [AccessedByRuntime("referenced from c++")]
        public const uint PRESENT      = 0x80;

        [AccessedByRuntime("referenced from c++")] 
        public const uint DPL_RING3    = 0x60;
        [AccessedByRuntime("referenced from c++")]
        public const uint DPL_RING2    = 0x40;
        [AccessedByRuntime("referenced from c++")]
        public const uint DPL_RING1    = 0x20;
        [AccessedByRuntime("referenced from c++")] 
        public const uint DPL_RING0    = 0x00;

        [AccessedByRuntime("referenced from c++")]
        public const uint TASK_GATE    = 0x05;
        [AccessedByRuntime("referenced from c++")]
        public const uint CALL_GATE    = 0x0c;
        [AccessedByRuntime("referenced from c++")] 
        public const uint INT_GATE     = 0x0e;
        [AccessedByRuntime("referenced from c++")]
        public const uint TRAP_GATE    = 0x0f;
    }

}

