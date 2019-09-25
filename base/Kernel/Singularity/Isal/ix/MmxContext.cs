////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MmxContext.cs
//
//  Note:
//

namespace Microsoft.Singularity.Isal.IX
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential)]
    [StructAlign(16)]
    [AccessedByRuntime("referenced from c++")]
    internal struct uint128
    {
        //[AccessedByRuntime("")]
        public ulong    lo;
        //[AccessedByRuntime("")]
        public ulong    hi;
    }

    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential)]
    [StructAlign(16)]
    [AccessedByRuntime("referenced from c++", AllFields = true)]
    internal struct MmxContext
    {
        public ushort   fcw;
        public ushort   fsw;
        public ushort   ftw;
        public ushort   fop;

#if ISA_IX64
        public ulong    ip;
        public ulong    dp;
#else
        public uint     ip;
        public ushort   cs;
        public ushort   reserved0;

        public uint     dp;
        public ushort   ds;
        public ushort   reserved1;
#endif

        public uint     mxcsr;
        public uint     mxcsrmask;

        public uint128  st0;
        public uint128  st1;
        public uint128  st2;
        public uint128  st3;
        public uint128  st4;
        public uint128  st5;
        public uint128  st6;
        public uint128  st7;

        public uint128  xmm0;
        public uint128  xmm1;
        public uint128  xmm2;
        public uint128  xmm3;
        public uint128  xmm4;
        public uint128  xmm5;
        public uint128  xmm6;
        public uint128  xmm7;

#if ISA_IX64
        public uint128  xmm8;
        public uint128  xmm9;
        public uint128  xmm10;
        public uint128  xmm11;
        public uint128  xmm12;
        public uint128  xmm13;
        public uint128  xmm14;
        public uint128  xmm15;
#else
        public uint128  reserved2;
        public uint128  reserved3;
        public uint128  reserved4;
        public uint128  reserved5;
        public uint128  reserved6;
        public uint128  reserved7;
        public uint128  reserved8;
        public uint128  reserved9;
#endif

        public uint128  reservedA;
        public uint128  reservedB;
        public uint128  reservedC;
        public uint128  reservedD;
        public uint128  reservedE;
        public uint128  reservedF;
    }
}

