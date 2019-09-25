///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:    BitmapFileHeader.cs
//
//  Note:
//
#define BUG

using System;
using System.Runtime.InteropServices;

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

namespace Microsoft.Singularity.Io
{
#if BUG
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit)]
    public pointerfree struct BITMAPFILEHEADER {
        [FieldOffset( 0)] public ushort bfType;
        [FieldOffset( 2)] public uint bfSize;
        [FieldOffset( 6)] public ushort bfReserved1;
        [FieldOffset( 8)] public ushort bfReserved2;
        [FieldOffset(10)] public int bfOffBits;
#else
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential, Pack=2)]
    public pointerfree struct BITMAPFILEHEADER {
        public ushort bfType;
        public uint bfSize;
        public ushort bfReserved1;
        public ushort bfReserved2;
        public int bfOffBits;
#endif

        public static BITMAPFILEHEADER Read(byte[]! in ExHeap buffer,
                                            int offset, out int used)
        {
            if (buffer == null || offset < 0 ||
                offset + sizeof(BITMAPFILEHEADER) > buffer.Length) {
                unchecked {
                    Tracing.Log(Tracing.Error,
                                "BITMAPFILEHEADER Read(offset={0}, length={1})",
                                (UIntPtr)(uint)offset,
                                (UIntPtr)(uint)buffer.Length);
                }
                throw new OverflowException("Read source invalid.");
            }

            used = offset + /*sizeof(BITMAPFILEHEADER)*/ 14;

            ref BITMAPFILEHEADER bmfh = ref buffer[offset];
            return bmfh;
        }
    }
} // namespace Microsoft.Singularity.Io
