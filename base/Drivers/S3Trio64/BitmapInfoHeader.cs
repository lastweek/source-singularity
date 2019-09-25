///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   BitmapInfoHeader.cs
//
//  Note:
//

using System;
using System.Runtime.InteropServices;

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Explicit)]
    public pointerfree struct BITMAPINFOHEADER {
        [FieldOffset( 0)] public uint     biSize;
        [FieldOffset( 4)] public int      biWidth;
        [FieldOffset( 8)] public int      biHeight;
        [FieldOffset(12)] public ushort   biPlanes;
        [FieldOffset(14)] public ushort   biBitCount;
        [FieldOffset(16)] public uint     biCompression;
        [FieldOffset(20)] public uint     biSizeImage;
        [FieldOffset(24)] public int      biXPelsPerMeter;
        [FieldOffset(28)] public int      biYPelsPerMeter;
        [FieldOffset(30)] public uint     biClrUsed;
        [FieldOffset(32)] public uint     biClrImportant;

        public static BITMAPINFOHEADER Read(byte[]! in ExHeap buffer,
                                            int offset, out int used)
        {
            if (buffer == null || offset < 0 ||
                offset + sizeof(BITMAPINFOHEADER) > buffer.Length) {
                unchecked {
                    Tracing.Log(Tracing.Error,
                                "BITMAPINFOHEADER Read(offset={0}, length={1})",
                                (UIntPtr)(uint)offset,
                                (UIntPtr)(uint)buffer.Length);
                }
                throw new OverflowException("Read source invalid.");
            }

            used = offset + sizeof(BITMAPINFOHEADER);

            ref BITMAPINFOHEADER bmih = ref buffer[offset];
            return bmih;
        }

        public RGB[] ReadPalette(byte[]! in ExHeap buffer, int offset, out int used)
        {
            if (biClrUsed == 0 && biBitCount >= 24) {
                used = offset;
                return null;
            }

            int count = (biClrUsed != 0) ? (int)biClrUsed : (1 << biBitCount);

            if (buffer == null || offset < 0 ||
                offset + count * sizeof(uint) > buffer.Length) {
                unchecked {
                    Tracing.Log(Tracing.Error,
                                "RGB Read(offset={0}, count={1}, length={2}",
                                (UIntPtr)(uint)offset,
                                (UIntPtr)(uint)count,
                                (UIntPtr)(uint)buffer.Length);
                }
                throw new OverflowException("Read source invalid.");
            }

            RGB[] values = new RGB [count];
            used = offset;
            offset += sizeof(uint);

            for (int i = 0; i < count; i++) {
                values[i] = new RGB(buffer[2+offset], buffer[1+offset], buffer[0+offset]);
                offset += sizeof(uint);
            }
            return values;
        }
    }
} // namespace Microsoft.Singularity.Io
