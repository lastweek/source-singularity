///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   RGB.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public struct RGB
    {
        byte    red;
        byte    green;
        byte    blue;

        public RGB(byte _red, byte _green, byte _blue)
        {
            red = _red;
            green = _green;
            blue = _blue;
        }

        public RGB(uint color32)
        {
            red = (byte)((color32 & 0xff0000) >> 16);
            green = (byte)((color32 & 0x00ff00) >> 8);
            blue = (byte)((color32 & 0x0000ff) >> 0);
        }

        public static explicit operator uint (RGB color)
        {
            return Compute32(color.red, color.green, color.blue);
        }

        public static explicit operator ushort (RGB color)
        {
            return Compute16(color.red, color.green, color.blue);
        }

        public static explicit operator byte (RGB color)
        {
            return Compute4(color.red, color.green, color.blue);
        }

        public static byte Compute4(byte red, byte green, byte blue)
        {
            byte c = 0;

            if (red > 0x40) {
                c |= 0x4;
            }
            if (green > 0x40) {
                c |= 0x2;
            }
            if (blue > 0x40) {
                c |= 0x1;
            }
            if (red > 0x80 || green > 0x80 || blue > 0x80) {
                c |= 0x8;
            }
            return c;
        }

        public static ushort Compute16(byte red, byte green, byte blue)
        {
            return (ushort)((((ushort)red >> 3) << 11) |
                            (((ushort)green >> 2) << 5) |
                            ((ushort)blue >> 3));
        }

        public static uint Compute32(byte red, byte green, byte blue)
        {
            return ((((uint)red) << 16) |
                    (((uint)green) << 8) |
                    ((uint)blue));
        }

        public static readonly RGB White    = new RGB(255, 255, 255);
        public static readonly RGB Red      = new RGB(255, 0, 0);
        public static readonly RGB Green    = new RGB(0, 255, 0);
        public static readonly RGB Blue     = new RGB(0, 0, 255);
        public static readonly RGB Black    = new RGB(0, 0, 0);
        public static readonly RGB Gray     = new RGB(127, 127, 127);
    };
} // namespace Microsoft.Singularity.Io
