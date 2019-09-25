///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ByteOrder.cs
//
//  Note:
//

using System;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public sealed class ByteOrder
    {
        private ByteOrder()
        {
        }

        static public short Swap(short value)
        {
            return (short)((value << 8) | ((value >> 8) & 0xff));
        }

        static public ushort Swap(ushort value)
        {
            return (ushort)Swap((short)value);
        }

        static public int Swap(int value)
        {
            return
                ((value >> 24) & 0x000000ff) | ((value >>  8) & 0x0000ff00) |
                ((value <<  8) & 0x00ff0000) | ((value << 24));
        }

        static public uint Swap(uint value)
        {
            return
                ((value >> 24) & 0x000000ffu) | ((value >>  8) & 0x0000ff00u) |
                ((value <<  8) & 0x00ff0000u) | ((value << 24));
        }

        static public long Swap(long value)
        {
            return ((long)(Swap((int)(value))) << 32) + (long)Swap((int)(value >> 32));
        }

        static public ulong Swap(ulong value)
        {
            return (ulong)Swap((long)value);
        }

#if BIG_ENDIAN
        static public short  HostToBigEndian(short  value)
        {
            return value;
        }

        static public int    HostToBigEndian(int    value)
        {
            return value;
        }

        static public long   HostToBigEndian(long   value)
        {
            return value;
        }

        static public ushort HostToBigEndian(ushort value)
        {
            return value;
        }

        static public uint   HostToBigEndian(uint   value)
        {
            return value;
        }

        static public ulong  HostToBigEndian(ulong  value)
        {
            return value;
        }

        static public short  BigEndianToHost(short  value)
        {
            return value;
        }

        static public ushort BigEndianToHost(ushort value)
        {
            return value;
        }

        static public int    BigEndianToHost(int    value)
        {
            return value;
        }

        static public uint   BigEndianToHost(uint   value)
        {
            return value;
        }

        static public long   BigEndianToHost(long   value)
        {
            return value;
        }

        static public ulong  BigEndianToHost(ulong  value)
        {
            return value;
        }


        static public short  HostToLittleEndian(short  value)
        {
            return Swap(value);
        }

        static public ushort HostToLittleEndian(ushort value)
        {
            return (ushort)Swap((short)value);
        }

        static public int    HostToLittleEndian(int    value)
        {
            return Swap(value);
        }

        static public uint   HostToLittleEndian(uint   value)
        {
            return (uint)Swap((int)value);
        }

        static public long   HostToLittleEndian(long   value)
        {
            return Swap(value);
        }

        static public ulong  HostToLittleEndian(ulong  value)
        {
            return (ulong)Swap((long)value);
        }

        static public short  LittleEndianToHost(short  value)
        {
            return Swap(value);
        }

        static public ushort LittleEndianToHost(ushort value)
        {
            return (ushort)Swap((short)value);
        }

        static public int    LittleEndianToHost(int    value)
        {
            return Swap(value);
        }

        static public uint   LittleEndianToHost(uint   value)
        {
            return (uint)Swap((int)value);
        }

        static public long   LittleEndianToHost(long   value)
        {
            return Swap(value);
        }

        static public ulong  LittleEndianToHost(ulong  value)
        {
            return (ulong)Swap((long)value);
        }

#elif LITTLE_ENDIAN
        static public short  HostToLittleEndian(short  value)
        {
            return value;
        }

        static public int    HostToLittleEndian(int    value)
        {
            return value;
        }

        static public long   HostToLittleEndian(long   value)
        {
            return value;
        }

        static public ushort HostToLittleEndian(ushort value)
        {
            return value;
        }

        static public uint   HostToLittleEndian(uint   value)
        {
            return value;
        }

        static public ulong  HostToLittleEndian(ulong  value)
        {
            return value;
        }

        static public short  LittleEndianToHost(short  value)
        {
            return value;
        }

        static public ushort LittleEndianToHost(ushort value)
        {
            return value;
        }

        static public int    LittleEndianToHost(int    value)
        {
            return value;
        }

        static public uint   LittleEndianToHost(uint   value)
        {
            return value;
        }

        static public long   LittleEndianToHost(long   value)
        {
            return value;
        }

        static public ulong  LittleEndianToHost(ulong  value)
        {
            return value;
        }


        static public short  HostToBigEndian(short  value)
        {
            return Swap(value);
        }

        static public ushort HostToBigEndian(ushort value)
        {
            return (ushort)Swap((short)value);
        }

        static public int    HostToBigEndian(int    value)
        {
            return Swap(value);
        }

        static public uint   HostToBigEndian(uint   value)
        {
            return (uint)Swap((int)value);
        }

        static public long   HostToBigEndian(long   value)
        {
            return Swap(value);
        }

        static public ulong  HostToBigEndian(ulong  value)
        {
            return (ulong)Swap((long)value);
        }

        static public short  BigEndianToHost(short  value)
        {
            return Swap(value);
        }

        static public ushort BigEndianToHost(ushort value)
        {
            return (ushort)Swap((short)value);
        }

        static public int    BigEndianToHost(int    value)
        {
            return Swap(value);
        }

        static public uint   BigEndianToHost(uint   value)
        {
            return (uint)Swap((int)value);
        }

        static public long   BigEndianToHost(long   value)
        {
            return Swap(value);
        }

        static public ulong  BigEndianToHost(ulong  value)
        {
            return (ulong)Swap((long)value);
        }

#else

#error "Endian conversion routines expect BIG_ENDIAN or LITTLE_ENDIAN to be defined"

#endif
    }
} // Microsoft.Singularity.Io
