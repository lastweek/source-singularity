///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: NetworkBitConverter.cs
//

using System;

#if SINGULARITY
using Microsoft.Singularity.Io;
#endif

namespace Drivers.Net
{
    /// <summary>
    /// Converts host ordered integer base types to network
    /// ordered array of bytes, and vice-versa.
    /// </summary>
    public sealed class NetworkBitConverter
    {
        /// <returns>
        /// Returns a host-order 16-bit signed integer converted from
        /// two bytes in a byte array.
        /// </returns>
        public static short ToInt16(byte[] value, int startIndex)
        {
            return ByteOrder.BigEndianToHost(
                BitConverter.ToInt16(value, startIndex)
                );
        }

        /// <returns>
        /// Returns a host-order 16-bit unsigned integer converted from
        /// two bytes in a byte array.
        /// </returns>
        public static ushort ToUInt16(byte[] value, int startIndex)
        {
            return ByteOrder.BigEndianToHost(
                BitConverter.ToUInt16(value, startIndex)
                );
        }

        /// <returns>
        /// Returns a host-order 32-bit signed integer converted from
        /// two bytes in a byte array.
        /// </returns>
        public static int ToInt32(byte[] value, int startIndex)
        {
            return ByteOrder.BigEndianToHost(
                BitConverter.ToInt32(value, startIndex)
                );
        }

        /// <returns>
        /// Returns a host-order 32-bit unsigned integer converted from
        /// two bytes in a byte array.
        /// </returns>
        public static uint ToUInt32(byte[] value, int startIndex)
        {
            return ByteOrder.BigEndianToHost(
                BitConverter.ToUInt32(value, startIndex)
                );
        }

        /// <returns>
        /// Returns a host-order 64-bit signed integer converted from
        /// two bytes in a byte array.
        /// </returns>
        public static long ToInt64(byte[] value, int startIndex)
        {
            return ByteOrder.BigEndianToHost(
                BitConverter.ToInt64(value, startIndex)
                );
        }

        /// <returns>
        /// Returns a host-order 64-bit unsigned integer converted from
        /// two bytes in a byte array.
        /// </returns>
        public static ulong ToUInt64(byte[] value, int startIndex)
        {
            return ByteOrder.BigEndianToHost(
                BitConverter.ToUInt64(value, startIndex)
                );
        }

        /// <returns>
        /// Returns network ordered bytes representing 16-bit signed integer.
        /// </returns>
        public static byte[] GetBytes(short value)
        {
            return BitConverter.GetBytes(
                ByteOrder.HostToBigEndian(value)
                );
        }

        /// <returns>
        /// Returns network ordered bytes representing 16-bit unsigned integer.
        /// </returns>
        public static byte[] GetBytes(ushort value)
        {
            return BitConverter.GetBytes(
                ByteOrder.HostToBigEndian(value)
                );
        }

        /// <returns>
        /// Returns network ordered bytes representing 32-bit signed integer.
        /// </returns>
        public static byte[] GetBytes(int value)
        {
            return BitConverter.GetBytes(
                ByteOrder.HostToBigEndian(value)
                );
        }

        /// <returns>
        /// Returns network ordered bytes representing 32-bit unsigned integer.
        /// </returns>
        public static byte[] GetBytes(uint value)
        {
            return BitConverter.GetBytes(
                ByteOrder.HostToBigEndian(value)
                );
        }

        /// <returns>
        /// Returns network ordered bytes representing 64-bit signed integer.
        /// </returns>
        public static byte[] GetBytes(long value)
        {
            return BitConverter.GetBytes(
                ByteOrder.HostToBigEndian(value)
                );
        }

        /// <returns>
        /// Returns network ordered bytes representing 64-bit unsigned integer.
        /// </returns>
        public static byte[] GetBytes(ulong value)
        {
            return BitConverter.GetBytes(
                ByteOrder.HostToBigEndian(value)
                );
        }

        /// <summary>
        /// Convert a host-ordered 16-bit signed integer into network order
        /// and place result in a byte array.
        /// <param name = "value"> Value to be placed into byte array.</param>
        /// <param name = "dstBuffer"> Byte array to receive value.</param>
        /// <param name = "dstOffset"> Offset in buffer to place value.
        /// </param>
        /// </summary>
        public static int PutBytes(short   value,
                                   byte[]! dstBuffer,
                                   int     dstOffset)
        {
            dstBuffer[dstOffset]     = (byte) (value >> 8);
            dstBuffer[dstOffset + 1] = (byte) value;
            return 2;
        }

        /// <summary>
        /// Convert a host-ordered 16-bit unsigned integer into network order
        /// and place result in a byte array.
        /// <param name = "value"> Value to be placed into byte array.</param>
        /// <param name = "dstBuffer"> Byte array to receive value.</param>
        /// <param name = "dstOffset"> Offset in buffer to place value.
        /// </param>
        /// </summary>
        public static int PutBytes(ushort   value,
                                   byte[]!  dstBuffer,
                                   int      dstOffset)
        {
            dstBuffer[dstOffset]     = (byte) (value >> 8);
            dstBuffer[dstOffset + 1] = (byte) value;
            return 2;
        }

        /// <summary>
        /// Convert a host-ordered 32-bit signed integer into network order
        /// and place result in a byte array.
        /// <param name = "value"> Value to be placed into byte array.</param>
        /// <param name = "dstBuffer"> Byte array to receive value.</param>
        /// <param name = "dstOffset"> Offset in buffer to place value.
        /// </param>
        /// </summary>
        public static int PutBytes(int     value,
                                   byte[]! dstBuffer,
                                   int     dstOffset)
        {
            dstBuffer[dstOffset]     = (byte) (value >> 24);
            dstBuffer[dstOffset + 1] = (byte) (value >> 16);
            dstBuffer[dstOffset + 2] = (byte) (value >> 8);
            dstBuffer[dstOffset + 3] = (byte) (value);
            return 4;
        }

        /// <summary>
        /// Convert a host-ordered 32-bit unsigned integer into network order
        /// and place result in a byte array.
        /// <param name = "value"> Value to be placed into byte array.</param>
        /// <param name = "dstBuffer"> Byte array to receive value.</param>
        /// <param name = "dstOffset"> Offset in buffer to place value.
        /// </param>
        /// </summary>
        public static int PutBytes(uint    value,
                                   byte[]! dstBuffer,
                                   int     dstOffset)
        {
            dstBuffer[dstOffset]     = (byte) (value >> 24);
            dstBuffer[dstOffset + 1] = (byte) (value >> 16);
            dstBuffer[dstOffset + 2] = (byte) (value >> 8);
            dstBuffer[dstOffset + 3] = (byte) (value);
            return 4;
        }

        /// <summary>
        /// Convert a host-ordered 64-bit signed integer into network order
        /// and place result in a byte array.
        /// <param name = "value"> Value to be placed into byte array.</param>
        /// <param name = "dstBuffer"> Byte array to receive value.</param>
        /// <param name = "dstOffset"> Offset in buffer to place value.
        /// </param>
        /// </summary>
        public static int PutBytes(long    value,
                                   byte[]! dstBuffer,
                                   int     dstOffset)
        {
            PutBytes((int) (value >> 32), dstBuffer, dstOffset);
            PutBytes((uint) (value), dstBuffer, dstOffset + 4);
            return 8;
        }

        /// <summary>
        /// Convert a host-ordered 64-bit unsigned integer into network order
        /// and place result in a byte array.
        /// <param name = "value"> Value to be placed into byte array.</param>
        /// <param name = "dstBuffer"> Byte array to receive value.</param>
        /// <param name = "dstOffset"> Offset in buffer to place value.
        /// </param>
        /// </summary>
        public static int PutBytes(ulong   value,
                                   byte[]! dstBuffer,
                                   int     dstOffset)
        {
            PutBytes((uint) (value >> 32), dstBuffer, dstOffset);
            PutBytes((uint) (value), dstBuffer, dstOffset + 4);
            return 8;
        }

        private NetworkBitConverter()
        {
        }
    }
} // namespace Drivers.Net
