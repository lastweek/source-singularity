// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  BitConverter
//
// Purpose: Allows developers to view the base data types as
//          an arbitrary array of bits.
//
//===========================================================  

namespace System
{

    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    // The BitConverter class contains methods for
    // converting an array of bytes to one of the base data
    // types, as well as for converting a base data type to an
    // array of bytes.
    //
    //| <include path='docs/doc[@for="BitConverter"]/*' />

    [CCtorIsRunDuringStartup]
    public sealed class BitConverter {

        // This field indicates the "endianness" of the architecture.
        // The value is set to true if the architecture is
        // little endian; false if it is big endian.
        //| <include path='docs/doc[@for="BitConverter.IsLittleEndian"]/*' />
        public static readonly bool IsLittleEndian = true;

        // This class only contains static methods and may not be instantiated.
        private BitConverter() {
        }

        // ======================================================================
        // Convert from primitive types to byte array slices.  These functions
        // do not perform memory allocation and so are suitable for use in
        // interrupt handlers and other no-allocation-allowed contexts. -- mbj
        // ======================================================================

        // Converts a byte into an existing array slice of bytes with length one.
        public static void GetBytes(bool value, byte[] array, int startIndex) {
            const int bytesNeeded = 1;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            array[startIndex] = (value ? (byte)Boolean.True : (byte)Boolean.False );
        }

        // Converts a char into an existing array slice of bytes with length two.
        public static void GetBytes(char value, byte[] array, int startIndex) {
            const int bytesNeeded = 2;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            if (IsLittleEndian) {
                array[startIndex + 0] = (byte)(value);
                array[startIndex + 1] = (byte)(value >> 8);
            }
            else {
                array[startIndex + 1] = (byte)(value);
                array[startIndex + 0] = (byte)(value >> 8);
            }
        }

        // Converts a short into an existing array slice of bytes with length two.
        public static void GetBytes(short value, byte[] array, int startIndex) {
            const int bytesNeeded = 2;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            if (IsLittleEndian) {
                array[startIndex + 0] = (byte)(value);
                array[startIndex + 1] = (byte)(value >> 8);
            }
            else {
                array[startIndex + 1] = (byte)(value);
                array[startIndex + 0] = (byte)(value >> 8);
            }
        }

        // Converts an int into an existing array slice of bytes with length four.
        public static void GetBytes(int value, byte[] array, int startIndex) {
            const int bytesNeeded = 4;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            if (IsLittleEndian) {
                array[startIndex + 0] = (byte)(value);
                array[startIndex + 1] = (byte)(value >> 8);
                array[startIndex + 2] = (byte)(value >> 16);
                array[startIndex + 3] = (byte)(value >> 24);
            }
            else {
                array[startIndex + 3] = (byte)(value);
                array[startIndex + 2] = (byte)(value >> 8);
                array[startIndex + 1] = (byte)(value >> 16);
                array[startIndex + 0] = (byte)(value >> 24);
            }
        }

        // Converts a long into an existing array slice of bytes with length eight.
        public static void GetBytes(long value, byte[] array, int startIndex) {
            const int bytesNeeded = 8;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            if (IsLittleEndian) {
                array[startIndex + 0] = (byte)(value);
                array[startIndex + 1] = (byte)(value >> 8);
                array[startIndex + 2] = (byte)(value >> 16);
                array[startIndex + 3] = (byte)(value >> 24);
                array[startIndex + 4] = (byte)(value >> 32);
                array[startIndex + 5] = (byte)(value >> 40);
                array[startIndex + 6] = (byte)(value >> 48);
                array[startIndex + 7] = (byte)(value >> 56);
            }
            else {
                array[startIndex + 7] = (byte)(value);
                array[startIndex + 6] = (byte)(value >> 8);
                array[startIndex + 5] = (byte)(value >> 16);
                array[startIndex + 4] = (byte)(value >> 24);
                array[startIndex + 3] = (byte)(value >> 32);
                array[startIndex + 2] = (byte)(value >> 40);
                array[startIndex + 1] = (byte)(value >> 48);
                array[startIndex + 0] = (byte)(value >> 56);
            }
        }

        // Converts an ushort into an existing array slice of bytes with length two.
        [CLSCompliant(false)]
        public static void GetBytes(ushort value, byte[] array, int startIndex) {
            const int bytesNeeded = 2;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            if (IsLittleEndian) {
                array[startIndex + 0] = (byte)(value);
                array[startIndex + 1] = (byte)(value >> 8);
            }
            else {
                array[startIndex + 1] = (byte)(value);
                array[startIndex + 0] = (byte)(value >> 8);
            }
        }

        // Converts an uint into an existing array slice of bytes with length four.
        [CLSCompliant(false)]
        public static void GetBytes(uint value, byte[] array, int startIndex) {
            const int bytesNeeded = 4;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            if (IsLittleEndian) {
                array[startIndex + 0] = (byte)(value);
                array[startIndex + 1] = (byte)(value >> 8);
                array[startIndex + 2] = (byte)(value >> 16);
                array[startIndex + 3] = (byte)(value >> 24);
            }
            else {
                array[startIndex + 3] = (byte)(value);
                array[startIndex + 2] = (byte)(value >> 8);
                array[startIndex + 1] = (byte)(value >> 16);
                array[startIndex + 0] = (byte)(value >> 24);
            }
        }

        // Converts an unsigned long into an existing array slice of bytes with length eight.
        [CLSCompliant(false)]
        public static void GetBytes(ulong value, byte[] array, int startIndex) {
            const int bytesNeeded = 8;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            if (IsLittleEndian) {
                array[startIndex + 0] = (byte)(value);
                array[startIndex + 1] = (byte)(value >> 8);
                array[startIndex + 2] = (byte)(value >> 16);
                array[startIndex + 3] = (byte)(value >> 24);
                array[startIndex + 4] = (byte)(value >> 32);
                array[startIndex + 5] = (byte)(value >> 40);
                array[startIndex + 6] = (byte)(value >> 48);
                array[startIndex + 7] = (byte)(value >> 56);
            }
            else {
                array[startIndex + 7] = (byte)(value);
                array[startIndex + 6] = (byte)(value >> 8);
                array[startIndex + 5] = (byte)(value >> 16);
                array[startIndex + 4] = (byte)(value >> 24);
                array[startIndex + 3] = (byte)(value >> 32);
                array[startIndex + 2] = (byte)(value >> 40);
                array[startIndex + 1] = (byte)(value >> 48);
                array[startIndex + 0] = (byte)(value >> 56);
            }
        }

/*
        // Converts a float into an existing array slice of bytes with length four.
        public unsafe static void GetBytes(float value, byte[] array, int startIndex)
        {
            const int bytesNeeded = 4;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            fixed (byte *ptr = &array[startIndex])
                *((float*) ptr) = value;
        }

        // Converts a double into an existing array slice of bytes with length eight.
        public unsafe static void GetBytes(double value, byte[] array, int startIndex)
        {
            const int bytesNeeded = 8;
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + bytesNeeded > array.Length) {
                throw new ArgumentException("Array is too small");
            }
            fixed (byte *ptr = &array[startIndex])
                *((double*) ptr) = value;
        }
*/

        // ======================================================================
        // Convert from primitive types to new byte arrays.  These functions
        // perform memory allocation and so are unsuitable for use in
        // interrupt handlers and other no-allocation-allowed contexts. -- mbj
        // ======================================================================

        // Converts a byte into an array of bytes with length one.
        //| <include path='docs/doc[@for="BitConverter.GetBytes"]/*' />
        public static byte[] GetBytes(bool value) {
            byte[] result = new byte[1];
            GetBytes(value, result, 0);
            return result;
        }

        // Converts a char into an array of bytes with length two.
        //| <include path='docs/doc[@for="BitConverter.GetBytes1"]/*' />
        public static byte[] GetBytes(char value) {
            // See also Lightning\Src\VM\COMUtilNative.cpp::CharToBytes
            byte[] result = new byte[2];
            GetBytes(value, result, 0);
            return result;
        }

        // Converts a short into an array of bytes with length
        // two.
        //| <include path='docs/doc[@for="BitConverter.GetBytes2"]/*' />
        public static byte[] GetBytes(short value) {
            byte[] result = new byte[2];
            GetBytes(value, result, 0);
            return result;
        }

        // Converts an int into an array of bytes with length
        // four.
        //| <include path='docs/doc[@for="BitConverter.GetBytes3"]/*' />
        public static byte[] GetBytes(int value) {
            byte[] result = new byte[4];
            GetBytes(value, result, 0);
            return result;
        }

        // Converts a long into an array of bytes with length
        // eight.
        //| <include path='docs/doc[@for="BitConverter.GetBytes4"]/*' />
        public static byte[] GetBytes(long value) {
            byte[] result = new byte[8];
            GetBytes(value, result, 0);
            return result;
        }

        // Converts an ushort into an array of bytes with
        // length two.
        //| <include path='docs/doc[@for="BitConverter.GetBytes5"]/*' />
        [CLSCompliant(false)]
        public static byte[] GetBytes(ushort value) {
            byte[] result = new byte[2];
            GetBytes(value, result, 0);
            return result;
        }

        // Converts an uint into an array of bytes with
        // length four.
        //| <include path='docs/doc[@for="BitConverter.GetBytes6"]/*' />
        [CLSCompliant(false)]
        public static byte[] GetBytes(uint value) {
            byte[] result = new byte[4];
            GetBytes(value, result, 0);
            return result;
        }

        // Converts an unsigned long into an array of bytes with
        // length eight.
        //| <include path='docs/doc[@for="BitConverter.GetBytes7"]/*' />
        [CLSCompliant(false)]
        public static byte[] GetBytes(ulong value) {
            byte[] result = new byte[8];
            GetBytes(value, result, 0);
            return result;
        }

/*
        // Converts a float into an array of bytes with length
        // four.
        //| <include path='docs/doc[@for="BitConverter.GetBytes8"]/*' />
        public static byte[] GetBytes(float value)
        {
            byte[] result = new byte[4];
            GetBytes(value, result, 0);
            return result;
        }

        // Converts a double into an array of bytes with length
        // eight.
        //| <include path='docs/doc[@for="BitConverter.GetBytes9"]/*' />
        public static byte[] GetBytes(double value)
        {
            byte[] result = new byte[8];
            GetBytes(value, result, 0);
            return result;
        }
*/

        // ============ Convert from byte array slices to primitive types ============

        // Converts an array of bytes into a char.
        //| <include path='docs/doc[@for="BitConverter.ToChar"]/*' />
        public static char ToChar(byte[] value, int startIndex) {
            return (char)(ToInt16(value, startIndex));
        }

        // Converts an array of bytes into a short.
        //| <include path='docs/doc[@for="BitConverter.ToInt16"]/*' />
        public static short ToInt16(byte[] value, int startIndex)
        {
            if (value == null) {
                throw new ArgumentNullException("value");
            }
            if (((uint)startIndex) >= (uint)value.Length) {
                throw new ArgumentOutOfRangeException("startIndex");
            }
            if (startIndex > (value.Length - 2)) {
                throw new ArgumentException("startIndex");
            }
                if (IsLittleEndian) {
                    return (short)(value[startIndex + 0] | (value[startIndex + 1] << 8));
                }
                else {
                    return (short)(value[startIndex + 1] | (value[startIndex + 0] << 8));
                }
        }

        // Converts an array of bytes into an int.
        //| <include path='docs/doc[@for="BitConverter.ToInt32"]/*' />
        public static int ToInt32(byte[]value, int startIndex)
        {
            if (value == null) {
                throw new ArgumentNullException("value");
            }
            if (((uint)startIndex) >= (uint)value.Length) {
                throw new ArgumentOutOfRangeException("startIndex");
            }
            if (startIndex > (value.Length - 4)) {
                throw new ArgumentException("startIndex");
            }
                if (IsLittleEndian) {
                    return (
                        ((int)value[startIndex + 0]) |
                        (((int)value[startIndex + 1]) << 8) |
                        (((int)value[startIndex + 2]) << 16) |
                        (((int)value[startIndex + 3]) << 24)
                        );
                }
                else {
                    return (
                        ((int)value[startIndex + 3]) |
                        (((int)value[startIndex + 2]) << 8) |
                        (((int)value[startIndex + 1]) << 16) |
                        (((int)value[startIndex + 0]) << 24)
                        );
                }
        }

        // Converts an array of bytes into a long.
        //| <include path='docs/doc[@for="BitConverter.ToInt64"]/*' />
        public static long ToInt64(byte[] value, int startIndex)
        {
            if (value == null) {
                throw new ArgumentNullException("value");
            }
            if (((uint)startIndex) >= (uint)value.Length) {
                throw new ArgumentOutOfRangeException("startIndex");
            }
            if (startIndex > (value.Length - 8)) {
                throw new ArgumentException("startIndex");
            }
                if (IsLittleEndian) {
                    uint lo = (((uint)value[startIndex + 0]) |
                              (((uint)value[startIndex + 1]) << 8) |
                              (((uint)value[startIndex + 2]) << 16) |
                              (((uint)value[startIndex + 3]) << 24)
                              );
                    uint hi = (((uint)value[startIndex + 4]) |
                              (((uint)value[startIndex + 5]) << 8) |
                              (((uint)value[startIndex + 6]) << 16) |
                              (((uint)value[startIndex + 7]) << 24)
                              );
                    return (long)(((ulong)lo) | ((ulong)hi) << 32);
                }
                else {
                    uint hi = (((uint)value[startIndex + 3]) |
                              (((uint)value[startIndex + 2]) << 8) |
                              (((uint)value[startIndex + 1]) << 16) |
                              (((uint)value[startIndex + 0]) << 24)
                              );
                    uint lo = (((uint)value[startIndex + 7]) |
                              (((uint)value[startIndex + 6]) << 8) |
                              (((uint)value[startIndex + 5]) << 16) |
                              (((uint)value[startIndex + 4]) << 24)
                              );
                    return (long)(((ulong)lo) | ((ulong)hi) << 32);
                }
        }

        // Converts an array of bytes into an ushort.
        //
        //| <include path='docs/doc[@for="BitConverter.ToUInt16"]/*' />
        [CLSCompliant(false)]
        public static ushort ToUInt16(byte[] value, int startIndex)
        {
            unchecked {
                return (ushort)ToInt16(value, startIndex);
            }
        }

        // Converts an array of bytes into an uint.
        //
        //| <include path='docs/doc[@for="BitConverter.ToUInt32"]/*' />
        [CLSCompliant(false)]
        public static uint ToUInt32(byte[] value, int startIndex)
        {
            unchecked {
                return (uint)ToInt32(value, startIndex);
            }
        }

        // Converts an array of bytes into an unsigned long.
        //
        //| <include path='docs/doc[@for="BitConverter.ToUInt64"]/*' />
        [CLSCompliant(false)]
        public static ulong ToUInt64(byte[] value, int startIndex)
        {
            unchecked {
                return (ulong)ToInt64(value, startIndex);
            }
        }

/*
        // Converts an array of bytes into a float.
        //| <include path='docs/doc[@for="BitConverter.ToSingle"]/*' />
        public static unsafe float ToSingle(byte[]value, int startIndex) {
            float result;
            fixed (byte *ptr = value) {
                result = *((float *) (ptr + startIndex));
            }
            return result;
        }

        // Converts an array of bytes into a double.
        //| <include path='docs/doc[@for="BitConverter.ToDouble"]/*' />
        public static unsafe double ToDouble(byte []value, int startIndex) {
            double result;
            fixed (byte *ptr = value) {
                result = *((double *) (ptr + startIndex));
            }
            return result;
        }
*/

        //==================================ToBoolean===================================
        //Action:  Convert an array of bytes to a boolean value.  We treat this array
        //         as if the first 4 bytes were an Int4 an operate on this value.
        //Returns: True if the Int4 value of the first 4 bytes is non-zero.
        //Arguments: value -- The byte array
        //           startIndex -- The position within the array.
        //Exceptions: See ToInt4.
        //==============================================================================  
        // Converts an array of bytes into a boolean.
        //| <include path='docs/doc[@for="BitConverter.ToBoolean"]/*' />
        public static bool ToBoolean(byte[]value, int startIndex) {
            if (value == null)
                throw new ArgumentNullException("value");
            if (startIndex < 0)
                throw new ArgumentOutOfRangeException("startIndex", "ArgumentOutOfRange_NeedNonNegNum");
            if (startIndex > value.Length - 1)
                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_Index");

            return (value[startIndex]==0)?false:true;
        }

/*
        //| <include path='docs/doc[@for="BitConverter.DoubleToInt64Bits"]/*' />
        [Inline]
        public static unsafe long DoubleToInt64Bits(double value) {
            return *((long *)&value);
        }

        //| <include path='docs/doc[@for="BitConverter.Int64BitsToDouble"]/*' />
        [Inline]
        public static unsafe double Int64BitsToDouble(long value) {
            return *((double *)&value);
        }

        //| <include path='docs/doc[@for="BitConverter.DoubleToUInt64Bits"]/*' />
        [Inline]
        [CLSCompliant(false)]
        public static unsafe ulong DoubleToUInt64Bits(double value) {
            return *((ulong *)&value);
        }

        //| <include path='docs/doc[@for="BitConverter.UInt64BitsToDouble"]/*' />
        [Inline]
        [CLSCompliant(false)]
        public static unsafe double UInt64BitsToDouble(ulong value) {
            return *((double *)&value);
        }

        //| <include path='docs/doc[@for="BitConverter.SingleToUInt32Bits"]/*' />
        [Inline]
        [CLSCompliant(false)]
        public static unsafe uint SingleToUInt32Bits(float value) {
            return *((uint *)&value);
        }

        //| <include path='docs/doc[@for="BitConverter.UInt32BitsToSingle"]/*' />
        [Inline]
        [CLSCompliant(false)]
        public static unsafe float UInt32BitsToSingle(uint value) {
            return *((float *)&value);
        }
*/
    }
}
