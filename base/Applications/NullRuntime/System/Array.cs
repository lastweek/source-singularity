 // ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Array
//
// Purpose: Base class which can be used to access any array
//
//===========================================================  
namespace System
{
    using Microsoft.Bartok.Runtime;
    using System;
    using System.Collections;
    using System.GCs;
    using System.Diagnostics;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using System.Threading;

    // REVIEW: to be moved/integrated elsewhere
    // REVIEW: see System.Variant::ClassTypes
    internal class TypeInfo {
        internal static VTable[] arrayOfBox = {
            null, // not array
            null, // reference
            null, // untraced pointer
            null, // struct
            ((RuntimeType)typeof(Boolean)).classVtable,
            ((RuntimeType)typeof(Char)).classVtable,
            ((RuntimeType)typeof(SByte)).classVtable,
            ((RuntimeType)typeof(Int16)).classVtable,
            ((RuntimeType)typeof(Int32)).classVtable,
            ((RuntimeType)typeof(Int64)).classVtable,
            ((RuntimeType)typeof(Byte)).classVtable,
            ((RuntimeType)typeof(UInt16)).classVtable,
            ((RuntimeType)typeof(UInt32)).classVtable,
            ((RuntimeType)typeof(UInt64)).classVtable,
            ((RuntimeType)typeof(Single)).classVtable,
            ((RuntimeType)typeof(Double)).classVtable,
            ((RuntimeType)typeof(IntPtr)).classVtable,
            ((RuntimeType)typeof(UIntPtr)).classVtable
        };
    }

    //| <include path='docs/doc[@for="Array"]/*' />
    [StructLayout(LayoutKind.Sequential)]
    public abstract class Array
    {
        // [spacer] means 4 byte insertion if elements are 8-aligned

        // Vector layout:
        // length, [spacer], elem0, ...

        // Rect layout:
        // rank, total_length, base0, length0, ..., basen, lengthn, elem0, ...

        // VTable vtable is inherited from Object

        internal int field1;
        private int field2;
        private int field3;
        private int field4;

        /// <internalonly/>
        private Array() {}

        // Create instance will create an array
        //| <include path='docs/doc[@for="Array.CreateInstance"]/*' />
        public static Array CreateInstance(Type elementType, int length)
        {
            if (elementType == null)
                throw new ArgumentNullException("elementType");
            RuntimeType t = elementType.UnderlyingSystemType as RuntimeType;
            if (t == null)
                throw new ArgumentException("Arg_MustBeType","elementType");
            if (length < 0)
                throw new ArgumentOutOfRangeException("length", "ArgumentOutOfRange_NeedNonNegNum");
            VTable v = t.classVtable.vectorClass;
            if (v == null) {
                throw new InvalidCastException("Arg_VectorClassNotFound");
            }
            return GC.AllocateVector(v, length);
        }

        private static void VectorCopy(Object srcObject, int srcOffset,
                                       Object dstObject, int dstOffset,
                                       int length) {
            StructuralType srcArrayOf = srcObject.vtable.arrayOf;
            StructuralType dstArrayOf = dstObject.vtable.arrayOf;
            if ((srcArrayOf == StructuralType.None)
                 || (srcArrayOf != dstArrayOf) ) {
                throw new ArrayTypeMismatchException();
            }
            if ((srcOffset < 0)
                 || (dstOffset < 0)
                 || (length < 0) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            switch (srcArrayOf) {
              case StructuralType.None:
                throw new ArrayTypeMismatchException();

              case StructuralType.Bool: {
                  bool[] srcArray = (bool[])srcObject;
                  bool[] dstArray = (bool[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.Char: {
                  char[] srcArray = (char[])srcObject;
                  char[] dstArray = (char[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.Int8: {
                  sbyte[] srcArray = (sbyte[])srcObject;
                  sbyte[] dstArray = (sbyte[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.Int16:  {
                  short[] srcArray = (short[])srcObject;
                  short[] dstArray = (short[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.Int32: {
                  int[] srcArray = (int[])srcObject;
                  int[] dstArray = (int[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.Int64: {
                  long[] srcArray = (long[])srcObject;
                  long[] dstArray = (long[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.UInt8: {
                  byte[] srcArray = (byte[])srcObject;
                  byte[] dstArray = (byte[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.UInt16:  {
                  ushort[] srcArray = (ushort[])srcObject;
                  ushort[] dstArray = (ushort[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.UInt32: {
                  uint[] srcArray = (uint[])srcObject;
                  uint[] dstArray = (uint[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.UInt64: {
                  ulong[] srcArray = (ulong[])srcObject;
                  ulong[] dstArray = (ulong[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.Float32: {
                  float[] srcArray = (float[])srcObject;
                  float[] dstArray = (float[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.Float64: {
                  double[] srcArray = (double[])srcObject;
                  double[] dstArray = (double[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              case StructuralType.Reference: {
                  Object[] srcArray = (Object[])srcObject;
                  Object[] dstArray = (Object[])dstObject;
                  Copy(srcArray,srcOffset,dstArray,dstOffset,length);
                  return;
              }
              default:
                VTable.DebugBreak();
                return;
            }
        }

#if DEBUG_ARRAY
        private void debug(Object srcArray,int srcOffset,Object dstArray,int dstOffset,
                           int length)
        {
#if TODO
            DebugPrint("System.Copy(");
            DebugPrint(srcArray.getClass().getName());
            DebugPrint(",");
            DebugPrint(srcOffset);
            DebugPrint(",");
            DebugPrint(dstArray.getClass().getName());
            DebugPrint(",");
            DebugPrint(dstOffset);
            DebugPrint(",");
            DebugPrint(length);
            DebugPrintln(")");
#endif
        }
#endif

        public static void Copy(bool[] srcArray, int srcOffset, bool[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;

#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfBool);
            }
#endif

            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyBoolDown(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyBoolDown(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyBoolUp(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyBoolUp(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        public static void Copy(char[] srcArray, int srcOffset, char[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfChar);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyCharDown(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyCharDown(srcArray, srcOffset, dstArray, dstOffset, length);
                }

            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyCharUp(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyCharUp(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        [CLSCompliant(false)]
        public static void Copy(sbyte[] srcArray, int srcOffset, sbyte[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfByte);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyInt8Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyInt8Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyInt8Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyInt8Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
        }

        public static void Copy(short[] srcArray, int srcOffset, short[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfShort);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyInt16Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyInt16Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyInt16Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyInt16Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        public static void Copy(int[] srcArray, int srcOffset, int[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfInt);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyInt32Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyInt32Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.CopyInt32Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyInt32Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        public static void Copy(long[] srcArray, int srcOffset, long[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfLong);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyInt64Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyInt64Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyInt64Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyInt64Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        public static void Copy(byte[] srcArray, int srcOffset, byte[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfByte);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyUInt8Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyUInt8Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyUInt8Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyUInt8Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
        }

        [CLSCompliant(false)]
        public static void Copy(ushort[] srcArray, int srcOffset, ushort[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfShort);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyUInt16Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyUInt16Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyUInt16Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyUInt16Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        [CLSCompliant(false)]
        public static void Copy(uint[] srcArray, int srcOffset, uint[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfInt);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyUInt32Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyUInt32Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.CopyUInt32Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyUInt32Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        [CLSCompliant(false)]
        public static void Copy(ulong[] srcArray, int srcOffset, ulong[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfLong);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyUInt64Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyUInt64Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyUInt64Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyUInt64Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        public static void Copy(float[] srcArray, int srcOffset, float[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfFloat);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyFloat32Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyFloat32Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyFloat32Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyFloat32Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        public static void Copy(double[] srcArray, int srcOffset, double[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfDouble);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyFloat64Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyFloat64Down(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            else {
                if ((srcOffset + length <= srcLength)
                     && (dstOffset+length <= dstLength) ) {
                    ArrayHelper.UncheckedCopyFloat64Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
                else {
                    ArrayHelper.CopyFloat64Up(srcArray, srcOffset, dstArray, dstOffset, length);
                }
            }
            return;
        }

        public static void Copy(Object[] srcArray, int srcOffset, Object[] dstArray, int dstOffset, int length)
        {
#if DEBUG_ARRAY
            debug(srcArray,srcOffset,dstArray,dstOffset,length);
#endif
            int srcLength = srcArray.Length;
            int dstLength = dstArray.Length;
#if TODO
            if (VTable.enableLibraryOptions) {
                Assert(VTable.enableLibraryOptions && EnableLibraryAsserts() &&
                       srcArray.vtable.arrayOf == Array.OfReference);
            }
#endif
            if ((length < 0)
                 || (srcOffset < 0)
                 || (dstOffset < 0)
                 || (srcOffset+length > srcLength)
                 || (dstOffset+length > dstLength) ) {
                VTable.throwNewArgumentOutOfRangeException();
            }
            if ((srcArray == dstArray)
                 && (srcOffset < dstOffset)
                 && (dstOffset < srcOffset+length) ) {
                int dx = dstOffset+length-1;
                int sx = srcOffset+length-1;
                for (int i = length - 1; i >= 0; i--) {
                    dstArray[dx] = srcArray[sx];
                    sx--;
                    dx--;
                }
                //          for (int i=0; i<length; i++) {
                //              dstArray[dstOffset+length-i-1] = srcArray[srcOffset+length-i-1];
                //          }
            }
            else {
                int dx = dstOffset;
                int sx = srcOffset;
                for (int i = length - 1; i >= 0; i--) {
                    dstArray[dx] = srcArray[sx];
                    sx++;
                    dx++;
                }
                //          for (int i=0; i<length; i++) {
                //              dstArray[dstOffset+i] = srcArray[srcOffset+i];
                //          }
            }
            return;
        }

        private enum AssignArray {
            WrongType, WillWork, MustCast, BoxValueClassOrPrimitive,
            UnboxValueClassOrPrimitive, PrimitiveWiden
        }

        private static AssignArray CanAssignArrayType(Array source, Array dest) {
            VTable.Assert(source != null);
            VTable.Assert(dest != null);

            VTable sourceVTable = source.vtable;
            VTable destVTable = dest.vtable;
            RuntimeType srcType = sourceVTable.vtableType;
            RuntimeType destType = destVTable.vtableType;
            if (srcType == destType) {
                return AssignArray.WillWork;
            }
            //
            // Code review: do we need the following test on element types?
            //
            RuntimeType srcElemType = sourceVTable.arrayElementClass.vtableType;
            RuntimeType destElemType = destVTable.arrayElementClass.vtableType;

            // The next 50 lines are a little tricky.  Change them with great
            // care.  Make sure you run the ArrayCopy BVT when changing this.

            // TODO: get an ArrayCopy BVT
            // REVIEW: System.Enum[] and System.ValueType[]
            //   are arrays of references to boxed elements -
            //   need to be careful there

            if (srcElemType == destElemType) {
                return AssignArray.WillWork;
            }
            // Value class boxing
            if (srcElemType.IsValueType && !destElemType.IsValueType) {
                return AssignArray.BoxValueClassOrPrimitive;
            }

            // Value class unboxing.
            if (!srcElemType.IsValueType && destElemType.IsValueType) {
                return AssignArray.UnboxValueClassOrPrimitive;
            }

            // Copying primitives from one type to another
            if (srcElemType.IsPrimitive && destElemType.IsPrimitive) {
                VTable.NotImplemented("arraycopy primitives");
            }

            if (VTable.isValidAssignment(destElemType, srcElemType)) {
                return AssignArray.WillWork;
            }
            if (VTable.isValidAssignment(srcElemType, destElemType)) {
                return AssignArray.MustCast;
            }
            VTable.NotImplemented("arraycopy more cases to do");
            return AssignArray.WrongType;
        }

        private unsafe static void CastCheckEachElement(Array sourceArray,
                                                        int srcIndex,
                                                        Array destArray,
                                                        int destIndex,
                                                        int len)
        {
            // pSrc is either a PTRARRAYREF or a multidimensional array.
            VTable.Assert(sourceArray != null && srcIndex >= 0 &&
                          destArray != null && destIndex >= 0 && len >= 0);
            VTable destVT = destArray.vtable.arrayElementClass;
            VTable.Assert(destVT != null);
            // Cache last cast test to speed up cast checks.
            VTable lastVT = null;

            //const BOOL destIsArray = destTH.IsArray();
            fixed (int *srcField = &sourceArray.field1) {
                fixed (int *dstField = &destArray.field1) {
                    UIntPtr* sourceArrayPtr =(UIntPtr*)
                        sourceArray.GetFirstElementAddress(srcField);
                    UIntPtr* destArrayPtr = (UIntPtr*)
                        destArray.GetFirstElementAddress(dstField);
                    Object obj;
                    for (int i = srcIndex; i < srcIndex + len; ++i) {
                        UIntPtr objAddress = sourceArrayPtr[i];
                        obj = Magic.fromAddress(objAddress);
                        // Now that we have grabbed obj, we are no longer
                        // subject to races from another mutator thread.
                        if (obj != null) {
                            VTable objVT = obj.vtable;
                            if (objVT != lastVT && objVT != destVT) {
                                lastVT = objVT;
                                // do cast check
                                if(!VTable.isValidAssignment
                                   (destVT.vtableType, objVT.vtableType)) {
                                    throw new InvalidCastException("InvalidCast_DownCastArrayElement");
                                }
                            }
                        }
                        VTable.Assert(destArray.vtable.arrayOf !=
                                      StructuralType.Struct);
                        if (destArray.vtable.arrayOf == 
                            StructuralType.Reference) {
#if REFERENCE_COUNTING_GC
                            GCs.ReferenceCountingCollector.
                                IncrementRefCount(obj);
                            UIntPtr dstAddr =
                                destArrayPtr[i-srcIndex+destIndex];
                            Object dst = Magic.fromAddress(dstAddr);
                            GCs.ReferenceCountingCollector.
                                DecrementRefCount(dst);
                            destArrayPtr[i - srcIndex + destIndex] = objAddress;
#elif DEFERRED_REFERENCE_COUNTING_GC
                            GCs.DeferredReferenceCountingCollector.
                                IncrementRefCount(obj);
                            UIntPtr dstAddr =
                                destArrayPtr[i-srcIndex+destIndex];
                            Object dst = Magic.fromAddress(dstAddr);
                            GCs.DeferredReferenceCountingCollector.
                                DecrementRefCount(dst);
                            destArrayPtr[i - srcIndex + destIndex] = objAddress;
#else
                            UIntPtr *elementPtr =
                                destArrayPtr + i - srcIndex + destIndex;
                            Barrier.StoreIndirect(elementPtr, obj);
#endif // REFERENCE_COUNTING_GC
                        }
                        else {
                            destArrayPtr[i - srcIndex + destIndex] = objAddress;
                        }
                        // N.B. CLR uses layers of #defines/methods to do this
                        // assignment, starting with SetObjectReference
                    }
                }
            }
        }

        private static void BoxEachElement(Array sourceArray, int srcIndex,
                                           Array destArray, int destIndex,
                                           int len) {
            // For now, use this silly implementation that leans on
            // SetValue to do the right thing.
            for (int i = 0; i < len; ++i) {
                destArray.SetValue(sourceArray.GetValue(srcIndex + i), destIndex + i);
            }
        }

        private static void UnBoxEachElement(Array sourceArray, int srcIndex,
                                             Array destArray, int destIndex,
                                             int len, bool castEachElement) {
            // For now, use this silly implementation that leans on
            // SetValue to do the right thing.
            for (int i = 0; i < len; ++i) {
                destArray.SetValue(sourceArray.GetValue(srcIndex + i), destIndex + i);
            }
        }

        private static void PrimitiveWiden(Array sourceArray, int srcIndex,
                                           Array destArray, int destIndex,
                                           int len) {
            throw new Exception("System.Array.PrimitiveWiden not implemented in Bartok!");
        }

        // Copies length elements from sourceArray, starting at index 0, to
        // destinationArray, starting at index 0.
        //
        //| <include path='docs/doc[@for="Array.Copy"]/*' />
        public static void Copy(Array sourceArray, Array destinationArray, int length)
        {
            if (sourceArray == null)
                throw new ArgumentNullException("sourceArray");
            if (destinationArray == null)
                throw new ArgumentNullException("destinationArray");
            Copy(sourceArray, sourceArray.GetLowerBound(0), destinationArray, destinationArray.GetLowerBound(0), length);
        }

        // Copies length elements from sourceArray, starting at sourceIndex, to
        // destinationArray, starting at destinationIndex.
        //
        //| <include path='docs/doc[@for="Array.Copy1"]/*' />


        //| <include path='docs/doc[@for="Array.Copy2"]/*' />
        public static void Copy(Array sourceArray, Array destinationArray, long length)
        {
            if (length > Int32.MaxValue || length < Int32.MinValue)
                throw new ArgumentOutOfRangeException("length", "ArgumentOutOfRange_HugeArrayNotSupported");

            Array.Copy(sourceArray, destinationArray, (int) length);
        }

        //| <include path='docs/doc[@for="Array.Copy3"]/*' />
        public unsafe static void Copy(Array sourceArray, int sourceIndex,
                                       Array destinationArray,
                                       int destinationIndex, int length) {
            if (sourceArray == null) {
                throw new ArgumentNullException("sourceArray");
            }
            if (destinationArray == null) {
                throw new ArgumentNullException("destinationArray");
            }
            if (sourceArray.Rank != destinationArray.Rank) {
                throw new RankException("Ranks must match");
            }

            bool castEachElement = false;
            bool boxEachElement = false;
            bool unboxEachElement = false;
            bool primitiveWiden = false;

            AssignArray r;

            // Small perf optimization - we copy from one portion of an array
            // back to itself a lot when resizing collections, etc.  The cost of
            // doing the type checking is significant for copying small numbers
            // of bytes (~half of the time for copying 1 byte within one array
            // from element 0 to element 1).
            if (sourceArray == destinationArray) {
                r = AssignArray.WillWork;
            }
            else {
                r = CanAssignArrayType(sourceArray, destinationArray);
            }

            // Specialized vector copy

            // Undo support adds logging to array copies which can trigger GCs
            // at inopportune times so for now we use the specialized copy
            // routine when possible for correctness.
            // BUGBUG: arraycopy of struct + logging may lose GC information

            if (r == AssignArray.WillWork
                && sourceArray.IsVector
                && (sourceArray.vtable.arrayOf != StructuralType.Struct)) {
                VectorCopy(sourceArray,sourceIndex,destinationArray,
                           destinationIndex,length);
                return;
            }
            else {
                    switch (r) {
                      case AssignArray.WrongType:
                        throw new ArrayTypeMismatchException("ArrayTypeMismatch_CantAssignType");
                      case AssignArray.MustCast:
                        castEachElement = true;
                        break;
                      case AssignArray.WillWork:
                        break;
                      case AssignArray.BoxValueClassOrPrimitive:
                        boxEachElement = true;
                        break;
                      case AssignArray.UnboxValueClassOrPrimitive:
                        castEachElement = true;
                        unboxEachElement = true;
                        break;
                      case AssignArray.PrimitiveWiden:
                        primitiveWiden = true;
                        break;
                      default:
                        VTable.NotReached("Fell through switch in Array.Copy!");
                        break;
                    }
                }
            if (length < 0) {
                throw new ArgumentOutOfRangeException("length", "ArgumentOutOfRange_NeedNonNegNum");
            }

            int sourceLower = sourceArray.GetLowerBound(0);
            int destinationLower = destinationArray.GetLowerBound(0);
            if (sourceIndex < sourceLower ||
                sourceIndex + length > sourceLower + sourceArray.Length) {
                throw new ArgumentException("Illegal range from sourceArray");
            }
            if (destinationIndex < destinationLower ||
                destinationIndex + length > destinationLower + destinationArray.Length) {
                throw new ArgumentException("Illegal range from destinationArray");
            }

            if (length > 0) {
                VTable.Assert(!boxEachElement || !castEachElement);
                if (unboxEachElement) {
                    UnBoxEachElement(sourceArray, sourceIndex - sourceLower,
                                     destinationArray,
                                     destinationIndex - destinationLower,
                                     length, castEachElement);
                }
                else if (boxEachElement) {
                    BoxEachElement(sourceArray, sourceIndex - sourceLower,
                                   destinationArray,
                                   destinationIndex - destinationLower, length);
                }
                else if (castEachElement) {
                    VTable.Assert(!unboxEachElement);   // handled above
                    CastCheckEachElement(sourceArray, sourceIndex - sourceLower,
                                         destinationArray,
                                         destinationIndex - destinationLower,
                                         length);
                }
                else if (primitiveWiden) {
                    PrimitiveWiden(sourceArray, sourceIndex - sourceLower,
                                   destinationArray,
                                   destinationIndex - destinationLower, length);
                }
                else {
#if !REFERENCE_COUNTING_GC && !DEFERRED_REFERENCE_COUNTING_GC
                    Barrier.ArrayCopy(sourceArray,
                                           sourceIndex - sourceLower,
                                           destinationArray,
                                           destinationIndex - destinationLower,
                                           length);
#else
                    fixed (int *sourceFieldPtr = &sourceArray.field1) {
                        fixed (int *dstFieldPtr = &destinationArray.field1) {
                            byte* src = (byte*) sourceArray.GetFirstElementAddress(sourceFieldPtr);
                            byte* dst = (byte*) destinationArray.GetFirstElementAddress(dstFieldPtr);
                            int size = sourceArray.vtable.arrayElementSize;
                            Buffer.MoveMemory(dst + ((destinationIndex - destinationLower)*size),
                                              src + ((sourceIndex - sourceLower)*size),
                                              length*size);
                        }
                    }
#endif
                }
            }
        }

        // Sets length elements in array to 0 (or null for Object arrays), starting
        // at index.
        //
        //| <include path='docs/doc[@for="Array.Clear"]/*' />
        public unsafe static void Clear(Array array, int index, int length) {
            // cannot pass null for array
            if (array == null) {
                throw new ArgumentNullException("array", "ArgumentNull_Array");
            }

            // array bounds checking
            int lb = array.GetLowerBound(0);
            // are the first two redundant or is there an overflow issue?
            if (index < lb || (index - lb) < 0 || length < 0) {
                throw new IndexOutOfRangeException();
            }
            if (index - lb > array.Length - length) {
                throw new IndexOutOfRangeException();
            }

            if (length > 0) {
                fixed (int *fieldPtr = &array.field1) {
                    byte* arrayPtr = (byte*)
                        array.GetFirstElementAddress(fieldPtr);
                    int size = array.vtable.arrayElementSize;
                    VTable.Assert(size >= 1);
                    // REVIEW: what about structs?
                    VTable.Assert(size <= 8);
                    Buffer.ZeroMemory(arrayPtr + (index-lb) * size,
                                      length * size);
                }
            }
        }

        // The various Get values...
        //| <include path='docs/doc[@for="Array.GetValue"]/*' />
        public Object GetValue(params int[] indices)
        {
            if (indices == null)
                throw new ArgumentNullException("indices");
            if (Rank != indices.Length)
                throw new ArgumentException("Arg_RankIndices");
            return InternalGetValueEx(indices);
        }

        //| <include path='docs/doc[@for="Array.GetValue1"]/*' />
        public Object GetValue(int index)
        {
            if (Rank != 1)
                throw new ArgumentException("Arg_Need1DArray");
            return InternalGetValue(index,0,0);
        }

        //| <include path='docs/doc[@for="Array.GetValue2"]/*' />
        public Object GetValue(int index1, int index2)
        {
            if (Rank != 2)
                throw new ArgumentException("Arg_Need2DArray");
            return InternalGetValue(index1,index2,0);
        }

        //| <include path='docs/doc[@for="Array.GetValue3"]/*' />
        public Object GetValue(int index1, int index2, int index3)
        {
            if (Rank != 3)
                throw new ArgumentException("Arg_Need3DArray");
            return InternalGetValue(index1,index2,index3);
        }

        //| <include path='docs/doc[@for="Array.GetValue4"]/*' />
        public Object GetValue(long index)
        {
            if (index > Int32.MaxValue || index < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index", "ArgumentOutOfRange_HugeArrayNotSupported");

            return this.GetValue((int) index);
        }

        //| <include path='docs/doc[@for="Array.GetValue5"]/*' />
        public Object GetValue(long index1, long index2)
        {
            if (index1 > Int32.MaxValue || index1 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index1", "ArgumentOutOfRange_HugeArrayNotSupported");
            if (index2 > Int32.MaxValue || index2 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index2", "ArgumentOutOfRange_HugeArrayNotSupported");

            return this.GetValue((int) index1, (int) index2);
        }

        //| <include path='docs/doc[@for="Array.GetValue6"]/*' />
        public Object GetValue(long index1, long index2, long index3)
        {
            if (index1 > Int32.MaxValue || index1 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index1", "ArgumentOutOfRange_HugeArrayNotSupported");
            if (index2 > Int32.MaxValue || index2 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index2", "ArgumentOutOfRange_HugeArrayNotSupported");
            if (index3 > Int32.MaxValue || index3 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index3", "ArgumentOutOfRange_HugeArrayNotSupported");

            return this.GetValue((int) index1, (int) index2, (int) index3);
        }

        //| <include path='docs/doc[@for="Array.GetValue7"]/*' />
        public Object GetValue(params long[] indices)
        {
            int[] intIndices = new int[indices.Length];

            for (int i = 0; i < indices.Length; ++i) {
                long index = indices[i];
                if (index > Int32.MaxValue || index < Int32.MinValue)
                    throw new ArgumentOutOfRangeException("index", "ArgumentOutOfRange_HugeArrayNotSupported");
                intIndices[i] = (int) index;
            }

            return this.GetValue(intIndices);
        }


        //| <include path='docs/doc[@for="Array.SetValue"]/*' />
        public void SetValue(Object value,int index)
        {
            if (Rank != 1)
                throw new ArgumentException("Arg_Need1DArray");
            InternalSetValue(value,index,0,0);
        }

        //| <include path='docs/doc[@for="Array.SetValue1"]/*' />
        public void SetValue(Object value,int index1, int index2)
        {
            if (Rank != 2)
                throw new ArgumentException("Arg_Need2DArray");
            InternalSetValue(value,index1,index2,0);
        }

        //| <include path='docs/doc[@for="Array.SetValue2"]/*' />
        public void SetValue(Object value,int index1, int index2, int index3)
        {
            if (Rank != 3)
                throw new ArgumentException("Arg_Need3DArray");
            InternalSetValue(value,index1,index2,index3);
        }

        //| <include path='docs/doc[@for="Array.SetValue3"]/*' />
        public void SetValue(Object value,params int[] indices)
        {
            if (indices == null)
                throw new ArgumentNullException("indices");
            if (Rank != indices.Length)
                throw new ArgumentException("Arg_RankIndices");
            InternalSetValueEx(value,indices);
        }

        //| <include path='docs/doc[@for="Array.SetValue4"]/*' />
        public void SetValue(Object value, long index)
        {
            if (index > Int32.MaxValue || index < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index", "ArgumentOutOfRange_HugeArrayNotSupported");

            this.SetValue(value, (int) index);
        }

        //| <include path='docs/doc[@for="Array.SetValue5"]/*' />
        public void SetValue(Object value, long index1, long index2)
        {
            if (index1 > Int32.MaxValue || index1 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index1", "ArgumentOutOfRange_HugeArrayNotSupported");
            if (index2 > Int32.MaxValue || index2 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index2", "ArgumentOutOfRange_HugeArrayNotSupported");

            this.SetValue(value, (int) index1, (int) index2);
        }

        //| <include path='docs/doc[@for="Array.SetValue6"]/*' />
        public void SetValue(Object value, long index1, long index2, long index3)
        {
            if (index1 > Int32.MaxValue || index1 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index1", "ArgumentOutOfRange_HugeArrayNotSupported");
            if (index2 > Int32.MaxValue || index2 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index2", "ArgumentOutOfRange_HugeArrayNotSupported");
            if (index3 > Int32.MaxValue || index3 < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index3", "ArgumentOutOfRange_HugeArrayNotSupported");

            this.SetValue(value, (int) index1, (int) index2, (int) index3);
        }

        //| <include path='docs/doc[@for="Array.SetValue7"]/*' />
        public void SetValue(Object value, params long[] indices)
        {
            int[] intIndices = new int[indices.Length];

            for (int i = 0; i < indices.Length; ++i) {
                long index = indices[i];
                if (index > Int32.MaxValue || index < Int32.MinValue)
                    throw new ArgumentOutOfRangeException("index", "ArgumentOutOfRange_HugeArrayNotSupported");
                intIndices[i] = (int) index;
            }

            this.SetValue(value, intIndices);
        }

        // These functions are provided to help device drivers.
        //
        [CLSCompliant(false)]
        public unsafe UIntPtr AddressOfContent()
        {
            if (!IsVector) {
                return UIntPtr.Zero;
            }

            // This operation is only legal on a pinned object!
            UIntPtr addr = UIntPtr.Zero;
            fixed (int *fieldPtr = &field1) {
                addr = (UIntPtr)GetFirstElementAddress(fieldPtr);
            }
            return addr;
        }

        [CLSCompliant(false)]
        public UIntPtr SizeOfContent()
        {
            if (!IsVector) {
                return UIntPtr.Zero;
            }
            return (UIntPtr)(GetLengthVector() * vtable.arrayElementSize);
        }

        // This is the set of native routines that implement the real
        //  Get/Set Value.  The arguments have been verified that they exist
        //  before we get to this point.
        //| <include path='docs/doc[@for="Array.GetLength"]/*' />
        public int GetLength(int dimension) {
            if (IsVector) {
                return GetLengthVector();
            }
            else {
                return GetLengthRectangleArray(dimension);
            }
        }

        //| <include path='docs/doc[@for="Array.Length"]/*' />
        public int Length {
            get {
                if (IsVector) {
                    return GetLengthVector();
                }
                else {
                    return GetLengthRectangleArray();
                }
            }
        }

        //| <include path='docs/doc[@for="Array.LongLength"]/*' />
        public long LongLength {
            get { return Length; }
        }

        //| <include path='docs/doc[@for="Array.GetLongLength"]/*' />
        public long GetLongLength(int dimension) {
            return GetLength(dimension);
        }

        //| <include path='docs/doc[@for="Array.Rank"]/*' />
        public int Rank {
            get {
                if (IsVector) {
                    return 1;
                }
                else {
                    return RankRectangleArray;
                }
            }
        }

        // This is to be used only when allocating a vector!
        [Inline]
        internal void InitializeVectorLength(int numElements) {
            this.field1 = numElements;
        }

        // This is to be used only when allocating an array!
        [Inline]
        internal void InitializeArrayLength(int rank, int totalElements) {
            this.field1 = rank;
            this.field2 = totalElements;
        }

        internal bool IsVector {
            get {
                // REVIEW: information can be closer
                return this.vtable.vtableType.IsVector;
            }
        }
        private bool IsRectangleArray {
            get {
                // REVIEW: information can be closer
                return this.vtable.vtableType.IsRectangleArray;
            }
        }

        //| <include path='docs/doc[@for="Array.GetUpperBound"]/*' />
        public int GetUpperBound(int dimension) {
            if (dimension >= Rank) {
                throw new IndexOutOfRangeException("GetUpperBound dimension");
            }
            return GetLowerBound(dimension) + GetLength(dimension) - 1;
        }

        //| <include path='docs/doc[@for="Array.GetLowerBound"]/*' />
        public int GetLowerBound(int dimension) {
            if (dimension >= Rank) {
                throw new IndexOutOfRangeException("GetLowerBound dimension");
            }
            if (IsVector) { // zero - based
                return 0;
            }
            // IsRectangleArray() == true
            return GetLowerBoundRectangleArray(dimension);
        }

        // Returns an object appropriate for synchronizing access to this
        // Array.
        //| <include path='docs/doc[@for="Array.SyncRoot"]/*' />
        public virtual Object SyncRoot
        { get { return this; } }

        // Is this Array read-only?
        //| <include path='docs/doc[@for="Array.IsReadOnly"]/*' />
        public virtual bool IsReadOnly
        { get { return false; } }

        //| <include path='docs/doc[@for="Array.IsFixedSize"]/*' />
        public virtual bool IsFixedSize {
            get { return true; }
        }

        // Is this Array synchronized (i.e., thread-safe)?  If you want a synchronized
        // collection, you can use SyncRoot as an object to synchronize your
        // collection with.  You could also call GetSynchronized()
        // to get a synchronized wrapper around the Array.
        //| <include path='docs/doc[@for="Array.IsSynchronized"]/*' />
        public virtual bool IsSynchronized
        { get { return false; } }

        // Make a new array which is a deep copy of the original array.
        //
        //| <include path='docs/doc[@for="Array.Clone"]/*' />
        public virtual Object Clone()
        {
            return MemberwiseClone();
        }

        // Searches an array for a given element using a binary search algorithm.
        // Elements of the array are compared to the search value using the
        // IComparable interface, which must be implemented by all elements
        // of the array and the given search value. This method assumes that the
        // array is already sorted according to the IComparable interface;
        // if this is not the case, the result will be incorrect.
        //
        // The method returns the index of the given value in the array. If the
        // array does not contain the given value, the method returns a negative
        // integer. The bitwise complement operator (~) can be applied to a
        // negative result to produce the index of the first element (if any) that
        // is larger than the given search value.
        //
        //| <include path='docs/doc[@for="Array.BinarySearch"]/*' />
        public static int BinarySearch(Array array, Object value) {
            if (array == null)
                throw new ArgumentNullException("array");
            int lb = array.GetLowerBound(0);
            return BinarySearch(array, lb, array.Length, value, null);
        }

        // Searches a section of an array for a given element using a binary search
        // algorithm. Elements of the array are compared to the search value using
        // the IComparable interface, which must be implemented by all
        // elements of the array and the given search value. This method assumes
        // that the array is already sorted according to the IComparable
        // interface; if this is not the case, the result will be incorrect.
        //
        // The method returns the index of the given value in the array. If the
        // array does not contain the given value, the method returns a negative
        // integer. The bitwise complement operator (~) can be applied to a
        // negative result to produce the index of the first element (if any) that
        // is larger than the given search value.
        //
        //| <include path='docs/doc[@for="Array.BinarySearch1"]/*' />
        public static int BinarySearch(Array array, int index, int length, Object value) {
            return BinarySearch(array, index, length, value, null);
        }

        // Searches an array for a given element using a binary search algorithm.
        // Elements of the array are compared to the search value using the given
        // IComparer interface. If comparer is null, elements of the
        // array are compared to the search value using the IComparable
        // interface, which in that case must be implemented by all elements of the
        // array and the given search value. This method assumes that the array is
        // already sorted; if this is not the case, the result will be incorrect.
        //
        // The method returns the index of the given value in the array. If the
        // array does not contain the given value, the method returns a negative
        // integer. The bitwise complement operator (~) can be applied to a
        // negative result to produce the index of the first element (if any) that
        // is larger than the given search value.
        //
        //| <include path='docs/doc[@for="Array.BinarySearch2"]/*' />
        public static int BinarySearch(Array array, Object value, IComparer comparer) {
            if (array == null)
                throw new ArgumentNullException("array");
            int lb = array.GetLowerBound(0);
            return BinarySearch(array, lb, array.Length, value, comparer);
        }

        // Searches a section of an array for a given element using a binary search
        // algorithm. Elements of the array are compared to the search value using
        // the given IComparer interface. If comparer is null,
        // elements of the array are compared to the search value using the
        // IComparable interface, which in that case must be implemented by
        // all elements of the array and the given search value. This method
        // assumes that the array is already sorted; if this is not the case, the
        // result will be incorrect.
        //
        // The method returns the index of the given value in the array. If the
        // array does not contain the given value, the method returns a negative
        // integer. The bitwise complement operator (~) can be applied to a
        // negative result to produce the index of the first element (if any) that
        // is larger than the given search value.
        //
        //| <include path='docs/doc[@for="Array.BinarySearch3"]/*' />
        public static int BinarySearch(Array array, int index, int length, Object value, IComparer comparer) {
            if (array == null)
                throw new ArgumentNullException("array");
            int lb = array.GetLowerBound(0);
            if (index < lb || length < 0)
                throw new ArgumentOutOfRangeException((index<lb ? "index" : "length"), "ArgumentOutOfRange_NeedNonNegNum");
            if (array.Length - index < length)
                throw new ArgumentException("Argument_InvalidOffLen");
            if (array.Rank != 1)
                throw new RankException("Rank_MultiDimNotSupported");

            if (comparer == null) comparer = Comparer.Default;
            if (comparer == Comparer.Default) {
                int retval;
                int r = TrySZBinarySearch(array, index, length, value, out retval);
                if (r != 0)
                    return retval;
            }

            int lo = index;
            int hi = index + length - 1;
            Object[] objArray = array as Object[];
            if (objArray != null) {
                while (lo <= hi) {
                    int i = (lo + hi) >> 1;
                    int c;
                    try {
                        c = comparer.Compare(objArray[i], value);
                    }
                    catch (Exception e) {
                        throw new InvalidOperationException("InvalidOperation_IComparerFailed", e);
                    }
                    if (c == 0) return i;
                    if (c < 0) {
                        lo = i + 1;
                    }
                    else {
                        hi = i - 1;
                    }
                }
            }
            else {
                while (lo <= hi) {
                    int i = (lo + hi) >> 1;
                    int c;
                    try {
                        c = comparer.Compare(array.GetValue(i), value);
                    }
                    catch (Exception e) {
                        throw new InvalidOperationException("InvalidOperation_IComparerFailed", e);
                    }
                    if (c == 0) return i;
                    if (c < 0) {
                        lo = i + 1;
                    }
                    else {
                        hi = i - 1;
                    }
                }
            }
            return ~lo;
        }

        private static int TrySZBinarySearch(Array sourceArray, int sourceIndex, int count, Object value, out int retVal) {
            // BUGBUG: was fast native primitive type method
            // returning false (0) means we couldn't handle it
            retVal = -1;
            return 0;
        }

        // CopyTo copies a collection into an Array, starting at a particular
        // index into the array.
        //
        // This method is to support the ICollection interface, and calls
        // Array.Copy internally.  If you aren't using ICollection explicitly,
        // call Array.Copy to avoid an extra indirection.
        //
        //| <include path='docs/doc[@for="Array.CopyTo"]/*' />
        public virtual void CopyTo(Array array, int index)
        {
            if (array != null && array.Rank != 1)
                throw new ArgumentException("Arg_RankMultiDimNotSupported");
            // Note: Array.Copy throws a RankException and we want a consistent ArgumentException for all the IList CopyTo methods.
            Array.Copy(this, GetLowerBound(0), array, index, Length);
        }

        //| <include path='docs/doc[@for="Array.CopyTo1"]/*' />
        public virtual void CopyTo(Array array, long index)
        {
            if (index > Int32.MaxValue || index < Int32.MinValue)
                throw new ArgumentOutOfRangeException("index", "ArgumentOutOfRange_HugeArrayNotSupported");

            this.CopyTo(array, (int) index);
        }


        // GetEnumerator returns an IEnumerator over this Array.
        //
        // Currently, only one dimensional arrays are supported.
        //
        //| <include path='docs/doc[@for="Array.GetEnumerator"]/*' />
        public virtual IEnumerator GetEnumerator()
        {
            int lowerBound = GetLowerBound(0);
            if (Rank == 1 && lowerBound == 0)
                return new SZArrayEnumerator(this);
            else
                return new ArrayEnumerator(this, lowerBound, Length);
        }

        // Returns the index of the first occurrence of a given value in an array.
        // The array is searched forwards, and the elements of the array are
        // compared to the given value using the Object.Equals method.
        //
        //| <include path='docs/doc[@for="Array.IndexOf"]/*' />
        public static int IndexOf(Array array, Object value) {
            if (array == null)
                throw new ArgumentNullException("array");
            int lb = array.GetLowerBound(0);
            return IndexOf(array, value, lb, array.Length);
        }

        // Returns the index of the first occurrence of a given value in a range of
        // an array. The array is searched forwards, starting at index
        // startIndex and ending at the last element of the array. The
        // elements of the array are compared to the given value using the
        // Object.Equals method.
        //
        //| <include path='docs/doc[@for="Array.IndexOf1"]/*' />
        public static int IndexOf(Array array, Object value, int startIndex) {
            if (array == null)
                throw new ArgumentNullException("array", "ArgumentNull_Array");
            int lb = array.GetLowerBound(0);
            return IndexOf(array, value, startIndex, array.Length - startIndex + lb);
        }

        // Returns the index of the first occurrence of a given value in a range of
        // an array. The array is searched forwards, starting at index
        // startIndex and up to count elements. The
        // elements of the array are compared to the given value using the
        // Object.Equals method.
        //
        //| <include path='docs/doc[@for="Array.IndexOf2"]/*' />
        public static int IndexOf(Array array, Object value, int startIndex, int count) {
            if (array == null)
                throw new ArgumentNullException("array");
            int lb = array.GetLowerBound(0);
            if (startIndex < lb || startIndex > array.Length + lb)
                throw new ArgumentOutOfRangeException("startIndex", "ArgumentOutOfRange_Index");
            if (count < 0 || count > array.Length - startIndex + lb)
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_Count");
            if (array.Rank != 1)
                throw new RankException("Rank_MultiDimNotSupported");

            // Try calling a quick native method to handle primitive types.
            int retVal;
            int r = TrySZIndexOf(array, startIndex, count, value, out retVal);
            if (r != 0)
                return retVal;

            Object[] objArray = array as Object[];
            int endIndex = startIndex + count;
            if (objArray != null) {
                if (value == null) {
                    for (int i = startIndex; i < endIndex; i++) {
                        if (objArray[i] == null) return i;
                    }
                }
                else {
                    for (int i = startIndex; i < endIndex; i++) {
                        Object obj = objArray[i];
                        if (obj != null && value.Equals(obj)) return i;
                    }
                }
            }
            else {
                // This is an array of value classes
                Debug.Assert(array.GetType().GetElementType().IsValueType, "array.GetType().GetUnderlyingType().IsValueType");
                if (value == null)
                    return -1;
                for (int i = startIndex; i < endIndex; i++) {
                    Object obj = array.GetValue(i);
                    if (obj != null && value.Equals(obj)) return i;
                }
            }
            // Return one less than the lower bound of the array.  This way,
            // for arrays with a lower bound of -1 we will not return -1 when the
            // item was not found.  And for SZArrays (the vast majority), -1 still
            // works for them.
            return lb-1;
        }

        private static int TrySZIndexOf(Array sourceArray, int sourceIndex, int count, Object value, out int retVal) {
            // BUGBUG: was fast native primitive type method
            // returning false (0) means we couldn't handle it
            retVal = -1;
            return 0;
        }

        // Returns the index of the last occurrence of a given value in an array.
        // The array is searched backwards, and the elements of the array are
        // compared to the given value using the Object.Equals method.
        //
        //| <include path='docs/doc[@for="Array.LastIndexOf"]/*' />
        public static int LastIndexOf(Array array, Object value) {
            if (array == null)
                throw new ArgumentNullException("array", "ArgumentNull_Array");
            int lb = array.GetLowerBound(0);
            return LastIndexOf(array, value, array.Length - 1 + lb, array.Length);
        }

        // Returns the index of the last occurrence of a given value in a range of
        // an array. The array is searched backwards, starting at index
        // startIndex and ending at index 0. The elements of the array are
        // compared to the given value using the Object.Equals method.
        //
        //| <include path='docs/doc[@for="Array.LastIndexOf1"]/*' />
        public static int LastIndexOf(Array array, Object value, int startIndex) {
            if (array == null)
                throw new ArgumentNullException("array");
            int lb = array.GetLowerBound(0);
            return LastIndexOf(array, value, startIndex, startIndex + 1 - lb);
        }

        // Returns the index of the last occurrence of a given value in a range of
        // an array. The array is searched backwards, starting at index
        // startIndex and counting uptocount elements. The elements of
        // the array are compared to the given value using the Object.Equals
        // method.
        //
        //| <include path='docs/doc[@for="Array.LastIndexOf2"]/*' />
        public static int LastIndexOf(Array array, Object value, int startIndex, int count) {
            if (array == null)
                throw new ArgumentNullException("array");
            if (array.Length == 0) {
                return -1;
            }
            int lb = array.GetLowerBound(0);
            if (startIndex < lb || startIndex >= array.Length + lb)
                throw new ArgumentOutOfRangeException("startIndex", "ArgumentOutOfRange_Index");
            if (count < 0)
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_Count");
            if (count > startIndex - lb + 1)
                throw new ArgumentOutOfRangeException("endIndex", "ArgumentOutOfRange_EndIndexStartIndex");
            if (array.Rank != 1)
                throw new RankException("Rank_MultiDimNotSupported");

            // Try calling a quick native method to handle primitive types.
            int retVal;
            int r = TrySZLastIndexOf(array, startIndex, count, value, out retVal);
            if (r != 0)
                return retVal;

            Object[] objArray = array as Object[];
            int endIndex = startIndex - count + 1;
            if (objArray != null) {
                if (value == null) {
                    for (int i = startIndex; i >= endIndex; i--) {
                        if (objArray[i] == null) return i;
                    }
                }
                else {
                    for (int i = startIndex; i >= endIndex; i--) {
                        Object obj = objArray[i];
                        if (obj != null && value.Equals(obj)) return i;
                    }
                }
            }
            else {
                // This is an array of value classes
                Debug.Assert(array.GetType().GetElementType().IsValueType, "array.GetType().GetUnderlyingType().IsValueType");
                if (value == null)
                    return -1;
                for (int i = startIndex; i >= endIndex; i--) {
                    Object obj = array.GetValue(i);
                    if (obj != null && value.Equals(obj)) return i;
                }
            }
            return lb-1;  // Return lb-1 for arrays with negative lower bounds.
        }

        private static int TrySZLastIndexOf(Array sourceArray, int sourceIndex, int count, Object value, out int retVal) {
            // BUGBUG: was fast native primitive type method
            // returning false (0) means we couldn't handle it
            retVal = -1;
            return 0;
        }

        // Reverses all elements of the given array. Following a call to this
        // method, an element previously located at index i will now be
        // located at index length - i - 1, where length is the
        // length of the array.
        //
        //| <include path='docs/doc[@for="Array.Reverse"]/*' />
        public static void Reverse(Array array) {
            if (array == null)
                throw new ArgumentNullException("array", "ArgumentNull_Array");
            Reverse(array, array.GetLowerBound(0), array.Length);
        }

        // Reverses the elements in a range of an array. Following a call to this
        // method, an element in the range given by index and count
        // which was previously located at index i will now be located at
        // index index + (index + count - i - 1).
        //
        //| <include path='docs/doc[@for="Array.Reverse1"]/*' />
        public static void Reverse(Array array, int index, int length) {
            if (array == null)
                throw new ArgumentNullException("array");
            if (index < array.GetLowerBound(0) || length < 0)
                throw new ArgumentOutOfRangeException((index<0 ? "index" : "length"), "ArgumentOutOfRange_NeedNonNegNum");
            if (array.Length - (index - array.GetLowerBound(0)) < length)
                throw new ArgumentException("Argument_InvalidOffLen");
            if (array.Rank != 1)
                throw new RankException("Rank_MultiDimNotSupported");

            bool r = TrySZReverse(array, index, length);
            if (r)
                return;

            int i = index;
            int j = index + length - 1;
            Object[] objArray = array as Object[];
            if (objArray != null) {
                while (i < j) {
                    Object temp = objArray[i];
                    objArray[i] = objArray[j];
                    objArray[j] = temp;
                    i++;
                    j--;
                }
            }
            else {
                while (i < j) {
                    Object temp = array.GetValue(i);
                    array.SetValue(array.GetValue(j), i);
                    array.SetValue(temp, j);
                    i++;
                    j--;
                }
            }
        }

        private static bool TrySZReverse(Array array, int index, int count) {
            // BUGBUG: was fast native primitive type method
            // returning false means we couldn't handle it
            return false;
        }

        // Sorts the elements of an array. The sort compares the elements to each
        // other using the IComparable interface, which must be implemented
        // by all elements of the array.
        //
        //| <include path='docs/doc[@for="Array.Sort"]/*' />
        public static void Sort(Array array) {
            if (array == null)
                throw new ArgumentNullException("array", "ArgumentNull_Array");
            Sort(array, null, array.GetLowerBound(0), array.Length, null);
        }

        // Sorts the elements of two arrays based on the keys in the first array.
        // Elements in the keys array specify the sort keys for
        // corresponding elements in the items array. The sort compares the
        // keys to each other using the IComparable interface, which must be
        // implemented by all elements of the keys array.
        //
        //| <include path='docs/doc[@for="Array.Sort1"]/*' />
        public static void Sort(Array keys, Array items) {
            if (keys == null)
                throw new ArgumentNullException("keys");
            Sort(keys, items, keys.GetLowerBound(0), keys.Length, null);
        }

        // Sorts the elements in a section of an array. The sort compares the
        // elements to each other using the IComparable interface, which
        // must be implemented by all elements in the given section of the array.
        //
        //| <include path='docs/doc[@for="Array.Sort2"]/*' />
        public static void Sort(Array array, int index, int length) {
            Sort(array, null, index, length, null);
        }

        // Sorts the elements in a section of two arrays based on the keys in the
        // first array. Elements in the keys array specify the sort keys for
        // corresponding elements in the items array. The sort compares the
        // keys to each other using the IComparable interface, which must be
        // implemented by all elements of the keys array.
        //
        //| <include path='docs/doc[@for="Array.Sort3"]/*' />
        public static void Sort(Array keys, Array items, int index, int length) {
            Sort(keys, items, index, length, null);
        }

        // Sorts the elements of an array. The sort compares the elements to each
        // other using the given IComparer interface. If comparer is
        // null, the elements are compared to each other using the
        // IComparable interface, which in that case must be implemented by
        // all elements of the array.
        //
        //| <include path='docs/doc[@for="Array.Sort4"]/*' />
        public static void Sort(Array array, IComparer comparer) {
            if (array == null)
                throw new ArgumentNullException("array", "ArgumentNull_Array");
            Sort(array, null, array.GetLowerBound(0), array.Length, comparer);
        }

        // Sorts the elements of two arrays based on the keys in the first array.
        // Elements in the keys array specify the sort keys for
        // corresponding elements in the items array. The sort compares the
        // keys to each other using the given IComparer interface. If
        // comparer is null, the elements are compared to each other using
        // the IComparable interface, which in that case must be implemented
        // by all elements of the keys array.
        //
        //| <include path='docs/doc[@for="Array.Sort5"]/*' />
        public static void Sort(Array keys, Array items, IComparer comparer) {
            if (keys == null)
                throw new ArgumentNullException("keys");
            Sort(keys, items, keys.GetLowerBound(0), keys.Length, comparer);
        }

        // Sorts the elements in a section of an array. The sort compares the
        // elements to each other using the given IComparer interface. If
        // comparer is null, the elements are compared to each other using
        // the IComparable interface, which in that case must be implemented
        // by all elements in the given section of the array.
        //
        //| <include path='docs/doc[@for="Array.Sort6"]/*' />
        public static void Sort(Array array, int index, int length, IComparer comparer) {
            Sort(array, null, index, length, comparer);
        }

        // Sorts the elements in a section of two arrays based on the keys in the
        // first array. Elements in the keys array specify the sort keys for
        // corresponding elements in the items array. The sort compares the
        // keys to each other using the given IComparer interface. If
        // comparer is null, the elements are compared to each other using
        // the IComparable interface, which in that case must be implemented
        // by all elements of the given section of the keys array.
        //
        //| <include path='docs/doc[@for="Array.Sort7"]/*' />
        public static void Sort(Array keys, Array items, int index, int length, IComparer comparer) {
            if (keys == null)
                throw new ArgumentNullException("keys");
            if (keys.Rank != 1 || (items != null && items.Rank != 1))
                throw new RankException("Rank_MultiDimNotSupported");
            if (items != null && keys.GetLowerBound(0) != items.GetLowerBound(0))
                throw new ArgumentException("Arg_LowerBoundsMustMatch");
            if (index < keys.GetLowerBound(0) || length < 0)
                throw new ArgumentOutOfRangeException((length<0 ? "length" : "index"), "ArgumentOutOfRange_NeedNonNegNum");
            if (keys.Length - (index + keys.GetLowerBound(0)) < length || (items != null && index > items.Length - length))
                throw new ArgumentException("Argument_InvalidOffLen");



            if (length > 1) {
                if (comparer == Comparer.Default || comparer == null) {
                    int r = TrySZSort(keys, items, index, index + length - 1);
                    if (r != 0)
                        return;
                }

                Object[] objKeys = keys as Object[];
                Object[] objItems = null;
                if (objKeys != null)
                    objItems = items as Object[];
                if (objKeys != null && (items == null || objItems != null)) {
                    SorterObjectArray sorter = new SorterObjectArray(objKeys, objItems, comparer);
                    sorter.QuickSort(index, index + length - 1);
                }
                else {
                    SorterGenericArray sorter = new SorterGenericArray(keys, items, comparer);
                    sorter.QuickSort(index, index + length - 1);
                }
            }
        }

        private static int TrySZSort(Array keys, Array items, int left, int right) {
            // BUGBUG: was fast native primitive type method
            // returning false (0) means we couldn't handle it
            return 0;
        }

        // Private class used by the Sort methods.
        private class SorterObjectArray
        {
            private Object[] keys;
            private Object[] items;
            private IComparer comparer;


            public SorterObjectArray(Object[] keys, Object[] items, IComparer comparer) {
                if (comparer == null) comparer = Comparer.Default;
                this.keys = keys;
                this.items = items;
                this.comparer = comparer;
            }

            public virtual void QuickSort(int left, int right) {
                // Can use the much faster jit helpers for array access.
                do {
                    int i = left;
                    int j = right;
                    Object x = keys[(i + j) >> 1];
                    do {
                        // Add a try block here to detect IComparers (or their
                        // underlying IComparables, etc) that are bogus.
                        try {
                            while (comparer.Compare(keys[i], x) < 0) i++;
                            while (comparer.Compare(x, keys[j]) < 0) j--;
                        }
                        catch (IndexOutOfRangeException) {
                            throw new ArgumentException(String.Format("Arg_BogusIComparer", x, x.GetType().Name, comparer));
                        }
                        catch (Exception e) {
                            throw new InvalidOperationException("InvalidOperation_IComparerFailed", e);
                        }
                        Debug.Assert(i>=left && j<=right, "(i>=left && j<=right)  Sort failed - Is your IComparer bogus?");
                        if (i > j) break;
                        if (i < j) {
                            Object key = keys[i];
                            keys[i] = keys[j];
                            keys[j] = key;
                            if (items != null) {
                                Object item = items[i];
                                items[i] = items[j];
                                items[j] = item;
                            }
                        }
                        i++;
                        j--;
                    } while (i <= j);
                    if (j - left <= right - i) {
                        if (left < j) QuickSort(left, j);
                        left = i;
                    }
                    else {
                        if (i < right) QuickSort(i, right);
                        right = j;
                    }
                } while (left < right);
            }
        }

        // Private class used by the Sort methods for instances of System.Array.
        // This is slower than the one for Object[], since we can't use the JIT helpers
        // to access the elements.  We must use GetValue & SetValue.
        private class SorterGenericArray
        {
            private Array keys;
            private Array items;
            private IComparer comparer;

            public SorterGenericArray(Array keys, Array items, IComparer comparer) {
                if (comparer == null) comparer = Comparer.Default;
                this.keys = keys;
                this.items = items;
                this.comparer = comparer;
            }

            public virtual void QuickSort(int left, int right) {
                // Must use slow Array accessors (GetValue & SetValue)
                do {
                    int i = left;
                    int j = right;
                    Object x = keys.GetValue((i + j) >> 1);
                    do {
                        // Add a try block here to detect IComparers (or their
                        // underlying IComparables, etc) that are bogus.
                        try {
                            while (comparer.Compare(keys.GetValue(i), x) < 0) i++;
                            while (comparer.Compare(x, keys.GetValue(j)) < 0) j--;
                        }
                        catch (IndexOutOfRangeException) {
                            throw new ArgumentException(String.Format("Arg_BogusIComparer", x, x.GetType().Name, comparer));
                        }
                        catch (Exception e) {
                            throw new InvalidOperationException("InvalidOperation_IComparerFailed", e);
                        }
                        Debug.Assert(i>=left && j<=right, "(i>=left && j<=right)  Sort failed - Is your IComparer bogus?");
                        if (i > j) break;
                        if (i < j) {
                            Object key = keys.GetValue(i);
                            keys.SetValue(keys.GetValue(j), i);
                            keys.SetValue(key, j);
                            if (items != null) {
                                Object item = items.GetValue(i);
                                items.SetValue(items.GetValue(j), i);
                                items.SetValue(item, j);
                            }
                        }
                        i++;
                        j--;
                    } while (i <= j);
                    if (j - left <= right - i) {
                        if (left < j) QuickSort(left, j);
                        left = i;
                    }
                    else {
                        if (i < right) QuickSort(i, right);
                        right = j;
                    }
                } while (left < right);
            }
        }

        private class SZArrayEnumerator : IEnumerator, ICloneable
        {
            private Array _array;
            private int _index;
            private int _endIndex; // cache array length, since it's a little slow.

            internal SZArrayEnumerator(Array array) {
                Debug.Assert(array.Rank == 1 && array.GetLowerBound(0) == 0, "SZArrayEnumerator only works on single dimension arrays w/ a lower bound of zero.");
                _array = array;
                _index = -1;
                _endIndex = array.Length;
            }

            public virtual Object Clone()
            {
                return MemberwiseClone();
            }

            public virtual bool MoveNext() {
                if (_index < _endIndex) {
                    _index++;
                    return (_index < _endIndex);
                }
                return false;
            }

            public virtual Object Current {
                get {
                    if (_index < 0) throw new InvalidOperationException("InvalidOperation_EnumNotStarted");
                    if (_index >= _endIndex) throw new InvalidOperationException("InvalidOperation_EnumEnded");
                    return _array.GetValue(_index);
                }
            }

            public virtual void Reset() {
                _index = -1;
            }
        }

        private class ArrayEnumerator : IEnumerator, ICloneable
        {
            private Array array;
            private int index;
            private int endIndex;
            private int startIndex;    // Save for Reset.
            private int[] _indices;    // The current position in a multidim array
            private bool _complete;

            internal ArrayEnumerator(Array array, int index, int count) {
                this.array = array;
                this.index = index - 1;
                startIndex = index;
                endIndex = index + count;
                _indices = new int[array.Rank];
                int checkForZero = 1;  // Check for dimensions of size 0.
                for (int i = 0; i < array.Rank; i++) {
                    _indices[i] = array.GetLowerBound(i);
                    checkForZero *= array.GetLength(i);
                }
                // To make MoveNext simpler, decrement least significant index.
                _indices[_indices.Length-1]--;
                _complete = (checkForZero == 0);
            }

            private void IncArray() {
                // This method advances us to the next valid array index,
                // handling all the multiple dimension & bounds correctly.
                // Think of it like an odometer in your car - we start with
                // the last digit, increment it, and check for rollover.  If
                // it rolls over, we set all digits to the right and including
                // the current to the appropriate lower bound.  Do these overflow
                // checks for each dimension, and if the most significant digit
                // has rolled over it's upper bound, we're done.
                //
                // @TODO: Figure out if this slower and/or more complex than
                // sticking a private method on Array to access it as a flat
                // structure (ie, reference from 0 to length, ignoring bounds &
                // dimensions).
                int rank = array.Rank;
                _indices[rank-1]++;
                for (int dim = rank - 1; dim >= 0; dim--) {
                    if (_indices[dim] > array.GetUpperBound(dim)) {
                        if (dim == 0) {
                            _complete = true;
                            break;
                        }
                        for (int j = dim; j < rank; j++)
                            _indices[j] = array.GetLowerBound(j);
                        _indices[dim-1]++;
                    }
                }
            }

            public virtual Object Clone()
            {
                return MemberwiseClone();
            }

            public virtual bool MoveNext() {
                if (_complete) {
                    index = endIndex;
                    return false;
                }
                index++;
                IncArray();
                return !_complete;
            }

            public virtual Object Current {
                get {
                    if (index < startIndex) throw new InvalidOperationException("InvalidOperation_EnumNotStarted");
                    if (_complete) throw new InvalidOperationException("InvalidOperation_EnumEnded");
                    return array.GetValue(_indices);
                }
            }

            public virtual void Reset() {
                index = startIndex - 1;
                int checkForZero = 1;
                for (int i = 0; i < array.Rank; i++) {
                    _indices[i] = array.GetLowerBound(i);
                    checkForZero *= array.GetLength(i);
                }
                _complete = (checkForZero == 0);
                // To make MoveNext simpler, decrement least significant index.
                _indices[_indices.Length-1]--;
            }
        }


        // if this is an array of value classes and that value class has a default constructor
        // then this calls this default constructor on every element in the value class array.
        // otherwise this is a no-op.  Generally this method is called automatically by the compiler
        //| <include path='docs/doc[@for="Array.Initialize"]/*' />
        public unsafe void Initialize()
        {
            // if it is an array of struct, we need to call the default
            // constructor for the struct
            if (this.vtable.arrayOf == StructuralType.Struct) {
                RuntimeType runtimeType = this.vtable.arrayElementClass.vtableType;
                UIntPtr fn = runtimeType.ctor;
                if (fn == UIntPtr.Zero)
                    return;

                int total = 0;
                for (int i = 0; i < Rank; i++) {
                    total += GetLength(i);
                }
                fixed(int *srcField = &this.field1) {
                    UIntPtr elementAddress =
                        new UIntPtr(this.GetFirstElementAddress(srcField));
                    UIntPtr elementSize =
                        new UIntPtr(this.vtable.arrayElementSize);
                    for (int i = 0; i < total; i++) {
                        Magic.calli(runtimeType.ctor, elementAddress);
                        elementAddress = elementAddress + elementSize;
                    }
                }
            }
        }

        private int RankRectangleArray {
            get {
                return field1;
            }
        }
        private int Length0RectangleArray {
            get {
                return field4;
            }
        }
        // PRE: this fixed
        // REVIEW: return type
        internal unsafe void* GetFirstDimInfoRectangleArray() {
            fixed(int* ptr = &field3) {
                return (void*)ptr;
            }
        }

        private unsafe int GetLowerBoundRectangleArray(int dimension) {
            fixed(int* ptr = &field3) {
                return ptr[2*dimension];
            }
        }

        private int GetLengthVector() {
            return field1;
        }

        private unsafe int GetLengthRectangleArray(int dimension) {
            fixed(int* ptr = &field3) {
                return ptr[2*dimension+1];
            }
        }

        private unsafe int GetLengthRectangleArray() {
            return field2;
        }

        // PRE: this fixed
        // REVIEW: return type
        internal unsafe void* GetFirstElementAddress(int *field1Addr) {
            return (void*)(((byte*)field1Addr) + this.vtable.baseLength -
                           (PreHeader.Size + PostHeader.Size));
        }

        // Calculates the offset from the first element of the array to the
        // desired element.  This offset is a count -- that is, it does not take
        // the size of the elements into account (e.g. int_array[2] would lead
        // to 2, not 2*sizeof(int) = 8).
        private unsafe int InternalGetOffset(int[] indices) {
            if (IsVector) {
                return indices[0];
            }
            else {
                int rank = RankRectangleArray;
                int dwOffset = 0;
                int dwMultiplier = 1;

                fixed(int* ptr = &field3) {
                    for (int i = rank - 1; i >= 0; i--) {
                        int dwIndex = indices[i] - ptr[2*i];

                        if (dwIndex >= ptr[2*i + 1]) {
                            throw new IndexOutOfRangeException();
                        }

                        dwOffset += dwIndex * dwMultiplier;
                        dwMultiplier *= ptr[2*i+1];
                    }
                    return dwOffset;
                }
            }
        }

        // See comment by the other InternalGetOffset
        private unsafe int InternalGetOffset(int index1, int index2,
                                             int index3) {
            if (IsVector) {
                VTable.Assert(index2 == 0);
                VTable.Assert(index3 == 0);
                return index1;
            }
            else {
                int rank = RankRectangleArray;
                int dwOffset = 0;
                int dwMultiplier = 1;

                VTable.Assert(rank <= 3);

                fixed(int* ptr = &field3) {
                    for (int i = rank - 1; i >= 0; i--) {
                        int dwIndex;
                        if (i == 2) {
                            dwIndex = index3 - ptr[2*i];
                        }
                        else if(i == 1) {
                            dwIndex = index2 - ptr[2*i];
                        }
                        else {
                            dwIndex = index1 - ptr[2*i];
                        }

                        if (dwIndex >= ptr[2*i + 1]) {
                            throw new IndexOutOfRangeException();
                        }
                        dwOffset += dwIndex * dwMultiplier;
                        dwMultiplier *= ptr[2*i+1];
                    }
                    return dwOffset;
                }
            }
        }

        // Given an array (this), a pointer to its first element (EA), and
        // the offset (count of elements -- see InternalGetOffset comment for
        // what this means), compute the desired element's address, get the
        // value, box it if necessary, and return it
        // PRE: 'this' fixed
        private unsafe Object InternalGetValueHelper(byte *EA, int dwOffset) {
            int arrayElementSize = this.vtable.arrayElementSize;
            EA += dwOffset * arrayElementSize;

            // now we have the address of the array element
            // if it's already an object, return it
            if (this.vtable.arrayOf == StructuralType.Reference) {
                return Magic.fromAddress(*(UIntPtr*)EA);
            }

            // BUGBUG: we won't have the enum type anywhere!

            Object result;
            switch (this.vtable.arrayOf) {
              case StructuralType.Struct:
                // possible GC point -- but 'this' is fixed so EA won't get
                // invalidated

                Thread thread = Thread.CurrentThread;
                result = GC.AllocateObject(vtable.arrayElementClass);

                // HACK: depends on value being at same spot in all valuetypes
                // REVIEW: result is not fixed
                byte *dst = (byte *) Magic.addressOf(result) + 4;
                Buffer.MoveMemory(dst, EA, arrayElementSize);
                break;
              case StructuralType.Bool:
                result = *(bool*)EA;
                break;
              case StructuralType.Char:
                result = *(char*)EA;
                break;
              case StructuralType.Int8:
                result = *(sbyte*)EA;
                break;
              case StructuralType.Int16:
                result = *(short*)EA;
                break;
              case StructuralType.Int32:
                result = *(int*)EA;
                break;
              case StructuralType.Int64:
                result = *(long*)EA;
                break;
              case StructuralType.UInt8:
                result = *(byte*)EA;
                break;
              case StructuralType.UInt16:
                result = *(ushort*)EA;
                break;
              case StructuralType.UInt32:
                result = *(uint*)EA;
                break;
              case StructuralType.UInt64:
                result = *(ulong*)EA;
                break;
              case StructuralType.Float32:
                result = *(float*)EA;
                break;
              case StructuralType.Float64:
                result = *(double*)EA;
                break;
              default:
                VTable.Assert(false, "unreachable array get box");
                return null;
            }
            return result;
        }

        // Given an array (this), a pointer to its first element (EA), and
        // the offset (count of elements -- see m_InternalGetOffset comment for
        // what this means), compute the desired element's address, typecheck
        // the value against the actual array type, unbox it if necessary, and
        // put it in the array
        // PRE: 'this' fixed
        // BUGBUG: need to support widening of primitives
        private unsafe void InternalSetValueHelper(byte *EA, int dwOffset,
                                                   Object value) {
            int arrayElementSize = this.vtable.arrayElementSize;
            EA += dwOffset * arrayElementSize;

            // have address to store at, but need to typecheck
            if (this.vtable.arrayOf == StructuralType.Reference) {
                VTable.checkArrayStore(this, value);

                *(UIntPtr *)EA = Magic.addressOf(value);
                return;
            }

            // BUGBUG: enum type lost

            VTable vtable;
            if (this.vtable.arrayOf == StructuralType.Struct) {
                vtable = this.vtable.arrayElementClass;
            }
            else {
                // assert primitive
                vtable = TypeInfo.arrayOfBox[(int)this.vtable.arrayOf];
            }

            // BUGBUG: need to also widening of primitives
            if (vtable != value.vtable) {
                throw new InvalidCastException("InvalidCast_StoreArrayElement");
            }

            // HACK: depends on value being at same spot in all valuetypes
            // REVIEW: value is not fixed
            byte *src = (byte *) Magic.addressOf(value) + 4;

            Buffer.MoveMemory(EA, src, arrayElementSize);
        }


        // This is the core set routines for Get/Set Value.  The arguments have
        // been verified that they exist before we get to this point.

        // PRE: rank has been checked (e.g. if rank==1, then index2==index3==0)
        private unsafe Object InternalGetValue(int index1, int index2, int index3) {
            fixed(int *o = &this.field1) {
                byte *EA = (byte*) GetFirstElementAddress(o);
                int dwOffset = InternalGetOffset(index1, index2, index3);
                return InternalGetValueHelper(EA, dwOffset);
            }
        }

        // PRE: rank has been checked
        private unsafe Object InternalGetValueEx(int[] indices) {
            fixed(int *o = &this.field1) {
                byte *EA = (byte*) GetFirstElementAddress(o);
                int dwOffset = InternalGetOffset(indices);
                return InternalGetValueHelper(EA, dwOffset);
            }
        }


        // PRE: rank has been checked (e.g. if rank==1, then index2==index3==0)
        // REVIEW: check ordering of errors (e.g. if you try to store the wrong
        // types of object in an array at an illegal offset, what should happen?)
        private unsafe void InternalSetValue(Object value, int index1,
                                             int index2, int index3) {
            fixed(int *o = &this.field1) {
                byte *EA = (byte*) GetFirstElementAddress(o);
                int dwOffset = InternalGetOffset(index1, index2, index3);
                InternalSetValueHelper(EA, dwOffset, value);
            }
        }

        private unsafe void InternalSetValueEx(Object value,int[] indices) {
            fixed(int *o = &this.field1) {
                byte *EA = (byte*) GetFirstElementAddress(o);
                int dwOffset = InternalGetOffset(indices);
                InternalSetValueHelper(EA, dwOffset, value);
            }
        }

        [MethodImpl(MethodImplOptions.InternalCall)]
        extern private static void UnsafeUpdateArray(Array a,Object value,int index);
        [MethodImpl(MethodImplOptions.InternalCall)]
        extern private static Object UnsafeReadArray(Array arr,int index);

        [MethodImpl(MethodImplOptions.InternalCall)]
        internal static extern Array InternalQuickCreateEx(VTable array_type,int[] lengths,int[] lowerBounds);

    }
}
