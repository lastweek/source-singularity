//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to the Bartok Depot and propagated to Singularity Depot.   */
/*******************************************************************/


namespace System {

  using Microsoft.Bartok.Runtime;
  using System;
  using System.Collections;
  using System.GCs;
  using System.Runtime.InteropServices;
  using System.Runtime.CompilerServices;

  [RequiredByBartok]
  internal class ArrayHelper {
      [RequiredByBartok]
      public static void CopyBoolUp(bool[] srcArray, int srcOffset,
                                    bool[] dstArray, int dstOffset,
                                    int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyBoolDown(bool[] srcArray, int srcOffset,
                                      bool[] dstArray, int dstOffset,
                                      int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyCharUp(char[] srcArray, int srcOffset,
                                    char[] dstArray, int dstOffset,
                                    int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyCharDown(char[] srcArray, int srcOffset,
                                      char[] dstArray, int dstOffset,
                                      int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyInt8Up(sbyte[] srcArray, int srcOffset,
                                    sbyte[] dstArray, int dstOffset,
                                    int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyInt8Down(sbyte[] srcArray, int srcOffset,
                                      sbyte[] dstArray, int dstOffset,
                                      int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyInt16Up(short[] srcArray, int srcOffset,
                                     short[] dstArray, int dstOffset,
                                     int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyInt16Down(short[] srcArray, int srcOffset,
                                       short[] dstArray, int dstOffset,
                                       int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyInt32Up(int[] srcArray, int srcOffset,
                                     int[] dstArray, int dstOffset,
                                     int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyInt32Down(int[] srcArray, int srcOffset,
                                       int[] dstArray, int dstOffset,
                                       int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyInt64Up(long[] srcArray, int srcOffset,
                                     long[] dstArray, int dstOffset,
                                     int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyInt64Down(long[] srcArray, int srcOffset,
                                       long[] dstArray, int dstOffset,
                                       int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyUInt8Up(byte[] srcArray, int srcOffset,
                                     byte[] dstArray, int dstOffset,
                                     int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyUInt8Down(byte[] srcArray, int srcOffset,
                                       byte[] dstArray, int dstOffset,
                                       int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyUInt16Up(ushort[] srcArray, int srcOffset,
                                      ushort[] dstArray, int dstOffset,
                                      int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyUInt16Down(ushort[] srcArray, int srcOffset,
                                        ushort[] dstArray, int dstOffset,
                                        int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyUInt32Up(uint[] srcArray, int srcOffset,
                                      uint[] dstArray, int dstOffset,
                                      int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyUInt32Down(uint[] srcArray, int srcOffset,
                                        uint[] dstArray, int dstOffset,
                                        int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyUInt64Up(ulong[] srcArray, int srcOffset,
                                      ulong[] dstArray, int dstOffset,
                                      int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyUInt64Down(ulong[] srcArray, int srcOffset,
                                        ulong[] dstArray, int dstOffset,
                                        int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyFloat32Up(float[] srcArray, int srcOffset,
                                       float[] dstArray, int dstOffset,
                                       int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyFloat32Down(float[] srcArray, int srcOffset,
                                         float[] dstArray, int dstOffset,
                                         int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      [RequiredByBartok]
      public static void CopyFloat64Up(double[] srcArray, int srcOffset,
                                       double[] dstArray, int dstOffset,
                                       int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyFloat64Down(double[] srcArray, int srcOffset,
                                         double[] dstArray, int dstOffset,
                                         int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

#if false
      // Unchecked versions of these arrays.
      // Preconditions: bounds are in range.
      public static void UncheckedCopyBoolUp(bool[] srcArray, int srcOffset,
                                             bool[] dstArray, int dstOffset,
                                             int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyBoolDown(bool[] srcArray, int srcOffset,
                                               bool[] dstArray, int dstOffset,
                                               int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyCharUp(char[] srcArray, int srcOffset,
                                             char[] dstArray, int dstOffset,
                                             int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyCharDown(char[] srcArray, int srcOffset,
                                               char[] dstArray, int dstOffset,
                                               int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyInt8Up(sbyte[] srcArray, int srcOffset,
                                             sbyte[] dstArray, int dstOffset,
                                             int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyInt8Down(sbyte[] srcArray, int srcOffset,
                                               sbyte[] dstArray, int dstOffset,
                                               int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyInt16Up(short[] srcArray, int srcOffset,
                                              short[] dstArray, int dstOffset,
                                              int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyInt16Down(short[] srcArray, int srcOffset,
                                                short[] dstArray, int dstOffset,
                                                int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyInt32Up(int[] srcArray, int srcOffset,
                                              int[] dstArray, int dstOffset,
                                              int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyInt32Down(int[] srcArray, int srcOffset,
                                                int[] dstArray, int dstOffset,
                                                int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyInt64Up(long[] srcArray, int srcOffset,
                                              long[] dstArray, int dstOffset,
                                              int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyInt64Down(long[] srcArray, int srcOffset,
                                                long[] dstArray, int dstOffset,
                                                int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyUInt8Up(byte[] srcArray, int srcOffset,
                                              byte[] dstArray, int dstOffset,
                                              int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyUInt8Down(byte[] srcArray, int srcOffset,
                                                byte[] dstArray, int dstOffset,
                                                int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyUInt16Up(ushort[] srcArray, int srcOffset,
                                               ushort[] dstArray, int dstOffset,
                                               int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyUInt16Down(ushort[] srcArray,
                                                 int srcOffset,
                                                 ushort[] dstArray,
                                                 int dstOffset,
                                                 int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyUInt32Up(uint[] srcArray, int srcOffset,
                                               uint[] dstArray, int dstOffset,
                                               int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyUInt32Down(uint[] srcArray, int srcOffset,
                                                 uint[] dstArray, int dstOffset,
                                                 int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyUInt64Up(ulong[] srcArray, int srcOffset,
                                               ulong[] dstArray, int dstOffset,
                                               int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyUInt64Down(ulong[] srcArray,
                                                 int srcOffset,
                                                 ulong[] dstArray,
                                                 int dstOffset,
                                                 int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyFloat32Up(float[] srcArray, int srcOffset,
                                                float[] dstArray, int dstOffset,
                                                int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyFloat32Down(float[] srcArray,
                                                  int srcOffset,
                                                  float[] dstArray,
                                                  int dstOffset,
                                                  int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      public static void UncheckedCopyFloat64Up(double[] srcArray,
                                                int srcOffset,
                                                double[] dstArray,
                                                int dstOffset,
                                                int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void UncheckedCopyFloat64Down(double[] srcArray,
                                                  int srcOffset,
                                                  double[] dstArray,
                                                  int dstOffset,
                                                  int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }

      // PRE: lengths compatible
      // REVIEW: no length or type checking
      // REVIEW: see System.Array.Copy
      [RequiredByBartok]
      public static unsafe void InitArray(System.Array srcArray,
                                          System.Array dstArray) {
#if !REFERENCE_COUNTING_GC && !DEFERRED_REFERENCE_COUNTING_GC
          Barrier.ArrayCopy(srcArray, 0, dstArray, 0, srcArray.Length);
#else
          fixed (int *srcFieldPtr = &srcArray.field1) {
              void *src = srcArray.GetFirstElementAddress(srcFieldPtr);
              fixed (int *dstFieldPtr = &dstArray.field1) {
                  void *dst = dstArray.GetFirstElementAddress(dstFieldPtr);
                  int size = (srcArray.vtable.arrayElementSize *
                              srcArray.Length);
#if REFERENCE_COUNTING_GC
                  if (dstArray.vtable.arrayOf ==
                      StructuralType.Reference ||
                      dstArray.vtable.arrayOf ==
                      StructuralType.Struct) {
                      int dstLength =
                          size/dstArray.vtable.arrayElementSize;
                      GCs.ReferenceCountingCollector.
                      IncrementReferentRefCounts(Magic.addressOf(srcArray),
                                                 srcArray.vtable,
                                                 0,
                                                 srcArray.Length);
                      GCs.ReferenceCountingCollector.
                      DecrementReferentRefCounts(Magic.addressOf(dstArray),
                                                 dstArray.vtable,
                                                 0,
                                                 dstLength);
                  }
#elif DEFERRED_REFERENCE_COUNTING_GC
                  if (dstArray.vtable.arrayOf ==
                      StructuralType.Reference ||
                      dstArray.vtable.arrayOf ==
                      StructuralType.Struct) {
                      int dstLength =
                          size/dstArray.vtable.arrayElementSize;
                      GCs.DeferredReferenceCountingCollector.
                      IncrementReferentRefCounts(Magic.addressOf(srcArray),
                                                 srcArray.vtable,
                                                 0,
                                                 srcArray.Length);
                      GCs.DeferredReferenceCountingCollector.
                      DecrementReferentRefCounts(Magic.addressOf(dstArray),
                                                 dstArray.vtable,
                                                 0,
                                                 dstLength);
                  }
#endif // REFERENCE_COUNTING_GC
                  System.IO.__UnmanagedMemoryStream.memcpyimpl
                      ((byte*)src, (byte*)dst, size);
              }
          }
#endif // REFERENCE_COUNTING_GC
      }
#endif

      public static void CopyRefObjectUp(Object[] srcArray, int srcOffset,
                                         Object[] dstArray, int dstOffset,
                                         int length) {
          int dx = dstOffset;
          int sx = srcOffset;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx++;
              dx++;
          }
      }

      public static void CopyRefObjectDown(Object[] srcArray, int srcOffset,
                                           Object[] dstArray, int dstOffset,
                                           int length) {
          int dx = dstOffset+length-1;
          int sx = srcOffset+length-1;
          for (int i=length-1; i>=0; i--) {
              dstArray[dx] = srcArray[sx];
              sx--;
              dx--;
          }
      }
  }
}
