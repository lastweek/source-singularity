// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//
// Note: These routines assume that the processor supports
// 32-bit aligned accesses.  Migration to non-x86 platforms will
// need to examine and tune the implementations accordingly.
//

namespace System
{

    using System;
    using System.Runtime.CompilerServices;
    //| <include path='docs/doc[@for="Buffer"]/*' />

    public sealed partial class Buffer
    {
        [NoHeapAllocation]
        [Inline]
        private static unsafe void WriteHelperByte(byte* dst, byte val,
                                                   bool vol) {
            if (vol) {
                System.Threading.Thread.VolatileWriteUnsafe(dst, val);
            }
            else {
                *dst = val;
            }
        }

        [NoHeapAllocation]
        [Inline]
        private static unsafe byte ReadHelperByte(byte* src, bool vol) {
            if (vol) {
                return System.Threading.Thread.VolatileReadUnsafe(src);
            }
            else {
                return *src;
            }
        }

        [NoHeapAllocation]
        [Inline]
        private static unsafe void WriteHelperShort(short* dst, short val,
                                                    bool vol) {
            if (vol) {
                System.Threading.Thread.VolatileWriteUnsafe(dst, val);
            }
            else {
                *dst = val;
            }
        }

        [NoHeapAllocation]
        [Inline]
        private static unsafe short ReadHelperShort(short* src, bool vol) {
            if (vol) {
                return System.Threading.Thread.VolatileReadUnsafe(src);
            }
            else {
                return *src;
            }
        }

        [NoHeapAllocation]
        [Inline]
        private static unsafe void WriteHelperInt(int* dst, int val, bool vol) {
            if (vol) {
                System.Threading.Thread.VolatileWriteUnsafe(dst, val);
            }
            else {
                *dst = val;
            }
        }

        [NoHeapAllocation]
        [Inline]
        private static unsafe int ReadHelperInt(int* src, bool vol) {
            if (vol) {
                return System.Threading.Thread.VolatileReadUnsafe(src);
            }
            else {
                return *src;
            }
        }

        [NoHeapAllocation]
        public static unsafe void MoveMemory(byte* dmem, byte* smem,
                                             UIntPtr size)
        {
            MoveMemory(dmem, smem, (int)size);
        }

        // This is a replacement for the memmove intrinsic.
        // It performs better than the CRT one and the inline version
        // originally from Lightning\Src\VM\COMSystem.cpp
        [NoHeapAllocation]
        [Inline]
        private static unsafe void MoveMemoryImpl(byte* dmem, byte* smem,
                                                  int size, bool vol) {
            if (dmem <= smem) {
                // take the slow path if the source and dest and co-aligned.
                if (((int)smem & 0x3) != ((int)dmem & 0x3)) {
                    for (; size > 0; size--) {
                        WriteHelperByte(dmem++, ReadHelperByte(smem++, vol), vol);
                    }
                    return;
                }

                // make sure the destination is dword aligned
                while ((((int)dmem) & 0x3) != 0 && size >= 3) {
                    WriteHelperByte(dmem++, ReadHelperByte(smem++, vol), vol);
                    size -= 1;
                }
                // copy 16 bytes at a time
                if (size >= 16) {
                    size -= 16;
                    do {
                        WriteHelperInt(&((int*)dmem)[0],
                                       ReadHelperInt(&((int*)smem)[0], vol),
                                       vol);
                        WriteHelperInt(&((int*)dmem)[1],
                                       ReadHelperInt(&((int*)smem)[1], vol),
                                       vol);
                        WriteHelperInt(&((int*)dmem)[2],
                                       ReadHelperInt(&((int*)smem)[2], vol),
                                       vol);
                        WriteHelperInt(&((int*)dmem)[3],
                                       ReadHelperInt(&((int*)smem)[3], vol),
                                       vol);
                        dmem += 16;
                        smem += 16;
                    }
                    while ((size -= 16) >= 0);
                }

                // still 8 bytes or more left to copy?
                if ((size & 8) != 0) {
                    WriteHelperInt(&((int *)dmem)[0],
                                   ReadHelperInt(&((int *)smem)[0], vol), vol);
                    WriteHelperInt(&((int *)dmem)[1],
                                   ReadHelperInt(&((int *)smem)[1], vol), vol);
                    dmem += 8;
                    smem += 8;
                }

                // still 4 bytes or more left to copy?
                if ((size & 4) != 0) {
                    WriteHelperInt(&((int *)dmem)[0],
                                   ReadHelperInt(&((int *)smem)[0], vol), vol);
                    dmem += 4;
                    smem += 4;
                }

                // still 2 bytes or more left to copy?
                if ((size & 2) != 0) {
                    WriteHelperShort(&((short *)dmem)[0],
                                     ReadHelperShort(&((short *)smem)[0], vol),
                                     vol);
                    dmem += 2;
                    smem += 2;
                }

                // still 1 byte left to copy?
                if ((size & 1) != 0) {
                    WriteHelperByte(dmem, ReadHelperByte(smem, vol), vol);
                    dmem += 1;
                    smem += 1;
                }
            }
            else {
                smem += size;
                dmem += size;

                // take the slow path if the source and dest and co-aligned.
                if (((int)smem & 0x3) != ((int)dmem & 0x3)) {
                    for (; size > 0; size--) {
                        WriteHelperByte(--dmem, ReadHelperByte(--smem, vol), vol);
                    }
                    return;
                }

                // make sure the destination is dword aligned
                while ((((int)dmem) & 0x3) != 0 && size >= 3) {
                    WriteHelperByte(--dmem, ReadHelperByte(--smem, vol), vol);
                    size -= 1;
                }

                // copy 16 bytes at a time
                if (size >= 16) {
                    size -= 16;
                    do {
                        dmem -= 16;
                        smem -= 16;
                        WriteHelperInt(&((int *)dmem)[3],
                                       ReadHelperInt(&((int *)smem)[3], vol),
                                       vol);
                        WriteHelperInt(&((int *)dmem)[2],
                                       ReadHelperInt(&((int *)smem)[2], vol),
                                       vol);
                        WriteHelperInt(&((int *)dmem)[1],
                                       ReadHelperInt(&((int *)smem)[1], vol),
                                       vol);
                        WriteHelperInt(&((int *)dmem)[0],
                                       ReadHelperInt(&((int *)smem)[0], vol),
                                       vol);
                    }
                    while ((size -= 16) >= 0);
                }

                // still 8 bytes or more left to copy?
                if ((size & 8) != 0) {
                    dmem -= 8;
                    smem -= 8;
                    WriteHelperInt(&((int *)dmem)[1],
                                   ReadHelperInt(&((int *)smem)[1], vol), vol);
                    WriteHelperInt(&((int *)dmem)[0],
                                   ReadHelperInt(&((int *)smem)[0], vol), vol);
                }

                // still 4 bytes or more left to copy?
                if ((size & 4) != 0) {
                    dmem -= 4;
                    smem -= 4;
                    WriteHelperInt(&((int *)dmem)[0],
                                   ReadHelperInt(&((int *)smem)[0], vol), vol);
                }

                // still 2 bytes or more left to copy?
                if ((size & 2) != 0) {
                    dmem -= 2;
                    smem -= 2;
                    WriteHelperShort(&((short *)dmem)[0],
                                     ReadHelperShort(&((short *)smem)[0], vol),
                                     vol);
                }

                // still 1 byte left to copy?
                if ((size & 1) != 0) {
                    dmem -= 1;
                    smem -= 1;
                    WriteHelperByte(dmem,
                                    ReadHelperByte(smem, vol), vol);
                }
            }
        }

        // Copies from one primitive array to another primitive array without
        // respecting types.  This calls memmove internally.
        //| <include path='docs/doc[@for="Buffer.BlockCopy"]/*' />
        public static void BlockCopy(Array src, int srcOffset,
                                     Array dst, int dstOffset, int count) {
            if (src == null) {
                throw new ArgumentNullException("src");
            }
            if (dst == null) {
                throw new ArgumentNullException("dst");
            }
            InternalBlockCopy(src, srcOffset, dst, dstOffset, count);
        }

        // A very simple and efficient array copy that assumes all of the
        // parameter validation has already been done.  All counts here are
        // in bytes.
        internal static unsafe void InternalBlockCopy(Array src, int srcOffset,
                                                      Array dst, int dstOffset,
                                                      int count) {
            VTable.Assert(src != null);
            VTable.Assert(dst != null);

            // Unfortunately, we must do a check to make sure we're writing
            // within the bounds of the array.  This will ensure that we don't
            // overwrite memory elsewhere in the system nor do we write out junk.
            // This can happen if multiple threads screw with our IO classes
            // simultaneously without being threadsafe.  Throw here.
            int srcLen = src.Length * src.vtable.arrayElementSize;
            if (srcOffset < 0 || dstOffset < 0 || count < 0 ||
                srcOffset > srcLen - count)
                throw new IndexOutOfRangeException
                    ("IndexOutOfRange_IORaceCondition");
            if (src == dst) {
                if (dstOffset > srcLen - count)
                    throw new IndexOutOfRangeException
                        ("IndexOutOfRange_IORaceCondition");
            }
            else {
                int dstLen = dst.Length * dst.vtable.arrayElementSize;
                if (dstOffset > dstLen - count)
                    throw new IndexOutOfRangeException
                        ("IndexOutOfRange_IORaceCondition");
            }

            // Copy the data.
            // Call our faster version of memmove, not the CRT one.
            fixed (int *srcFieldPtr = &src.field1) {
                fixed (int *dstFieldPtr = &dst.field1) {
                    byte *srcPtr = (byte *)
                        src.GetFirstElementAddress(srcFieldPtr);
                    byte *dstPtr = (byte *)
                        dst.GetFirstElementAddress(dstFieldPtr);
                    MoveMemory(dstPtr + dstOffset, srcPtr + srcOffset, count);
                }
            }
        }

        [NoHeapAllocation]
        internal static unsafe void ZeroMemory(byte* dst, UIntPtr len)
        {
            ZeroMemory(dst, (int)len);
        }

        [Inline]
        [NoHeapAllocation]
        internal unsafe static void InitMemoryImpl(byte* dest, byte value,
                                                   int len, bool vol) {
            int intValue = (value == 0) ? 0 :
                (value | (value << 8) | (value << 16) | (value << 24));
            // This is based on Peter Sollich's faster memcpy implementation,
            // from COMString.cpp.
            while ((((int)dest) & 0x03) != 0 && len >= 3) {
                WriteHelperByte(dest++, value, vol);
                len -= 1;
            }

            if (len >= 16) {
                len -= 16;
                do {
                    WriteHelperInt(&((int*)dest)[0], intValue, vol);
                    WriteHelperInt(&((int*)dest)[1], intValue, vol);
                    WriteHelperInt(&((int*)dest)[2], intValue, vol);
                    WriteHelperInt(&((int*)dest)[3], intValue, vol);
                    dest += 16;
                } while ((len -= 16) >= 0);
            }
            if ((len & 8) > 0) {
                WriteHelperInt(&((int*)dest)[0], intValue, vol);
                WriteHelperInt(&((int*)dest)[1], intValue, vol);
                dest += 8;
            }
            if ((len & 4) > 0) {
                WriteHelperInt(&((int*)dest)[0], intValue, vol);
                dest += 4;
            }
            if ((len & 2) != 0) {
                short shortValue = (value == 0) ?  (short) 0 :
                    (short)(value | value << 8) ;
                dest += 2;
            }
            if ((len & 1) != 0)
                WriteHelperByte(dest++, value, vol);
        }

        // Gets a particular byte out of the array.  The array must be an
        // array of primitives.
        //
        // This essentially does the following:
        // return ((byte*)array) + index.
        //
        //| <include path='docs/doc[@for="Buffer.GetByte"]/*' />
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static extern byte GetByte(Array array, int index);

        // Sets a particular byte in an the array.  The array must be an
        // array of primitives.
        //
        // This essentially does the following:
        // *(((byte*)array) + index) = value.
        //
        //| <include path='docs/doc[@for="Buffer.SetByte"]/*' />
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static extern void SetByte(Array array, int index, byte value);

        // Gets a particular byte out of the array.  The array must be an
        // array of primitives.
        //
        // This essentially does the following:
        // return array.length * sizeof(array.UnderlyingElementType).
        //
        //| <include path='docs/doc[@for="Buffer.ByteLength"]/*' />
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static extern int ByteLength(Array array);
    }
}
