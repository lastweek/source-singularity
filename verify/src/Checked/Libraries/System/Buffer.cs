// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//

namespace System
{

    using System;
    using System.Runtime.CompilerServices;
    //| <include path='docs/doc[@for="Buffer"]/*' />

    public sealed class Buffer
    {
        [NoHeapAllocation]
        public static void MoveMemory(
            byte[] dmem, byte[] smem, int dIdx, int sIdx, int len)
        {
            if (dmem != smem || dIdx <= sIdx) {
                while (len > 0) {
                    dmem[dIdx] = smem[sIdx];
                    dIdx++;
                    sIdx++;
                    len--;
                }
            } else {
                dIdx += len;
                sIdx += len;
                while (len > 0) {
                    dIdx--;
                    sIdx--;
                    dmem[dIdx] = smem[sIdx];
                    len--;
                }
            }
        }

        [NoHeapAllocation]
        public static void MoveMemory(
            char[] dmem, char[] smem, int dIdx, int sIdx, int len)
        {
            if (dmem != smem || dIdx <= sIdx) {
                while (len > 0) {
                    dmem[dIdx] = smem[sIdx];
                    dIdx++;
                    sIdx++;
                    len--;
                }
            } else {
                dIdx += len;
                sIdx += len;
                while (len > 0) {
                    dIdx--;
                    sIdx--;
                    dmem[dIdx] = smem[sIdx];
                    len--;
                }
            }
        }

        public static void BlockCopy(byte[] src, int srcOffset,
                                     byte[] dst, int dstOffset, int count) {
            MoveMemory(dst, src, dstOffset, srcOffset, count);
        }

        public static void BlockCopy(char[] src, int srcOffset,
                                     char[] dst, int dstOffset, int count) {
            VTable.Assert((count & 1) == 0);
            VTable.Assert((srcOffset & 1) == 0);
            VTable.Assert((dstOffset & 1) == 0);
            MoveMemory(dst, src, dstOffset >> 1, srcOffset >> 1, count >> 1);
        }

        internal static void InternalBlockCopy(
            char[] src, int srcOffset,
            char[] dst, int dstOffset, int count)
        {
            VTable.Assert((count & 1) == 0);
            VTable.Assert((srcOffset & 1) == 0);
            VTable.Assert((dstOffset & 1) == 0);
            MoveMemory(dst, src, dstOffset >> 1, srcOffset >> 1, count >> 1);
        }

        internal static void InternalBlockCopy(
            byte[] src, int srcOffset,
            byte[] dst, int dstOffset, int count)
        {
            MoveMemory(dst, src, dstOffset, srcOffset, count);
        }

        internal static void InternalBlockCopy(
            char[] src, int srcOffset,
            byte[] dst, int dstOffset, int count)
        {
            VTable.Assert((count & 1) == 0);
            dstOffset = count >> 1;
            VTable.Assert((srcOffset & 1) == 0);
            srcOffset = srcOffset >> 1;
            for (int i = 0; i < count; i++) {
                char c = src[srcOffset + i];
                dst[dstOffset + 2 * i] = (byte) c;
                dst[dstOffset + 2 * i + 1] = (byte) (c >> 8);
            }
        }

        internal static void InternalBlockCopy(
            byte[] src, int srcOffset,
            char[] dst, int dstOffset, int count)
        {
            VTable.Assert((count & 1) == 0);
            dstOffset = count >> 1;
            VTable.Assert((dstOffset & 1) == 0);
            dstOffset = dstOffset >> 1;
            for (int i = 0; i < count; i++) {
                byte b0 = src[srcOffset + 2 * i];
                byte b1 = src[srcOffset + 2 * i + 1];
                dst[dstOffset + i] = (char)(((int) b0) | (((int) b1) << 8));
            }
        }

        // Copies from one primitive array to another primitive array without
        // respecting types.  This calls memmove internally.
        //| <include path='docs/doc[@for="Buffer.BlockCopy"]/*' />
/*
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
*/
    }
}
