//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


namespace System.GCs
{
    using System.Runtime.CompilerServices;

    // Util contains common functions for alignment and padding
    // arithmetic and for calculating object sizes.
    internal class Util
    {
        // WARNING: don't initialize any static fields in this class
        // without manually running the class constructor at startup!

        [NoHeapAllocation]
        internal static uint dwordAlign(uint numBytes) {
            return ((numBytes+3) & ~3U);
        }

        [NoHeapAllocation]
        internal static UIntPtr dwordAlign(UIntPtr numBytes) {
            return ((numBytes+3) & new UIntPtr(~3U));
        }

        [NoHeapAllocation]
        static UIntPtr qwordAlign(UIntPtr addr) {
            return ((addr+7) & new UIntPtr(~7U));
        }

        [Inline]
        [NoHeapAllocation]
        internal static bool IsAligned(uint bytes, uint size)
        {
            return (bytes & (size - 1)) == 0;
        }

        [Inline]
        [NoHeapAllocation]
        internal static bool IsAligned(UIntPtr bytes, UIntPtr size)
        {
            return (bytes & (size - 1)) == UIntPtr.Zero;
        }

        [Inline]
        [NoHeapAllocation]
        internal static uint Align(uint bytes, uint size)
        {
            return (bytes & ~(size - 1));
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr Align(UIntPtr bytes, UIntPtr size)
        {
            return (bytes & ~(size - 1));
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr UIntPtrAlign(UIntPtr bytes)
        {
            return Align(bytes, (UIntPtr) UIntPtr.Size);
        }

        [Inline]
        [NoHeapAllocation]
        internal static uint Pad(uint data, uint size)
        {
            return ((data + (size - 1)) & ~(size - 1));
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr Pad(UIntPtr data, UIntPtr size)
        {
            return ((data + (size - 1)) & ~(size - 1));
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr UIntPtrPad(UIntPtr bytes)
        {
            return Pad(bytes, (UIntPtr) UIntPtr.Size);
        }

        internal static unsafe void MemClear(UIntPtr startAddr,
                                             UIntPtr size)
        {
#if SINGULARITY
            // On Singularity we use the common optimized functions.
            Buffer.ZeroMemory((byte*)startAddr, (int)size);
#else
            VTable.Assert(UIntPtr.Size !=4 || ((startAddr & ((UIntPtr)0x3)) == ((UIntPtr)0)), "Not-aligned address in Util.MemClear");
            VTable.Assert(UIntPtr.Size !=8 || ((startAddr & ((UIntPtr)0x7)) == ((UIntPtr)0)), "Not-aligned address in Util.MemClear");
            VTable.Assert((size & ((UIntPtr)0x3)) == ((UIntPtr)0), "size expected to be multiple of 4 (size of int) in Util.MemClear");
            Buffer.ZeroMemory((byte*)startAddr, size);
#endif
        }

        internal static unsafe void MemCopy(UIntPtr toAddress,
                                            UIntPtr fromAddress,
                                            UIntPtr count)
        {
#if SINGULARITY
            // On Singularity we use the common optimized functions.
            Buffer.MoveMemory((byte*)toAddress, (byte*)fromAddress, (int)count);
#else
            int wordCount = (int) (count >> 2);
            int *from = (int *) fromAddress;
            int *to = (int *) toAddress;
            for (int i = 0; i < wordCount; i++) {
                to[i] = from[i];
            }
#endif
        }

        internal static void PrintPageContents(UIntPtr page)
        {
            UIntPtr startAddr = PageTable.PageAddr(page);
            UIntPtr endAddr = PageTable.PageAddr(page + 1);
            PrintMemoryContents(startAddr, endAddr);
        }

        internal static unsafe void PrintMemoryContents(UIntPtr startAddr,
                                                        UIntPtr endAddr)
        {
            if (UIntPtr.Size == 4) {
                VTable.DebugPrint("Memory contents for {0,8:x8}..{1,8:x8}\n",
                                  __arglist(startAddr, endAddr));
                for (UIntPtr addr = startAddr; addr < endAddr; addr += 32) {
                    UIntPtr *ptr = (UIntPtr *) addr;
                    // Only print 6 digits of the address in order to
                    // fit on 80 column output devices
                    uint printAddress = unchecked((uint) addr) & 0xffffff;
                    VTable.DebugPrint("{0,6:x6}: "+
                                      "{1,8:x8} {2,8:x8} {3,8:x8} {4,8:x8} "+
                                      "{5,8:x8} {6,8:x8} {7,8:x8} {8,8:x8}\n",
                                      __arglist(printAddress, *ptr, *(ptr+1),
                                                *(ptr+2), *(ptr+3), *(ptr+4),
                                                *(ptr+5), *(ptr+6), *(ptr+7)));
                }
            } else {
                VTable.DebugPrint("Memory contents for "+
                                  "{0,16:x16}..{1,16:x16}\n",
                                  __arglist(startAddr, endAddr));
                for (UIntPtr addr = startAddr; addr < endAddr; addr += 32) {
                    UIntPtr *ptr = (UIntPtr *) addr;
                    uint printAddress = unchecked((uint) addr);
                    VTable.DebugPrint("{0,8:x8}: {1,16:x16} {2,16:x16} "+
                                      "{3,16:x16} {4,16:x16}\n",
                                      __arglist(printAddress, *ptr,
                                                *(ptr+1), *(ptr+2), *(ptr+3)));
                }
            }
        }

    }

}
