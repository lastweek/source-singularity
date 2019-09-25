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

#if ISA_IX
#define USE_EXTERNAL_MEMORY_OPERATIONS
#endif

namespace System
{

    using System;
    using System.Runtime.CompilerServices;
    //| <include path='docs/doc[@for="Buffer"]/*' />

    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("output to header: defined in c++/asm")]
    public sealed partial class Buffer
    {
        private Buffer() {
        }

        [RequiredByBartok]
        internal static unsafe void MoveMemoryVolatile(byte* dmem, byte* smem,
                                                       int size) {
            MoveMemoryImpl(dmem, smem, size, true);
        }

        // Note that this is public (and shouldn't be) so that we can link
        // bitter.sg against buffer.cs.  This method will be made internal
        // when we can compile the .cs files with Sing#.
        //
#if USE_EXTERNAL_MEMORY_OPERATIONS
        [AccessedByRuntime("output to header: defined in c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
        [NoHeapAllocation]
        [RequiredByBartok]
        public static unsafe extern void MoveMemory(byte* dmem, byte* smem,
                                                    int size);
#else // !USE_EXTERNAL_MEMORY_OPERATIONS
        [NoHeapAllocation]
        [RequiredByBartok]
        public static unsafe void MoveMemory(byte* dmem, byte* smem,
                                               int size) {
            MoveMemoryImpl(dmem, smem, size, false);
        }
#endif // !USE_EXTERNAL_MEMORY_OPERATIONS

        // Other parts of class must define this static method:

        // [NoHeapAllocation]
        //private static unsafe void MoveMemoryImpl(byte* dmem, byte* smem,
        //                                          int size, bool vol);


#if USE_EXTERNAL_MEMORY_OPERATIONS
        [AccessedByRuntime("output to header: defined in c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
        [NoHeapAllocation]
        [RequiredByBartok]
        public static unsafe extern void ZeroMemory(byte* dst, int len);
#else // !USE_EXTERNAL_MEMORY_OPERATIONS
        [NoHeapAllocation]
        [RequiredByBartok]
        public static unsafe void ZeroMemory(byte* dest, int len)
        {
            InitMemoryImpl(dest, 0, len, false);
        }
#endif // !USE_EXTERNAL_MEMORY_OPERATIONS

        [NoHeapAllocation]
        [RequiredByBartok]
        internal unsafe static void InitMemory(byte* dest, byte value,
                                               int len) {
            InitMemoryImpl(dest, value, len, false);
        }

        [NoHeapAllocation]
        [RequiredByBartok]
        internal unsafe static void InitMemoryVolatile(byte* dest, byte value,
                                                       int len) {
            InitMemoryImpl(dest, value, len, true);
        }

        // Other parts of class must define this static method:

        // [NoHeapAllocation]
        // internal unsafe static void InitMemoryImpl(byte* dest, byte value,
        //                                            int len, bool vol);

#if USE_EXTERNAL_MEMORY_OPERATIONS
        [AccessedByRuntime("output to header: defined in asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(32)]
        [NoHeapAllocation]
        internal static unsafe extern void ZeroPages(byte* dst, int len);

        [AccessedByRuntime("output to header: defined in asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(32)]
        [NoHeapAllocation]
        internal static unsafe extern void CopyPages(byte* dst, byte *src, int len);
#else
        [AccessedByRuntime("output to header: available in asm")]
        [NoHeapAllocation]
        public static unsafe void ZeroPages(byte* dest, int len)
        {
            InitMemoryImpl(dest, 0, len, false);
        }

        [AccessedByRuntime("output to header: available in asm")]
        [NoHeapAllocation]
        public static unsafe void CopyPages(byte* dmem, byte* smem, int size)
        {
            MoveMemoryImpl(dmem, smem, size, false);
        }
#endif

    }
}
