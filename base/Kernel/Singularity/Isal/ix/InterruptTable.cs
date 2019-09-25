//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//


using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Isal.IX
{
    [NoCCtor]
    [AccessedByRuntime("referenced in c++")]
    [CLSCompliant(false)]
    [StructAlign(16)]
    [StructLayout(LayoutKind.Sequential, Pack=1, 
#if ISA_IX86
                  Size=256*8 // sizeof(Idte)
#else
                  Size=256*16 // sizeof(Idte)
#endif
                  )] 
    public struct InterruptTable
    {
        // Dispatcher is an opaque declaration of a code fragment which normalizes 
        // the stack with the interrupt id, then dispatches to the centralized dispatch routine.
        [AccessedByRuntime("referenced in asm")]
        [StructLayout(LayoutKind.Sequential, Pack=1, Size=16)]
        private struct Dispatcher
        {
            byte first;
        }

        // There are a total of 256 entries; this is controled by the StructLayout attribute above.
        Idte  entry0;

        unsafe Idte *GetStart() 
        {
            fixed (Idte *p = &entry0)
                return p;
        }

        unsafe Idte *GetEnd() 
        {
            fixed (Idte *p = &entry0)
                return p+256;
        }

        [AccessedByRuntime("defined in idt.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(16)]
        [NoHeapAllocation]
        private extern unsafe static Dispatcher *GetDispatchers();

        [NoHeapAllocation]
        public void Initialize()
        {
            unsafe {
                Dispatcher *d = GetDispatchers();

                fixed (Idte *first = &entry0) {
                    Idte *p = first;
                    Idte *pEnd = p + 256;

                    while (p < pEnd) {
                        InitializeEntry(ref *p, (UIntPtr) d);
                        p++;
                        d++;
                    }
                }
            }
        }

        [NoHeapAllocation]
        public static void InitializeEntry(ref Idte entry, UIntPtr address)
        {
            entry.offset_0_15 = (ushort) address;
            entry.offset_16_31 = (ushort) (((uint) address) >> 16);
#if ISA_IX64
            entry.offset_32_63 = (uint) (((ulong)address) >> 32);
#endif

            entry.selector = (ushort) Isa.GetCs();
            entry.flags = 0;
            entry.access = (byte) (Idte.PRESENT | Idte.DPL_RING0 | Idte.INT_GATE);
        } 
    }
}
