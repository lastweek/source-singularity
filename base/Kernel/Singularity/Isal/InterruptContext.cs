//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// This file defines an architecture-neutral encapsulation of the low-level information
// saved during an interrupt dispatch.
//

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

#if ISA_IX
using Microsoft.Singularity.Isal.IX;
#elif ISA_ARM
using Microsoft.Singularity.Isal.Arm;
#endif

namespace Microsoft.Singularity.Isal
{
    // InterruptContext is the lightweight context which is pushed on the stack
    // during interrupt generation.  This is the minimal context save we will
    // perform for any interrupt processing. (Note that it includes caller
    // saved registers so we can use C code.)

    [NoCCtor]
    [AccessedByRuntime("referenced in c++", AllFields = true)]
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential)]
    public struct InterruptContext
    {
#if ISA_IX
        // Vector constants
        public const int VectorExceptionMax = 0x20;
        public const int VectorSchedulerMin = 0x21;

#if ISA_IX64
        // Caller-saved registers (which get saved by our handler routine)
        public UIntPtr   r11;
        public UIntPtr   r10;
        public UIntPtr   r9;
        public UIntPtr   r8;
#endif //ISA_IX64

        // Caller-saved registers (which get saved by our handler routine)
        public UIntPtr   dx;
        public UIntPtr   cx;
        public UIntPtr   ax;

        // Interrupt information pushed as part of interrupt dispatch
        public UIntPtr   vector;
        public UIntPtr   err;

        // Interruption context
        public UIntPtr   ip;
        public UIntPtr   cs;
        public UIntPtr   fl;

        // This stack info is valid only in cases of cross-ring interrupts; otherwise
        // we stay on the same stack and pop to this level (ignoring these two fields.)
        public UIntPtr   sp;
        public UIntPtr   ss;

#elif ISA_ARM

        // Unbanked caller-saved registers.
        public uint     r0;
        public uint     r1;
        public uint     r2;
        public uint     r3;
        public uint     r12;
        public uint     pc; // aka r15

        // Banked caller-saved registers.
        public uint     sp; // aka r13
        public uint     lr; // aka r14

        // Resume proessor status register.
        public uint     cpsr;

        // Interrupt information.
        public uint     vector;
        public uint     instruction;

#endif

        [NoHeapAllocation]
        public bool IsException()
        {
#if ISA_IX
            return (vector < 0x20);
#elif ISA_ARM
            return (vector < ExceptionVector.Irq);
#endif
        }

        public byte ExceptionId
        {
            [NoHeapAllocation]
            get {
                return (byte)vector;
            }
        }

        public UIntPtr InstructionPointer
        {
            [NoHeapAllocation]
            get {
#if ISA_IX
                return (UIntPtr)ip;
#elif ISA_ARM
                return (UIntPtr)pc;
#endif
            }
        }

        public UIntPtr StackPointer
        {
            [NoHeapAllocation]
            get {
#if ISA_IX86
                if ((cs & 0x3) == (Isa.GetCs() & 0x3)) {
                    unsafe {
                        fixed (UIntPtr *p = &sp) {
                            return *p;
                        }
                    }
                }
                else {
                    return sp;
                }
#elif ISA_IX64
                return sp;
#elif ISA_ARM
                return sp;
#endif
            }
        }

        [NoHeapAllocation]
        public unsafe void Display()
        {
#if ISA_IX86
            DebugStub.WriteLine("  eax={0:x8} ecx={1:x8} edx={2:x8}",
                                __arglist(ax, cx, dx));

            DebugStub.WriteLine("  esp[x-ring only]={0:x8}",
                                __arglist(sp));

            DebugStub.WriteLine("  eip={0:x8} efl={1:x8}",
                                __arglist(ip, fl));
#elif ISA_IX64
            DebugStub.WriteLine("  rax={0:x16} rcx={1:x16} rdx={2:x16}",
                                __arglist(ax, cx, dx));

            DebugStub.WriteLine("  rsp={0:x16}",
                                __arglist(sp));

            DebugStub.WriteLine("  rip={0:x16} rfl={1:x16}",
                                __arglist(ip, fl));
#elif ISA_ARM
            DebugStub.WriteLine("pc={0:x8} sp={1:x8} lr={2:x8} sr={3:x8}",
                                __arglist(pc, sp, lr, cpsr));
            DebugStub.WriteLine("r0={0:x8} r1={1:x8} r2={2:x8} r3={3:x8}",
                                __arglist(r0, r1, r2, r3));
#endif
        }
    }
}
