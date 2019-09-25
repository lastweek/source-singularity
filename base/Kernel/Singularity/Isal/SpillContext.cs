//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// This file defines an architecture-neutral encapsulation of the state which is saved
// during a thread context switch.

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
    // SpillContext holds the CPU state which is local to a thread.  Note this
    // is a subset of the entire CPU context, as some of the context does not
    // change from thread to thread.

    [NoCCtor]
    [AccessedByRuntime("referenced in c++", AllFields = true)]
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential)]
    [StructAlign(16)]
    public struct SpillContext
    {
#if ISA_IX

        ///////////////////////////////////////////////////////////////////////////
        // ISA_IX86 Context

        //
        // Integer registers
        //

        public UIntPtr  ax;
        public UIntPtr  bx;
        public UIntPtr  cx;
        public UIntPtr  dx;
        public UIntPtr  di;
        public UIntPtr  si;

#if ISA_IX64

        public UIntPtr  r8;
        public UIntPtr  r9;
        public UIntPtr  r10;
        public UIntPtr  r11;
        public UIntPtr  r12;
        public UIntPtr  r13;
        public UIntPtr  r14;
        public UIntPtr  r15;

#endif

        //
        // Control registers
        //

        public UIntPtr  sp;
        public UIntPtr  ip;
        public UIntPtr  bp;
        public UIntPtr  fl;

        //
        // Mmx context.  Note that this must be 16-byte aligned.
        //

        internal MmxContext    mmx;

        // We always store cs even though it never changes in non-paging builds,
        // since it simplifies the context switching code.  Also note we
        // don't store any other segments because they either the same as cs (ss, ds, es) or
        // never change (fs, gs)
        public UIntPtr  cs;

#if PAGING

        //
        // Page table base
        //

        public UIntPtr  cr3;

#endif

#elif ISA_ARM

        ///////////////////////////////////////////////////////////////////////////
        // Arm Context

        //
        // Unbanked integer and control registers.
        //

        public uint     r0;
        public uint     r1;
        public uint     r2;
        public uint     r3;
        public uint     r4;
        public uint     r5;
        public uint     r6;
        public uint     r7;
        public uint     r8;
        public uint     r9;
        public uint     r10;
        public uint     r11;
        public uint     r12;
        public uint     pc; // aka r15

        //
        // Banked control Registers
        //

        public uint     sp; // aka r13
        public uint     lr; // aka r14

        //
        // Processor status register.
        //
        public uint     cpsr;

#endif

        //
        // Extra (unrestored) context information from InterruptContext.
        //

#if ISA_ARM

        public uint     instruction;

#endif

        ///////////////////////////////////////////////////////////////////////////
        // Common fields

        public const int ContentsSpilled            = 0x00000001;

        // Stack limit is stored as part of the spill context.
        public UIntPtr stackLimit;

        // Field for storing various flags about the state of the spill.
        public int spillFlags;

        ///////////////////////////////////////////////////////////////////////////
        // Properties - these are ISA-neutral ways to access common aspects of the
        // spill context.

        public UIntPtr InstructionPointer
        {
            [NoHeapAllocation]
            get {
#if ISA_IX
                return ip;
#elif ISA_ARM
                return pc;
#endif
            }
            [NoHeapAllocation]
            set {
#if ISA_IX
                ip = value;
#elif ISA_ARM
                pc = (uint)value;
#endif
            }
        }

        public UIntPtr StackPointer
        {
            [NoHeapAllocation]
            get {
                return sp;
            }
        }

        public UIntPtr FramePointer
        {
            [NoHeapAllocation]
            get {
#if ISA_IX
                return bp;
#elif ISA_ARM
                return r11; // ?
#endif
            }
        }

        public UIntPtr Flags
        {
            [NoHeapAllocation]
            get {
#if ISA_IX
                return fl;
#elif ISA_ARM
                return cpsr;
#endif
            }
        }

        // IsSpilled indicates whether or not the context is in a spilled state - that is,
        // whether the context represents a swapped-out thread (as opposed to the state
        // where the thread is running.)
        //
        // This flag is set every time we save the context, and cleared when it is restored.

        public bool IsSpilled
        {
            [NoHeapAllocation]
            get {
                return (spillFlags & ContentsSpilled) != 0;
            }
        }

        [NoHeapAllocation]
        public unsafe void Trace()
        {
#if ISA_IX86
            Tracing.Log(Tracing.Debug, "eax={0:x8} ebx={1:x8} ecx={2:x8} edx={3:x8}\n",
                        ax, bx, cx, dx);

            Tracing.Log(Tracing.Debug, "esp={0:x8} ebp={1:x8} esi={2:x8} edi={3:x8}\n",
                        sp, bp, si, di);

            Tracing.Log(Tracing.Debug, "eip={0:x8} efl={1:x8}\n", ip, fl);
#elif ISA_IX64
            Tracing.Log(Tracing.Debug, "rax={0:x16} rbx={1:x16} rcx={2:x16} rdx={3:x16}\n",
                        ax, bx, cx, dx);

            Tracing.Log(Tracing.Debug, "rsp={0:x16} rbp={1:x16} rsi={2:x16} rdi={3:x16}\n",
                        sp, bp, si, di);

            Tracing.Log(Tracing.Debug, "r8={0:x16} r9={1:x16} r10={2:x16} r11={3:x16}\n",
                        r8, r9, r10, r11);

            Tracing.Log(Tracing.Debug, "r12={0:x16} r13={1:x16} r14={2:x16} r15={3:x16}\n",
                        r12, r13, r14, r15);

            Tracing.Log(Tracing.Debug, "rip={0:x16} rfl={1:x16}\n",
                        ip, fl);
#elif ISA_ARM

            Tracing.Log(Tracing.Debug, "r0={0:x8} r1={1:x8} r2={2:x8} r3={3:x8}\n",
                        (UIntPtr) r0, (UIntPtr) r1, (UIntPtr) r2, (UIntPtr) r3);

            Tracing.Log(Tracing.Debug, "r4={0:x8} r5={1:x8} r6={2:x8} r7={3:x8}\n",
                        (UIntPtr) r4, (UIntPtr) r5, (UIntPtr) r6, (UIntPtr) r7);

            Tracing.Log(Tracing.Debug, "r8={0:x8} r9={1:x8} r10={2:x8} r11={3:x8}\n",
                        (UIntPtr) r8, (UIntPtr) r9, (UIntPtr) r10, (UIntPtr) r11);

            Tracing.Log(Tracing.Debug, "r12={0:x8} sp={1:x8} lr={2:x8} pc={3:x8}\n",
                        (UIntPtr) r12, (UIntPtr) sp, (UIntPtr) lr, (UIntPtr) pc);

            Tracing.Log(Tracing.Debug, "cpsr={0:x8}\n", (UIntPtr) cpsr);

#endif
        }

        [NoHeapAllocation]
        public unsafe void Display()
        {
#if ISA_IX86
            DebugStub.WriteLine("  eax={0:x8} ebx={1:x8} ecx={2:x8} edx={3:x8}",
                                __arglist(ax, bx, cx, dx));

            DebugStub.WriteLine("  esp={0:x8} ebp={1:x8} esi={2:x8} edi={3:x8}",
                                __arglist(sp, bp, si, di));

            DebugStub.WriteLine("  eip={0:x8} efl={1:x8}",
                                __arglist(ip, fl));
#elif ISA_IX64
            DebugStub.WriteLine("  rax={0:x16} rbx={1:x16} rcx={2:x16} rdx={3:x16}",
                                __arglist(ax, bx, cx, dx));

            DebugStub.WriteLine("  rsp={0:x16} rbp={1:x16} rsi={2:x16} rdi={3:x16}",
                                __arglist(sp, bp, si, di));

            DebugStub.WriteLine("   r8={0:x16}  r9={1:x16} r10={2:x16} r11={3:x16}",
                                __arglist(r8, r9, r10, r11));

            DebugStub.WriteLine("  r12={0:x16} r13={1:x16} r14={2:x16} r15={3:x16}",
                                __arglist(r12, r13, r14, r15));

            DebugStub.WriteLine("  rip={0:x16} rfl={1:x16}",
                                __arglist(ip, fl));
#elif ISA_ARM

            DebugStub.WriteLine("  r0={0:x8}  r1={1:x8}  r2={2:x8}  r3={3:x8}",
                                __arglist(r0, r1, r2, r3));

            DebugStub.WriteLine("  r4={0:x8}  r5={1:x8}  r6={2:x8}  r7={3:x8}",
                                __arglist(r4, r5, r6, r7));

            DebugStub.WriteLine("  r8={0:x8}  r9={1:x8} r10={2:x8} r11={3:x8}",
                                __arglist(r8, r9, r10, r11));

            DebugStub.WriteLine(" r12={0:x8} sp={1:x8}  lr={2:x8}  pc={3:x8}",
                                __arglist(r12, sp, lr, pc));

            DebugStub.WriteLine(" psr={0:x8}", __arglist(cpsr));
#endif
        }

#if SINGULARITY_KERNEL

        ///////////////////////////////////////////////////////////////////////////
        // Methods

        [AccessedByRuntime("defined in asm")]
        [CLSCompliant(false)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(32)]
        [NoHeapAllocation]
        public extern unsafe bool Save();

        [AccessedByRuntime("defined in asm")]
        [CLSCompliant(false)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(32)]
        [NoHeapAllocation]
        public extern unsafe bool Save(InterruptContext *interrupt);

        [AccessedByRuntime("defined in asm")]
        [CLSCompliant(false)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(32)]
        [NoHeapAllocation]
        public extern unsafe void Resume();

        [AccessedByRuntime("called from C++")]
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public unsafe void Initialize(UIntPtr stack, UIntPtr stackLimit,
                                      UIntPtr start, int threadIndex, UIntPtr cr3)
        {
#if ISA_IX
            UIntPtr *sp = (UIntPtr *) stack;
            *--sp = 0;
            *--sp = 0;
            this.bp = (uint) (UIntPtr) sp;
            this.sp = (uint) (UIntPtr) sp;
            this.ip = (uint) start;
            this.cs  = (uint) Isa.GetCs();
            this.cx = (uint) threadIndex;
            this.fl = EFlags.IF;

            // If we are allowed (i.e. the kernel is ring 0), set IO priveleges in the context
            if ((Isa.GetCs() & 0x3) == 0) {
                this.fl |= EFlags.IOPL; // TODO: get rid of IOPL
            }

            this.fl = EFlags.IF;
            this.mmx.fcw = 0x037f;
            this.mmx.ftw = 0;
            // mmx.mxcsr = 0x1f80;
            this.stackLimit = stackLimit;
#if PAGING
            this.cr3 = cr3;
#endif
#elif ISA_ARM
            this.sp = (uint) stack;
            this.r11 = (uint) stack;
            this.pc = (uint) start;
            this.r0 = (uint) threadIndex;
            this.cpsr = ProcessorMode.System;
            this.stackLimit = stackLimit;
#endif
            // Mark thread as having valid contents
            this.spillFlags = ContentsSpilled;
        }

        [AccessedByRuntime("defined in asm")]
        [CLSCompliant(false)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(32)]
        [NoHeapAllocation]
        public extern unsafe static void ResetCurrent();

#endif // SINGULARITY_KERNEL

    };
}
