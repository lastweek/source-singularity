///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   kd.cs
//
//  Definitions of types use the KD the protocol *AND* by the halkd stub.
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Microsoft.Singularity.Kd
{
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential)]
    [StructAlign(16)]
    [AccessedByRuntime("referenced from c++")]
    internal struct UInt128 {
        internal ulong    lo;
        internal ulong    hi;
    }

    //======================================================================
    // Selected structs and defines used by the KD protocol
    //

    //#pragma pack(push,4)
    //#pragma warning(disable:4200)    /* Zero length array */
    //#pragma warning(disable:4201)    /* Nameless struct/union */

    //-----> From winnt.h#2175

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct InstructionStream {
        internal byte   InstByte0;
        internal byte   InstByte1;
        internal byte   InstByte2;
        internal byte   InstByte3;
        internal byte   InstByte4;
        internal byte   InstByte5;
        internal byte   InstByte6;
        internal byte   InstByte7;
        internal byte   InstByte8;
        internal byte   InstByte9;
        internal byte   InstByte10;
        internal byte   InstByte11;
        internal byte   InstByte12;
        internal byte   InstByte13;
        internal byte   InstByte14;
        internal byte   InstByte15;
    };

    ///////////////////////////////////////////////////////////////////////// X86.
    //

    //
    // Format of data for 32-bit fxsave/fxrstor instructions.
    // Although the fxsave/fxrstor instructions must operate on a 16-byte aligned
    // structure, the KD X86Context structure aligns this field at 12 mod 16.
    // So, we must use a 128-bit type made out of 4-byte subtypes.
    //
    [AccessedByRuntime("referenced from c++")]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86Unaligned128 {
        internal uint   Bits0to31;
        internal uint   Bits32to63;
        internal uint   Bits64to95;
        internal uint   Bits96to128;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86XmmSaveArea {
        internal ushort ControlWord;
        internal ushort StatusWord;
        internal ushort TagWord;
        internal ushort ErrorOpcode;
        internal uint   ErrorOffset;
        internal ushort ErrorSelector;
        internal ushort reserved0;
        internal uint   DataOffset;
        internal ushort DataSelector;
        internal ushort reserved1;
        internal uint   MxCsr;
        internal uint   MxCsrMask;

        internal X86Unaligned128    St0;
        internal X86Unaligned128    St1;
        internal X86Unaligned128    St2;
        internal X86Unaligned128    St3;
        internal X86Unaligned128    St4;
        internal X86Unaligned128    St5;
        internal X86Unaligned128    St6;
        internal X86Unaligned128    St7;

        internal X86Unaligned128    Xmm0;
        internal X86Unaligned128    Xmm1;
        internal X86Unaligned128    Xmm2;
        internal X86Unaligned128    Xmm3;
        internal X86Unaligned128    Xmm4;
        internal X86Unaligned128    Xmm5;
        internal X86Unaligned128    Xmm6;
        internal X86Unaligned128    Xmm7;

        private X86Unaligned128     reserved2;
        private X86Unaligned128     reserved3;
        private X86Unaligned128     reserved4;
        private X86Unaligned128     reserved5;
        private X86Unaligned128     reserved6;
        private X86Unaligned128     reserved7;
        private X86Unaligned128     reserved8;
        private X86Unaligned128     reserved9;

        private X86Unaligned128     reservedA;
        private X86Unaligned128     reservedB;
        private X86Unaligned128     reservedC;
        private X86Unaligned128     reservedD;
        private X86Unaligned128     reservedE;
        private X86Unaligned128     reservedF;
    };

    // 387 floating-point registers are 10 bytes.  We must represent them as
    // groups of 16-bit words so that the data structure is 16-bit aligned.
    [AccessedByRuntime("referenced from c++")]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86Fp387Register {
        internal ushort word0;
        internal ushort word1;
        internal ushort word2;
        internal ushort word3;
        internal ushort word4;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86Fp387SaveArea {
        internal uint    ControlWord;
        internal uint    StatusWord;
        internal uint    TagWord;
        internal uint    ErrorOffset;
        internal uint    ErrorSelector;
        internal uint    DataOffset;
        internal uint    DataSelector;

        internal X86Fp387Register   St0;
        internal X86Fp387Register   St1;
        internal X86Fp387Register   St2;
        internal X86Fp387Register   St3;
        internal X86Fp387Register   St4;
        internal X86Fp387Register   St5;
        internal X86Fp387Register   St6;
        internal X86Fp387Register   St7;

        internal uint    Cr0NpxState;
    };

    //
    // Context Frame
    //
    //  This frame has a several purposes: 1) it is used as an argument to
    //  NtContinue, 2) is is used to construct a call frame for APC delivery,
    //  and 3) it is used in the user level thread creation routines.
    //
    //  The layout of the record conforms to a standard call frame.
    //

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86Context {

        //
        // The flags values within this flag control the contents of
        // a CONTEXT record.
        //
        // If the context record is used as an input parameter, then
        // for each portion of the context record controlled by a flag
        // whose value is set, it is assumed that that portion of the
        // context record contains valid context. If the context record
        // is being used to modify a threads context, then only that
        // portion of the threads context will be modified.
        //
        // If the context record is used as an IN OUT parameter to capture
        // the context of a thread, then only those portions of the thread's
        // context corresponding to set flags will be returned.
        //
        // The context record is never used as an OUT only parameter.
        //

        internal uint   ContextFlags;

        //
        // This section is specified/returned if CONTEXT_DEBUG_REGISTERS is
        // set in ContextFlags.  Note that CONTEXT_DEBUG_REGISTERS is NOT
        // included in CONTEXT_FULL.
        //

        internal uint   Dr0;
        internal uint   Dr1;
        internal uint   Dr2;
        internal uint   Dr3;
        internal uint   Dr6;
        internal uint   Dr7;

        //
        // This section is specified/returned if the
        // ContextFlags word contains the flag CONTEXT_FLOATING_POINT.
        //

        internal X86Fp387SaveArea   FloatSave;

        //
        // This section is specified/returned if the
        // ContextFlags word contains the flag CONTEXT_SEGMENTS.
        //

        internal uint   SegGs;
        internal uint   SegFs;
        internal uint   SegEs;
        internal uint   SegDs;

        //
        // This section is specified/returned if the
        // ContextFlags word contains the flag CONTEXT_INTEGER.
        //

        internal uint   Edi;
        internal uint   Esi;
        internal uint   Ebx;
        internal uint   Edx;
        internal uint   Ecx;
        internal uint   Eax;

        //
        // This section is specified/returned if the
        // ContextFlags word contains the flag CONTEXT_CONTROL.
        //

        internal uint   Ebp;
        internal uint   Eip;
        internal uint   SegCs;              // MUST BE SANITIZED
        internal uint   EFlags;             // MUST BE SANITIZED
        internal uint   Esp;
        internal uint   SegSs;

        //
        // This section is specified/returned if the ContextFlags word
        // contains the flag CONTEXT_EXTENDED_REGISTERS.
        // The format and contexts are processor specific
        // Note that this field is has N mod 16 = 12 alignment.
        //
        internal X86XmmSaveArea   ExtendedRegisters;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86Descriptor {
        internal ushort Pad;
        internal ushort Limit;
        internal uint   Base;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86SegmentRegisters {
        internal ushort SegCs;
        internal ushort SegDs;
        internal ushort SegEs;
        internal ushort SegFs;
        internal ushort SegGs;
        internal ushort SegSs;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86KSpecialRegisters {
        internal uint   Cr0;
        internal uint   Cr2;
        internal uint   Cr3;
        internal uint   Cr4;
        internal uint   KernelDr0;
        internal uint   KernelDr1;
        internal uint   KernelDr2;
        internal uint   KernelDr3;
        internal uint   KernelDr6;
        internal uint   KernelDr7;
        internal X86Descriptor  Gdtr;
        internal X86Descriptor  Idtr;
        internal ushort Tr;
        internal ushort Ldtr;

        private uint    Reserved0;
        private uint    Reserved1;
        private uint    Reserved2;
        private uint    Reserved3;
        private uint    Reserved4;
        private uint    Reserved5;
    };

    //
    // Processor State frame: Before a processor freezes itself, it
    // dumps the processor state to the processor state frame for
    // debugger to examine.
    //

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86KProcessorState {
        internal X86Context             ContextFrame;
        internal X86KSpecialRegisters   SpecialRegisters;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86KdControlReport {
        internal uint   Dr6;
        internal uint   Dr7;
        internal ushort InstructionCount;
        internal ushort ReportFlags;
        internal InstructionStream  InstructionStream;
        internal ushort SegCs;
        internal ushort SegDs;
        internal ushort SegEs;
        internal ushort SegFs;
        internal uint   EFlags;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X86KdControlSet {
        internal uint   ContinueStatus;
        internal uint   TraceFlag;
        internal uint   Dr7;
        internal uint   CurrentSymbolStart;
        internal uint   CurrentSymbolEnd;
    };

    ///////////////////////////////////////////////////////////////////////// X64.
    //
    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X64VectorRegisters {
        internal UInt128    Vr0;
        internal UInt128    Vr1;
        internal UInt128    Vr2;
        internal UInt128    Vr3;
        internal UInt128    Vr4;
        internal UInt128    Vr5;
        internal UInt128    Vr6;
        internal UInt128    Vr7;
        internal UInt128    Vr8;
        internal UInt128    Vr9;
        internal UInt128    Vr10;
        internal UInt128    Vr11;
        internal UInt128    Vr12;
        internal UInt128    Vr13;
        internal UInt128    Vr14;
        internal UInt128    Vr15;
        internal UInt128    Vr16;
        internal UInt128    Vr17;
        internal UInt128    Vr18;
        internal UInt128    Vr19;
        internal UInt128    Vr20;
        internal UInt128    Vr21;
        internal UInt128    Vr22;
        internal UInt128    Vr23;
        internal UInt128    Vr24;
        internal UInt128    Vr25;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X64XmmSaveArea {
        internal ushort ControlWord;
        internal ushort StatusWord;
        internal ushort TagWord;
        internal ulong  ErrorAddress;
        internal ulong  DataAddress;
        internal uint   MxCsr;
        internal uint   MxCsrMask;

        internal X86Unaligned128    St0;
        internal X86Unaligned128    St1;
        internal X86Unaligned128    St2;
        internal X86Unaligned128    St3;
        internal X86Unaligned128    St4;
        internal X86Unaligned128    St5;
        internal X86Unaligned128    St6;
        internal X86Unaligned128    St7;

        internal X86Unaligned128    Xmm0;
        internal X86Unaligned128    Xmm1;
        internal X86Unaligned128    Xmm2;
        internal X86Unaligned128    Xmm3;
        internal X86Unaligned128    Xmm4;
        internal X86Unaligned128    Xmm5;
        internal X86Unaligned128    Xmm6;
        internal X86Unaligned128    Xmm7;
        internal X86Unaligned128    Xmm8;
        internal X86Unaligned128    Xmm9;
        internal X86Unaligned128    Xmm10;
        internal X86Unaligned128    Xmm11;
        internal X86Unaligned128    Xmm12;
        internal X86Unaligned128    Xmm13;
        internal X86Unaligned128    Xmm14;
        internal X86Unaligned128    Xmm15;

        private X86Unaligned128     ReservedReg0;
        private X86Unaligned128     ReservedReg1;
        private X86Unaligned128     ReservedReg2;
        private X86Unaligned128     ReservedReg3;
        private X86Unaligned128     ReservedReg4;
        private X86Unaligned128     ReservedReg5;
    };

    //
    // Context Frame
    //
    //  This frame has a several purposes: 1) it is used as an argument to
    //  NtContinue, 2) is is used to construct a call frame for APC delivery,
    //  and 3) it is used in the user level thread creation routines.
    //
    //
    // The flags field within this record controls the contents of a CONTEXT
    // record.
    //
    // If the context record is used as an input parameter, then for each
    // portion of the context record controlled by a flag whose value is
    // set, it is assumed that that portion of the context record contains
    // valid context. If the context record is being used to modify a threads
    // context, then only that portion of the threads context is modified.
    //
    // If the context record is used as an output parameter to capture the
    // context of a thread, then only those portions of the thread's context
    // corresponding to set flags will be returned.
    //
    // CONTEXT_CONTROL specifies SegSs, Rsp, SegCs, Rip, and EFlags.
    //
    // CONTEXT_INTEGER specifies Rax, Rcx, Rdx, Rbx, Rbp, Rsi, Rdi, and R8-R15.
    //
    // CONTEXT_SEGMENTS specifies SegDs, SegEs, SegFs, and SegGs.
    //
    // CONTEXT_DEBUG_REGISTERS specifies Dr0-Dr3 and Dr6-Dr7.
    //
    // CONTEXT_MMX_REGISTERS specifies the floating point and extended registers
    //     Mm0/St0-Mm7/St7 and Xmm0-Xmm15).
    //

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X64Context {

        //
        // Register parameter home addresses.
        //
        // N.B. These fields are for convenience - they could be used to extend the
        //      context record in the future.
        //

        internal ulong  P1Home;
        internal ulong  P2Home;
        internal ulong  P3Home;
        internal ulong  P4Home;
        internal ulong  P5Home;
        internal ulong  P6Home;

        //
        // Control flags.
        //

        internal uint   ContextFlags;
        internal uint   MxCsr;

        //
        // Segment Registers and processor flags.
        //

        internal ushort SegCs;
        internal ushort SegDs;
        internal ushort SegEs;
        internal ushort SegFs;
        internal ushort SegGs;
        internal ushort SegSs;
        internal uint   EFlags;

        //
        // Debug registers
        //

        internal ulong  Dr0;
        internal ulong  Dr1;
        internal ulong  Dr2;
        internal ulong  Dr3;
        internal ulong  Dr6;
        internal ulong  Dr7;

        //
        // Integer registers.
        //

        internal ulong  Rax;
        internal ulong  Rcx;
        internal ulong  Rdx;
        internal ulong  Rbx;
        internal ulong  Rsp;
        internal ulong  Rbp;
        internal ulong  Rsi;
        internal ulong  Rdi;
        internal ulong  R8;
        internal ulong  R9;
        internal ulong  R10;
        internal ulong  R11;
        internal ulong  R12;
        internal ulong  R13;
        internal ulong  R14;
        internal ulong  R15;

        //
        // Program counter.
        //

        internal ulong  Rip;

        //
        // Floating point state.
        //

        internal X64XmmSaveArea FltSave;

        //
        // Vector registers.
        //

        internal X64VectorRegisters VectorRegister;
        internal ulong  VectorControl;

        //
        // Special debug control registers.
        //

        internal ulong  DebugControl;
        internal ulong  LastBranchToRip;
        internal ulong  LastBranchFromRip;
        internal ulong  LastExceptionToRip;
        internal ulong  LastExceptionFromRip;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X64Descriptor {
        internal ushort Pad0;
        internal ushort Pad1;
        internal ushort Pad2;
        internal ushort Limit;
        internal ulong  Base;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X64KSpecialRegisters {
        internal ulong  Cr0;
        internal ulong  Cr2;
        internal ulong  Cr3;
        internal ulong  Cr4;
        internal ulong  KernelDr0;
        internal ulong  KernelDr1;
        internal ulong  KernelDr2;
        internal ulong  KernelDr3;
        internal ulong  KernelDr6;
        internal ulong  KernelDr7;
        internal X64Descriptor  Gdtr;
        internal X64Descriptor  Idtr;
        internal ushort Tr;
        internal ushort Ldtr;
        internal uint   MxCsr;
        internal ulong  DebugControl;
        internal ulong  LastBranchToRip;
        internal ulong  LastBranchFromRip;
        internal ulong  LastExceptionToRip;
        internal ulong  LastExceptionFromRip;
        internal ulong  Cr8;
        internal ulong  MsrGsBase;
        internal ulong  MsrGsSwap;
        internal ulong  MsrStar;
        internal ulong  MsrLStar;
        internal ulong  MsrCStar;
        internal ulong  MsrSyscallMask;
    };

    //
    // Processor State frame: Before a processor freezes itself, it
    // dumps the processor state to the processor state frame for
    // debugger to examine.
    //

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X64KProcessorState {
        internal X64KSpecialRegisters   SpecialRegisters;
        private ulong                   Fill;
        X64Context                      ContextFrame;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X64KdControlReport {
        internal ulong  Dr6;
        internal ulong  Dr7;
        internal uint   EFlags;
        internal ushort InstructionCount;
        internal ushort ReportFlags;
        internal InstructionStream InstructionStream;
        internal ushort SegCs;
        internal ushort SegDs;
        internal ushort SegEs;
        internal ushort SegFs;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct X64KdControlSet {
        internal uint   ContinueStatus;
        internal uint   TraceFlag;
        internal ulong  Dr7;
        internal ulong  CurrentSymbolStart;
        internal ulong  CurrentSymbolEnd;
    };

    ///////////////////////////////////////////////////////////////////////// ARM.
    //

    //
    // Context Frame
    //
    //  This frame has a several purposes: 1) it is used as an argument to
    //  NtContinue, 2) is is used to constuct a call frame for APC delivery,
    //  and 3) it is used in the user level thread creation routines.
    //
    //
    // The flags field within this record controls the contents of a CONTEXT
    // record.
    //
    // If the context record is used as an input parameter, then for each
    // portion of the context record controlled by a flag whose value is
    // set, it is assumed that that portion of the context record contains
    // valid context. If the context record is being used to modify a threads
    // context, then only that portion of the threads context is modified.
    //
    // If the context record is used as an output parameter to capture the
    // context of a thread, then only those portions of the thread's context
    // corresponding to set flags will be returned.
    //
    // _ARM_WORKAROUND_ needs updating
    // CONTEXT_CONTROL specifies
    //
    // CONTEXT_FLOATING_POINT specifies
    //
    // CONTEXT_SEGMENTS specifies
    //
    // CONTEXT_DEBUG_REGISTERS
    //

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct ArmContext {

        //
        // Control flags.
        //

        internal uint   ContextFlags;

        //
        // Integer registers
        //

        internal uint   R0;
        internal uint   R1;
        internal uint   R2;
        internal uint   R3;
        internal uint   R4;
        internal uint   R5;
        internal uint   R6;
        internal uint   R7;
        internal uint   R8;
        internal uint   R9;
        internal uint   R10;
        internal uint   R11;
        internal uint   R12;

        //
        // Control Registers
        //

        internal uint   Sp;
        internal uint   Lr;
        internal uint   Pc;
        internal uint   Cpsr;
    };

    //
    // Define function table entry - a function table entry is generated for
    // each frame function.
    //

    // _ARM_WORKAROUND_ define RUNTIME_FUNCTION_INDIRECT 0x1 what is this?

    //
    // Define function table entry - a function table entry is generated for
    // each frame function.
    //
    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct ArmRuntimeFunction {
        internal uint   BeginAddress;
        internal uint   Flags;
        // Flags =>
        //  PrologLen : 8;
        //  FuncLen : 22;
        //  ThirtyTwoBit : 1;
        //  ExceptionFlag : 1;
    };

    //
    // Define exception data structure that can be found just before the
    // start of a function with an exception handler according to ARM
    // compiler conventions.  each frame function.
    //
    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct ArmRuntimeFunctionException {
        internal uint   Handler;        // was PVOID
        internal uint   HandlerData;    // was PVOID
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct ArmKSpecialRegisters {
        internal uint   Cp15Cr0Id;
        internal uint   Cp15Cr0Cachetype;
        internal uint   Cp15Cr1Control;
        internal uint   Cp15Cr2Ttb;
        internal uint   Cp15Cr3Dacr;
        internal uint   Cp15Cr5FaultStatus;
        internal uint   Cp15Cr5FaultAddress;
        internal uint   Cp15Cr13ProcessId;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct ArmKProcessorState {
        internal ArmKSpecialRegisters   SpecialRegisters;
        internal ArmContext             ContextFrame;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct ArmKdControlReport {
        internal uint   Cpsr;
        internal uint   InstructionCount;
        internal InstructionStream  InstructionStream;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct ArmKdControlSet {
        internal uint   ContinueStatus;
        internal uint   Continue;
        internal uint   CurrentSymbolStart;
        internal uint   CurrentSymbolEnd;
    };

    /////////////////////////////////////////////////////////////////////// Alpha.
    //
    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct AlphaKdControlReport {
        internal uint   InstructionCount;
        internal InstructionStream  InstructionStream;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct AlphaKdControlSet {
        internal uint   ContinueStatus;
        private uint    __padding;
    };

    //////////////////////////////////////////////////////////////////////// IA64.
    //
    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct Ia64KdControlReport {
        internal uint   InstructionCount;
        internal InstructionStream InstructionStream;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct Ia64KdControlSet {
        internal uint   ContinueStatus;
        internal uint   Continue;
        internal ulong  CurrentSymbolStart;
        internal ulong  CurrentSymbolEnd;
    };

    [AccessedByRuntime("referenced from c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential)]
    internal struct ExceptionRecord64 {
        internal uint   ExceptionCode;
        internal uint   ExceptionFlags;
        internal ulong  ExceptionRecord;
        internal ulong  ExceptionAddress;
        internal uint   NumberParameters;
        internal uint   __unusedAlignment;
        internal ulong  ExceptionInformation0;
        internal ulong  ExceptionInformation1;
        internal ulong  ExceptionInformation2;
        internal ulong  ExceptionInformation3;
        internal ulong  ExceptionInformation4;
        internal ulong  ExceptionInformation5;
        internal ulong  ExceptionInformation6;
        internal ulong  ExceptionInformation7;
        internal ulong  ExceptionInformation8;
        internal ulong  ExceptionInformation9;
        internal ulong  ExceptionInformation10;
        internal ulong  ExceptionInformation11;
        internal ulong  ExceptionInformation12;
        internal ulong  ExceptionInformation13;
        internal ulong  ExceptionInformation14;
    };
}

///////////////////////////////////////////////////////////////// End of File.
