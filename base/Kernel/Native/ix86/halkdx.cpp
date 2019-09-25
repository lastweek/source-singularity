///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   halkdx86.cpp - Processor-specific support routines for halkd.cpp.
//
#include "hal.h"
#include "halkd.h"

#define KDDBG if (0) kdprintf

extern "C" void *  __cdecl memcpy(void *, const void *, size_t);

//////////////////////////////////////////////// User visible progress beacon.
//
static UINT16 KdpSpinBase = 0x2f00;
void KdpSpin()
{
    if (KdpSpinBase != 0) {
        static UINT8 state = 0;

        // Write the spinner to the screen.
        *((UINT16 *)0xb809e) = KdpSpinBase + ("+-|*" [state++ & 0x3]);
    }
}

///////////////////////////////////////// Debugger Unique Interrupts Routines.
//
//  NB: Without these, we share routines with the mainline code and we get
//  caught in a loop when the debugger inserts a break after the pushfd when
//  someone tries to single step through Processor:g_DisableInterrupts!
//
bool __declspec(naked) KdpDisableInterruptsInline()
{
    __asm {
        pushfd;
        pop eax;
        test eax, Struct_Microsoft_Singularity_Isal_IX_EFlags_IF;
        setnz al;
        nop;    // required so that the linker doesn't combine with g_Disable
        cli;
        ret;
    }
}

void __declspec(naked) KdpRestoreInterruptsInline(bool enabled)
{
    __asm {
        nop;
        test cl, cl;
        je done;
        nop;    // required so that the linker doesn't combine with g_Restore
        sti;
      done:
        ret;
    }
}

// Pause processor in deference to other hardware threads on the same core.
void __declspec(naked) KdpPause()
{
    __asm {
        pause;
        ret;
    }
}

// Flush instruction cache.
void __declspec(naked) KdpFlushInstCache()
{
    __asm {
        wbinvd;   // privileged instruction
        ret;
    }
}

// Break into the debugger.
void __declspec(naked) Class_Microsoft_Singularity_DebugStub::g_Break()
{
    __asm {
        int 3;
        ret;
    }
}

// Read a machine specific register (MSR on x86 & x64).
bool KdpReadMsr(UINT32 msr, UINT32 *plo, UINT32 *phi)
{
    UINT32 lo;
    UINT32 hi;

    __asm {
        mov ecx, msr;
        rdmsr;
        mov hi, edx;
        mov lo, eax;
    }

    *phi = hi;
    *plo = lo;

    return true;
}

// Write a machine specific register (MSR on x86 & x64).
bool KdpWriteMsr(UINT32 msr, UINT32 lo, UINT32 hi)
{
    __asm {
        mov ecx, msr;
        mov edx, hi;
        mov eax, lo;
        wrmsr;
    }
    return true;
}

//////////////////////////////////////////////////////////////////////////////
//
void KdpToKdContext(IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *singularity,
                    OUT CONTEXT *windbg)
{
    windbg->ContextFlags = (CONTEXT_CONTROL |
                            CONTEXT_INTEGER |
                            CONTEXT_SEGMENTS |
                            CONTEXT_FLOATING_POINT |
                            CONTEXT_EXTENDED_REGISTERS);

    // CONTEXT_FULL;
    windbg->Eax = singularity->ax;
    windbg->Ebx = singularity->bx;
    windbg->Ecx = singularity->cx;
    windbg->Edx = singularity->dx;
    windbg->Esp = singularity->sp;
    windbg->Ebp = singularity->bp;
    windbg->Esi = singularity->si;
    windbg->Edi = singularity->di;
    windbg->Eip = singularity->ip;
    windbg->EFlags = singularity->fl;

    windbg->FloatSave.ControlWord = singularity->mmx.fcw;
    windbg->FloatSave.StatusWord = singularity->mmx.fsw;
    windbg->FloatSave.TagWord = singularity->mmx.ftw;
    windbg->FloatSave.ErrorOffset = singularity->mmx.ip;
    windbg->FloatSave.ErrorSelector = singularity->mmx.cs;
    windbg->FloatSave.DataOffset = singularity->mmx.dp;
    windbg->FloatSave.DataSelector = singularity->mmx.ds;

    memcpy(&windbg->FloatSave.St0, &singularity->mmx.st0, 10);
    memcpy(&windbg->FloatSave.St1, &singularity->mmx.st1, 10);
    memcpy(&windbg->FloatSave.St2, &singularity->mmx.st2, 10);
    memcpy(&windbg->FloatSave.St3, &singularity->mmx.st3, 10);
    memcpy(&windbg->FloatSave.St4, &singularity->mmx.st4, 10);
    memcpy(&windbg->FloatSave.St5, &singularity->mmx.st5, 10);
    memcpy(&windbg->FloatSave.St6, &singularity->mmx.st6, 10);
    memcpy(&windbg->FloatSave.St7, &singularity->mmx.st7, 10);

    memcpy(&windbg->ExtendedRegisters, &singularity->mmx, 512);

    // Segment registers other than cs don't change so they are live
    windbg->SegCs = singularity->cs;
    __asm {
        mov ebx, windbg;

        xor eax, eax;
        mov ax, gs;
        mov [ebx]CONTEXT.SegGs, eax;
        mov ax, fs;
        mov [ebx]CONTEXT.SegFs, eax;
        mov ax, es;
        mov [ebx]CONTEXT.SegEs, eax;
        mov ax, ds;
        mov [ebx]CONTEXT.SegDs, eax;
        mov ax, ss;
        mov [ebx]CONTEXT.SegSs, eax;
    }
}

void KdpFromKdContext(IN CONST CONTEXT *windbg,
                      OUT Struct_Microsoft_Singularity_Isal_SpillContext *singularity)
{
    singularity->ax = windbg->Eax;
    singularity->bx = windbg->Ebx;
    singularity->cx = windbg->Ecx;
    singularity->dx = windbg->Edx;
    singularity->sp = windbg->Esp;
    singularity->bp = windbg->Ebp;
    singularity->si = windbg->Esi;
    singularity->di = windbg->Edi;
    singularity->ip = windbg->Eip;
    singularity->fl = windbg->EFlags;

    // CONTEXT_FLOATING_POINT
    if (windbg->ContextFlags & CONTEXT_FLOATING_POINT) {
        singularity->mmx.fcw = windbg->FloatSave.ControlWord;
        singularity->mmx.fsw = windbg->FloatSave.StatusWord;
        singularity->mmx.ftw = windbg->FloatSave.TagWord;
        singularity->mmx.cs = windbg->FloatSave.ErrorSelector;
        singularity->mmx.ip = windbg->FloatSave.ErrorOffset;
        singularity->mmx.ds = windbg->FloatSave.DataSelector;
        singularity->mmx.dp = windbg->FloatSave.DataOffset;
        memcpy(&singularity->mmx.st0, &windbg->FloatSave.St0, 10);
        memcpy(&singularity->mmx.st1, &windbg->FloatSave.St1, 10);
        memcpy(&singularity->mmx.st2, &windbg->FloatSave.St2, 10);
        memcpy(&singularity->mmx.st3, &windbg->FloatSave.St3, 10);
        memcpy(&singularity->mmx.st4, &windbg->FloatSave.St4, 10);
        memcpy(&singularity->mmx.st5, &windbg->FloatSave.St5, 10);
        memcpy(&singularity->mmx.st6, &windbg->FloatSave.St6, 10);
        memcpy(&singularity->mmx.st7, &windbg->FloatSave.St7, 10);
    }

    // CONTEXT_EXTENDED_REGISTERS
    if (windbg->ContextFlags & CONTEXT_EXTENDED_REGISTERS) {
        memcpy(&singularity->mmx, &windbg->ExtendedRegisters, 512);
    }
}

void KdpSetControlReport(IN OUT PDBGKD_CONTROL_REPORT report,
                         IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *x86Context)
    //  Routine Description:
    //      Fill in the Wait_State_Change message record.
    //
    //  Arguments:
    //      WaitStateChange - Supplies pointer to record to fill in
    //      x86Context - Supplies a pointer to a context record.
{
    UINT32 _dr6;
    UINT32 _dr7;
    UINT16 _cs;
    UINT16 _ds;
    UINT16 _es;
    UINT16 _fs;

    __asm {
        mov eax, dr6;
        mov _dr6, eax;
        mov eax, dr7;
        mov _dr7, eax;

        mov ax, cs;
        mov _cs, ax;
        mov ax, ds;
        mov _ds, ax;
        mov ax, es;
        mov _es, ax;
        mov ax, fs;
        mov _fs, ax;
    }

    report->Dr6 = _dr6;
    report->Dr7 = _dr7;
    report->SegCs  = _cs;
    report->SegDs  = _ds;
    report->SegEs  = _es;
    report->SegFs  = _fs;
    report->EFlags = x86Context->fl;
    report->ReportFlags = X86_REPORT_INCLUDES_SEGS;

#if !PAGING
    // Let the debugger know so that it doesn't have to retrieve the CS descriptor.
    report->ReportFlags |= X86_REPORT_STANDARD_CS;
#endif
}

void KdpSetControlSet(IN CONST DBGKD_CONTROL_SET * control,
                      IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *x86Context)
{
    if (control->TraceFlag) {
        //KDDBG("KD: Warning - trace flag set prev efl=%x\n",x86Context->efl);
        x86Context->fl |= Struct_Microsoft_Singularity_Isal_IX_EFlags_TF;
    }
    else {
        //KDDBG("KD: turning off tracing in efl\n");
        x86Context->fl &= ~Struct_Microsoft_Singularity_Isal_IX_EFlags_TF;
    }

    UINT32 _dr7 = control->Dr7;

    __asm {
        mov eax, _dr7;
        mov dr7, eax
    }
}

//////////////////////////////////////////////////////////////////////////////

void KdpReadSpecialRegisters(KSPECIAL_REGISTERS *pksp,
                             IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *x86Context)
{
    Struct_Microsoft_Singularity_Kd_X86Descriptor idtp;
    Struct_Microsoft_Singularity_Kd_X86Descriptor gdtp;

    __asm {
        mov ebx, pksp;

        sidt idtp.Limit;
        sgdt gdtp.Limit;

        mov eax, cr0;
        mov [ebx]KSPECIAL_REGISTERS.Cr0, eax;
        mov eax, cr2;
        mov [ebx]KSPECIAL_REGISTERS.Cr2, eax;
        mov eax, cr3;
        mov [ebx]KSPECIAL_REGISTERS.Cr3, eax;
        _emit 0x0f;  // mov eax,cr4
        _emit 0x20;
        _emit 0xe0;
        mov [ebx]KSPECIAL_REGISTERS.Cr4, eax;

        // Should we save segment regs as well?
        str ax;
        mov [ebx]KSPECIAL_REGISTERS.Tr, ax;
    }

    pksp->Idtr = idtp;
    pksp->Gdtr = gdtp;
}

void KdpWriteSpecialRegisters(CONST KSPECIAL_REGISTERS *pksp)
{
    __asm {
        mov ebx, pksp;

        mov eax, [ebx]KSPECIAL_REGISTERS.KernelDr0;
        mov dr0, eax;
        mov eax, [ebx]KSPECIAL_REGISTERS.KernelDr1;
        mov dr1, eax;
        mov eax, [ebx]KSPECIAL_REGISTERS.KernelDr2;
        mov dr2, eax;
        mov eax, [ebx]KSPECIAL_REGISTERS.KernelDr3;
        mov dr3, eax;
        mov eax, [ebx]KSPECIAL_REGISTERS.KernelDr6;
        mov dr6, eax;
        mov eax, [ebx]KSPECIAL_REGISTERS.KernelDr7;
        mov dr7, eax;
    }
}

//////////////////////////////////////////////////////////////////////////////

KdDebugTrapData * KdpIsDebugTrap(IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *context,
                                 int id)
{
    if (id == Struct_Microsoft_Singularity_Isal_IX_EVectors_FirstChanceException) {
        return (KdDebugTrapData *)(context->ax);
    }
    return NULL;
}

// Convert a trap into a exception record.
void KdpConvertTrapToException(IN OUT EXCEPTION_RECORD64 *per,
                               IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *context,
                               int id)
{
    // Breakpoints:
    switch (id) {

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_SingleStep:
            KDDBG("SingleStep\n");
            per->ExceptionCode = STATUS_SINGLE_STEP;
            per->ExceptionAddress = SIGN_EXTEND(context->ip);
            // context->efl &= ~Struct_Microsoft_Singularity_Isal_IX_EFlags_TF;
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_Breakpoint:
            KDDBG("Breakpoint\n");
            context->ip -= 1;
            per->ExceptionCode = STATUS_BREAKPOINT;
            per->NumberParameters = 1;
            per->ExceptionInformation0 = BREAKPOINT_BREAK;
            per->ExceptionAddress = SIGN_EXTEND(context->ip);
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_IllegalInstruction:
            KDDBG("Illegal Instruction\n");
            per->ExceptionCode = STATUS_ILLEGAL_INSTRUCTION;
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_PageFault:
            KDDBG("KD: 0x0E %d\n", id);
            per->ExceptionCode = STATUS_ACCESS_VIOLATION;
            per->ExceptionAddress = SIGN_EXTEND(context->ip);
            per->NumberParameters = 1;
            {
                UINT32 _cr2;
                __asm {
                    mov eax, cr2;
                    mov _cr2, eax;
                }
                per->ExceptionInformation0 = SIGN_EXTEND(_cr2);
            }
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_FirstChanceException: {
            KdDebugTrapData *trapData = (KdDebugTrapData *) (context->ax);
            switch (trapData->tag) {
                case KdDebugTrapData::FIRST_CHANCE_EXCEPTION:
                    context->ax = trapData->firstChanceException.throwAddr;
                    KDDBG("KD: First chance C# exception\n");
                    // per->ExceptionCode = STATUS_CPP_EH_EXCEPTION; //0xe06d7363;
                    per->ExceptionCode = STATUS_VCPP_EXCEPTION; //0x8000ff1f;
                    per->ExceptionAddress = SIGN_EXTEND(context->ip);
                    per->NumberParameters = 1;
                    per->ExceptionInformation0 = BREAKPOINT_BREAK;
                    break;
                default:
                    KDDBG("KD: Unexpected interrupt %d\n", id);
                    per->ExceptionCode = 0x80000000 + id;
                    per->ExceptionAddress = SIGN_EXTEND(context->ip);
                    break;
            }
            break;
        }

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_SecondChanceException:
            KDDBG("KD: Second chance C# exception\n");
            per->ExceptionCode = STATUS_VCPP_EXCEPTION;
            per->ExceptionAddress = SIGN_EXTEND(context->ip);
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_DebuggerBreakRequest:
            KDDBG("KD: Debugger ctrl-break\n");
            per->ExceptionCode = STATUS_BREAKPOINT;
            per->ExceptionInformation0 = BREAKPOINT_BREAK;
            per->ExceptionAddress = SIGN_EXTEND(context->ip);
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_Nmi:
            KDDBG("KD: NMI exception\n");
            per->ExceptionCode = STATUS_UNHANDLED_EXCEPTION;
            per->ExceptionInformation0 = BREAKPOINT_BREAK;
            per->ExceptionAddress = SIGN_EXTEND(context->ip);
            break;

        default:
            KDDBG("KD: Unexpected interrupt %d\n", id);
            per->ExceptionCode = 0x80000000 + id;
            per->ExceptionAddress = SIGN_EXTEND(context->ip);
            break;

    }

    KDDBG("Trap: Context at %p\n", context);
    KDDBG("  CXT=%08x  THR=%08x\n",
          context,
          Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext()->_thread);
    KDDBG("  EIP=%08x  EFL=%08x\n",
          context->ip, context->fl);
    KDDBG("  EAX=%08x  EBX=%08x  ECX=%08x  EDX=%08x\n",
          context->ax, context->bx, context->cx, context->dx);
    KDDBG("  ESP=%08x  EBP=%08x  ESI=%08x  EDI=%08x\n",
          context->sp, context->bp, context->si, context->di);
}

//
// Read or Write I/O Space.
//
// Return:
//
// iowrite == 0: value read from port
//
// iowrite !=0:  zero
//
int KdpReadWriteIoSpace(
    int      size,    // 1, 2, 4
    int      iowrite, // true if write, false if read
    unsigned short addr,
    unsigned int   value
    )
{
    unsigned int retValue = 0;

    if (iowrite != 0) {
        // I/O Write's

        if (size == 1) {
            unsigned char byteValue = (unsigned char)value;
            __outbyte(addr, value);
        }
        else if (size == 2) {
            unsigned short wordValue = (unsigned short)value;
            __outword(addr, value);
        }
        else if (size == 4) {
            __outdword(addr, value);
        }
    }
    else {
        // I/O Read's

        if (size == 1) {
            retValue = __inbyte(addr);
        }
        else if (size == 2) {
            retValue = __inword(addr);
        }
        else if (size == 4) {
            retValue = __indword(addr);
        }
    }

    return retValue;
}

