///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   halkdx64.cpp - Processor-specific support routines for halkd.cpp.
//
#include "hal.h"
#include "halkd.h"

#define KDDBG if (0) kdprintf

extern "C" void *  __cdecl memcpy(void *, const void *, size_t);

void KdpX64GetSegmentRegisters(OUT CONTEXT * windbg);
UINT64 KdpX64ReadMsr(UINT32 msr);
void KdpX64WriteMsr(UINT32 msr, UINT64 value);
void KdpX64SetControlReport(IN OUT PDBGKD_CONTROL_REPORT report);
void KdpX64SetControlSet(IN CONST DBGKD_CONTROL_SET *report);
void KdpX64ReadSpecialRegisters(IN OUT KSPECIAL_REGISTERS *pksp);
void KdpX64WriteSpecialRegisters(IN CONST KSPECIAL_REGISTERS *pksp);

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

// Read a machine specific register (MSR on x86 & x64).
bool KdpReadMsr(UINT32 msr, UINT32 *plo, UINT32 *phi)
{
    UINT64 value = KdpX64ReadMsr(msr);
    *phi = (UINT32)(value >> 32);
    *plo = (UINT32)(value >> 0);
    return true;
}

// Write a machine specific register (MSR on x86 & x64).
bool KdpWriteMsr(UINT32 msr, UINT32 lo, UINT32 hi)
{
    UINT64 value = (((UINT64)hi) << 32) | (((UINT64)lo) << 0);
    KdpX64WriteMsr(msr, value);
    return true;
}

//////////////////////////////////////////////////////////////////////////////

void KdpToKdContext(IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *singularity,
                    OUT CONTEXT *windbg)
{
    windbg->ContextFlags = (CONTEXT_CONTROL |
                            CONTEXT_INTEGER |
                            CONTEXT_SEGMENTS |
                            CONTEXT_FLOATING_POINT);

    // CONTEXT_FULL;
    windbg->Rax = singularity->ax;
    windbg->Rbx = singularity->bx;
    windbg->Rcx = singularity->cx;
    windbg->Rdx = singularity->dx;
    windbg->Rsp = singularity->sp;
    windbg->Rbp = singularity->bp;
    windbg->Rsi = singularity->si;
    windbg->Rdi = singularity->di;
    windbg->Rip = singularity->ip;
    windbg->R8  = singularity->r8;
    windbg->R9  = singularity->r9;
    windbg->R10 = singularity->r10;
    windbg->R11 = singularity->r11;
    windbg->R12 = singularity->r12;
    windbg->R13 = singularity->r13;
    windbg->R14 = singularity->r14;
    windbg->R15 = singularity->r15;
    windbg->EFlags = (uint32)singularity->fl;

    windbg->FltSave.ControlWord = singularity->mmx.fcw;
    windbg->FltSave.StatusWord = singularity->mmx.fsw;
    windbg->FltSave.TagWord = singularity->mmx.ftw;
    windbg->FltSave.ErrorAddress = singularity->mmx.ip;
    windbg->FltSave.DataAddress = singularity->mmx.dp;

    memcpy(&windbg->FltSave.St0, &singularity->mmx.st0, 16);
    memcpy(&windbg->FltSave.St1, &singularity->mmx.st1, 16);
    memcpy(&windbg->FltSave.St2, &singularity->mmx.st2, 16);
    memcpy(&windbg->FltSave.St3, &singularity->mmx.st3, 16);
    memcpy(&windbg->FltSave.St4, &singularity->mmx.st4, 16);
    memcpy(&windbg->FltSave.St5, &singularity->mmx.st5, 16);
    memcpy(&windbg->FltSave.St6, &singularity->mmx.st6, 16);
    memcpy(&windbg->FltSave.St7, &singularity->mmx.st7, 16);

    KdpX64GetSegmentRegisters(windbg);

    //
    // This section is specified/returned if the
    // ContextFlags word contains the flag CONTEXT_CONTROL.
    //

    windbg->SegCs = (uint16)singularity->cs;
}

void KdpFromKdContext(IN CONST CONTEXT *windbg,
                      OUT Struct_Microsoft_Singularity_Isal_SpillContext *singularity)
{
    singularity->ax = windbg->Rax;
    singularity->bx = windbg->Rbx;
    singularity->cx = windbg->Rcx;
    singularity->dx = windbg->Rdx;
    singularity->sp = windbg->Rsp;
    singularity->bp = windbg->Rbp;
    singularity->si = windbg->Rsi;
    singularity->di = windbg->Rdi;
    singularity->ip = windbg->Rip;
    singularity->r8  = windbg->R8;
    singularity->r9  = windbg->R9;
    singularity->r10 = windbg->R10;
    singularity->r11 = windbg->R11;
    singularity->r12 = windbg->R12;
    singularity->r13 = windbg->R13;
    singularity->r14 = windbg->R14;
    singularity->r15 = windbg->R15;
    singularity->fl = windbg->EFlags;

    // CONTEXT_FLOATING_POINT
    if (windbg->ContextFlags & CONTEXT_FLOATING_POINT) {
        singularity->mmx.fcw = windbg->FltSave.ControlWord;
        singularity->mmx.fsw = windbg->FltSave.StatusWord;
        singularity->mmx.ftw = windbg->FltSave.TagWord;
        singularity->mmx.ip = windbg->FltSave.ErrorAddress;
        singularity->mmx.dp = windbg->FltSave.DataAddress;

        memcpy(&singularity->mmx.st0, &windbg->FltSave.St0, 16);
        memcpy(&singularity->mmx.st1, &windbg->FltSave.St1, 16);
        memcpy(&singularity->mmx.st2, &windbg->FltSave.St2, 16);
        memcpy(&singularity->mmx.st3, &windbg->FltSave.St3, 16);
        memcpy(&singularity->mmx.st4, &windbg->FltSave.St4, 16);
        memcpy(&singularity->mmx.st5, &windbg->FltSave.St5, 16);
        memcpy(&singularity->mmx.st6, &windbg->FltSave.St6, 16);
        memcpy(&singularity->mmx.st7, &windbg->FltSave.St7, 16);
    }
}

void KdpSetControlReport(IN OUT PDBGKD_CONTROL_REPORT report,
                         IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *x86Context)
    //  Routine Description:
    //      Fill in the DBGKD_CONTROL_REPORT record.
    //
    //  Arguments:
    //      WaitStateChange - Supplies pointer to record to fill in
    //      x86Context - Supplies a pointer to a context record.
{
    KdpX64SetControlReport(report);

    // report->EFlags = (uint32)x86Context->efl;
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

    KdpX64SetControlSet(control);
}

//////////////////////////////////////////////////////////////////////////////

void KdpReadSpecialRegisters(KSPECIAL_REGISTERS *pksp,
                             IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *x86Context)
{
    KdpX64ReadSpecialRegisters(pksp);
}

void KdpWriteSpecialRegisters(CONST KSPECIAL_REGISTERS *pksp)
{
    KdpX64WriteSpecialRegisters(pksp);
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
            per->ExceptionAddress = (UINT64)context->ip;
            // context->efl &= ~Struct_Microsoft_Singularity_Isal_IX_EFlags_TF;
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_Breakpoint:
            KDDBG("Breakpoint\n");
            context->ip -= 1;
            per->ExceptionCode = STATUS_BREAKPOINT;
            per->NumberParameters = 1;
            per->ExceptionInformation0 = BREAKPOINT_BREAK;
            per->ExceptionAddress = (UINT64)context->ip;
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_IllegalInstruction:
            KDDBG("Illegal Instruction\n");
            per->ExceptionCode = STATUS_ILLEGAL_INSTRUCTION;
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_PageFault:
            KDDBG("KD: 0x0E %d\n", id);
            per->ExceptionCode = STATUS_ACCESS_VIOLATION;
            per->ExceptionAddress = (UINT64)context->ip;
            per->NumberParameters = 1;
            per->ExceptionInformation0 = __readcr2();
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_FirstChanceException: {
            KdDebugTrapData *trapData = (KdDebugTrapData *) (context->ax);
            switch (trapData->tag) {
                case KdDebugTrapData::FIRST_CHANCE_EXCEPTION:
                    context->ax = trapData->firstChanceException.throwAddr;
                    KDDBG("KD: First chance C# exception\n");
                    // per->ExceptionCode = STATUS_CPP_EH_EXCEPTION; //0xe06d7363;
                    per->ExceptionCode = STATUS_VCPP_EXCEPTION; //0x8000ff1f;
                    per->ExceptionAddress = (UINT64)context->ip;
                    per->NumberParameters = 1;
                    per->ExceptionInformation0 = BREAKPOINT_BREAK;
                    break;
                default:
                    KDDBG("KD: Unexpected interrupt %d\n", id);
                    per->ExceptionCode = 0x80000000 + id;
                    per->ExceptionAddress = (UINT64)context->ip;
                    break;
            }
            break;
        }

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_SecondChanceException:
            KDDBG("KD: Second chance C# exception\n");
            per->ExceptionCode = STATUS_VCPP_EXCEPTION;
            per->ExceptionAddress = (UINT64)context->ip;
            break;

        case Struct_Microsoft_Singularity_Isal_IX_EVectors_DebuggerBreakRequest:
            KDDBG("KD: Debugger ctrl-break\n");
            per->ExceptionCode = STATUS_BREAKPOINT;
            per->ExceptionInformation0 = BREAKPOINT_BREAK;
            per->ExceptionAddress = (UINT64)context->ip;
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
            per->ExceptionAddress = (UINT64)context->ip;
            break;

    }

    KDDBG("Trap: Context at %p\n", context);
    KDDBG("  CXT=%08x  THR=%08x\n",
          context,
          Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext()->_thread);
    KDDBG("  RIP=%08x  EFL=%08x  ERR=%08x  CR2=%08x\n",
          context->ip, context->fl, id, __readcr2());
    KDDBG("  RAX=%08x  RBX=%08x  RCX=%08x  RDX=%08x\n",
          context->ax, context->bx, context->cx, context->dx);
    KDDBG("  RSP=%08x  RBP=%08x  RSI=%08x  RDI=%08x\n",
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


