///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   halkdarm.cpp - Processor-specific support routines for halkd.cpp.
//
#include "hal.h"
#include "halkd.h"

#define KDDBG if (0) kdprintf

extern "C" void *  __cdecl memcpy(void *, const void *, size_t);

void KdpArmSetControlReport(IN OUT PDBGKD_CONTROL_REPORT report);

//////////////////////////////////////////////// User visible progress beacon.
//
void KdpSpin()
{
#if 0
    extern uint16 * videoBuffer;
    static uint16 values[] = { 0x0000, 0xffff, 0xfc00, 0x03f0, 0x000f };


    if (videoBuffer != 0) {
        static UINT8 state = 0;

        videoBuffer[0] = values[state];
        videoBuffer[1] = values[state];
        videoBuffer[2] = values[state];
        videoBuffer[3] = values[state];
        videoBuffer[4] = values[state];
        videoBuffer[5] = values[state];
        videoBuffer[6] = values[state];
        videoBuffer[7] = values[state];

        state++;
        if (state >= arrayof(values)) {
            state = 0;
        }
    }
#endif
}

//////////////////////////////////////////////////////////////////////////////

void KdpToKdContext(IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *singularity,
                    OUT CONTEXT *windbg)
{
    windbg->ContextFlags = (CONTEXT_CONTROL |
                            CONTEXT_INTEGER);

    windbg->Sp = singularity->sp;
    windbg->Lr = singularity->lr;
    windbg->Pc = singularity->pc;
    windbg->R0 = singularity->r0;
    windbg->R1 = singularity->r1;
    windbg->R2 = singularity->r2;
    windbg->R3 = singularity->r3;
    windbg->R4 = singularity->r4;
    windbg->R5 = singularity->r5;
    windbg->R6 = singularity->r6;
    windbg->R7 = singularity->r7;
    windbg->R8 = singularity->r8;
    windbg->R9 = singularity->r9;
    windbg->R10 = singularity->r10;
    windbg->R11 = singularity->r11;
    windbg->R12 = singularity->r12;
    windbg->Cpsr = singularity->cpsr;
}

void KdpFromKdContext(IN CONST CONTEXT *windbg,
                      OUT Struct_Microsoft_Singularity_Isal_SpillContext *singularity)
{
    singularity->sp = windbg->Sp;
    singularity->lr = windbg->Lr;
    singularity->pc = windbg->Pc;
    singularity->r0 = windbg->R0;
    singularity->r1 = windbg->R1;
    singularity->r2 = windbg->R2;
    singularity->r3 = windbg->R3;
    singularity->r4 = windbg->R4;
    singularity->r5 = windbg->R5;
    singularity->r6 = windbg->R6;
    singularity->r7 = windbg->R7;
    singularity->r8 = windbg->R8;
    singularity->r9 = windbg->R9;
    singularity->r10 = windbg->R10;
    singularity->r11 = windbg->R11;
    singularity->r12 = windbg->R12;
    singularity->cpsr = windbg->Cpsr;
}

void KdpSetControlReport(IN OUT PDBGKD_CONTROL_REPORT report,
                         IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *singularity)
{
    KdpArmSetControlReport(report);

    report->Cpsr = singularity->cpsr;
}

void KdpSetControlSet(IN CONST DBGKD_CONTROL_SET * control,
                      IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *singularity)
{
    // TODO: This needs to be filled in.
}

//////////////////////////////////////////////////////////////////////////////

void KdpReadSpecialRegisters(KSPECIAL_REGISTERS *pksp,
                             IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *singularity)
{
#if 0
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
#endif

#if 0
    pksp->Cp15Cr0Id = _MoveFromCoprocessor(0, 15, 0, 7, 5, 0);
#endif
}

void KdpWriteSpecialRegisters(CONST KSPECIAL_REGISTERS *pksp)
{
#if 0
#endif
}

void KdpFlushInstCache(void)
{
    _MoveToCoprocessor(0, 15, 0, 7, 5, 0); // ICIALLU: Invalidate all instruction caches.
}

bool KdpReadMsr(UINT32 msr, UINT32 *plo, UINT32 *phi)
{
    *phi = 0;

    switch (msr) {
#undef VALID_COPROC_REGISTER
#define VALID_COPROC_REGISTER(_Coproc, _OpCode1, _CoReg1, _CoReg2, _OpCode2) \
        case (_Coproc << 16) | (_OpCode1 << 12) | (_CoReg1 << 8) | (_CoReg2 << 4) | _OpCode2 : \
            *plo = _MoveFromCoprocessor(_Coproc, _OpCode1, _CoReg1, _CoReg2, _OpCode2); \
            break;
#include "halkdmsr.h"

      default:
          return false;
    }
    return true;

}

bool KdpWriteMsr(UINT32 msr, UINT32 lo, UINT32 hi)
{
    switch (msr) {
#undef VALID_COPROC_REGISTER
#define VALID_COPROC_REGISTER(_Coproc, _OpCode1, _CoReg1, _CoReg2, _OpCode2) \
        case (_Coproc << 16) | (_OpCode1 << 12) | (_CoReg1 << 8) | (_CoReg2 << 4) | _OpCode2 : \
            _MoveToCoprocessor(lo, _Coproc, _OpCode1, _CoReg1, _CoReg2, _OpCode2); \
            break;
#include "halkdmsr.h"
        default:
          return false;
    }
    return true;
}

//////////////////////////////////////////////////////////////////////////////

KdDebugTrapData * KdpIsDebugTrap(IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *context,
                                 int id)
{
    if ((id == Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_SoftwareInterrupt) &&
        (context->instruction == 0xefffff2e)) {

        KDDBG("IsDebugTrap(%x) tag=%p\n", id, ((KdDebugTrapData *)(context->r0))->tag);
        return (KdDebugTrapData *)(context->r0);
    }
    KDDBG("IsDebugTrap(%x) NULL\n", id);
    return NULL;
}

// Convert a trap into a exception record.
void KdpConvertTrapToException(IN OUT EXCEPTION_RECORD64 *per,
                               IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *context,
                               int id)
{
    KDDBG("ConvertTrapToExc(%d)\n", id);
    KDDBG("  pc=%p [%p]\n", context->pc, *((uint32*)context->pc));
    KDDBG("  lr=%p r0=%p\n", context->lr, context->r0);

    // Breakpoints:
    switch (id) {

        case Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_UndefinedInstruction: {
            KDDBG("Illegal Instruction %08x\n", context->instruction);
            per->ExceptionCode = STATUS_ILLEGAL_INSTRUCTION;
            per->ExceptionAddress = SIGN_EXTEND(context->pc - 4);
            per->NumberParameters = 0;
            return;
        }

        case Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_PrefetchAbort: {
            KDDBG("KD: Prefetch Exception %d\n", id);
            per->ExceptionCode = STATUS_ACCESS_VIOLATION;
            per->ExceptionAddress = SIGN_EXTEND(context->pc);
            per->NumberParameters = 0;
            return;
        }

        case Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_DataAbort: {
            KDDBG("KD: Data Exception %d\n", id);
            per->ExceptionCode = STATUS_ACCESS_VIOLATION;
            // Should probably decode instruction to figure out the real faulty address.
            per->ExceptionAddress = SIGN_EXTEND(context->pc);
            per->NumberParameters = 0;
            return;
        }

        case Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_Reset:
        case Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_Irq:
        case Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_Fiq: {
            KDDBG("KD: Unexpected IRQ %d\n", id);
            per->ExceptionCode = STATUS_UNHANDLED_EXCEPTION;
            per->ExceptionAddress = SIGN_EXTEND(context->pc);
            per->NumberParameters = 1;
            per->ExceptionInformation0 = id;
            return;
        }

        case Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_SoftwareInterrupt: {
            switch (context->instruction) {
                case 0xefffff01: { // aka KDP_BREAKPOINT_VALUE (swi 0xffff01)
                    KDDBG("KD Single or Bkpt\n");
                    per->ExceptionCode = STATUS_SINGLE_STEP;
                    per->ExceptionAddress = SIGN_EXTEND(context->pc);
                    return;
                }

                case 0xefffff03: { // Hard-coded break (swi 0xffff03)
                    KDDBG("Breakpoint\n");
                    per->ExceptionCode = STATUS_BREAKPOINT;
                    per->NumberParameters = 1;
                    per->ExceptionInformation0 = BREAKPOINT_BREAK;
                    per->ExceptionAddress = SIGN_EXTEND(context->pc - 4);
                    return;
                }

                case 0xefffff2e: { // Debug notify (swi 0xffff2e)
                    KdDebugTrapData *trapData = (KdDebugTrapData *) (context->r0);
                    switch (trapData->tag) {
                        case KdDebugTrapData::FIRST_CHANCE_EXCEPTION:
                            context->r0 = trapData->firstChanceException.throwAddr;
                            KDDBG("KD: First chance C# exception\n");
                            // per->ExceptionCode = STATUS_CPP_EH_EXCEPTION; //0xe06d7363;
                            per->ExceptionCode = STATUS_VCPP_EXCEPTION; //0x8000ff1f;
                            per->ExceptionAddress = SIGN_EXTEND(context->pc - 4);
                            per->NumberParameters = 1;
                            per->ExceptionInformation0 = BREAKPOINT_BREAK;
                            return;

                        default:
                            KDDBG("KD: Bad trap 0x%x\n", id);
                            per->ExceptionCode = STATUS_UNHANDLED_EXCEPTION;
                            per->ExceptionAddress = SIGN_EXTEND(context->pc - 4);
                            per->NumberParameters = 1;
                            per->ExceptionInformation0 = id;
                            return;
                    }
                }

                default: {
                    KDDBG("KD: Unexpected SWI %08x\n", context->instruction);
                    per->ExceptionCode = STATUS_ILLEGAL_INSTRUCTION;
                    per->ExceptionAddress = SIGN_EXTEND(context->pc - 4);
                    return;
                }
            }
        }

        default:
            KDDBG("KD: Unexpected interrupt %d\n", id);
            per->ExceptionCode = 0x80000000 + id;
            per->ExceptionAddress = SIGN_EXTEND(context->pc);
            return;
    }
}

//
// Read or Write I/O Space.
//
// Return: Silently does nothing on ARM. Could be implemented
//         in the future to read/write from a simulated I/O space
//         if an ARM platform has such a mapping.
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
    return 0;
}


