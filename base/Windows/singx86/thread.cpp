/////////////////////////////////////////////////////////////////////////////
//
//  thread.cpp - Extension to select a Singularity thread.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
#include "singx86.h"

struct GDTE
{
    USHORT     limit;
    USHORT     base0_15;
    BYTE       base16_23;
    BYTE       access;
    BYTE       granularity;
    BYTE       base24_31;
};

static void Usage()
{
    ExtOut("Usage:\n"
           "    !thread {options} thread_addr\n"
           "Options:\n"
           "    -p show stack prior to interrupt or exception (if any)\n"
           "    -t show top stack (i.e. interrupt or exception (if any))\n"
           "Notes:\n"
           "    There are potentially three contexts associated with a thread:\n"
           "    the scheduler context, the interrupt context, and the exception\n"
           "    context.  The -p flag is only useful if an exception or interrupt\n"
           "    has occurred.  Using -p -p always gets the scheduler context.");
}

static PCSTR ParseArguments(PCSTR args,
                            OUT PLONG plPriorStack,
                            OUT PLONG plTopStack)
{
    *plPriorStack = 0;
    *plTopStack = 0;
    while (*args != '\0') {
        while (*args == ' ' || *args == '\t') {
            args++;
        }
        if (*args != '-' && *args != '/') {
            break;
        }
        args++;
        switch (*args++) {
            case 'p':
              *plPriorStack = *plPriorStack + 1;
              break;
            case 't':
              *plTopStack = 1;
              break;
            default:
              Usage();
              return NULL;
        }
    }
    return args;
}

EXT_DECL(thread) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    Thread thread;
    ThreadContext tc;

    LONG priorStack = 0;
    LONG topStack = 0;
    ULONG64 address = 0;

    if ((args = ParseArguments(args, &priorStack, &topStack)) == NULL) {
        status = S_FALSE;
        goto Exit;
    }

    status = ExtEvalU64(&args, &address);
    if (status != S_OK) {
        //// This code \/ needs to be replicated for ARM.
        ULONG indexGdtr = 0;
        ULONG indexGdtl = 0;
        ULONG indexFs = 0;
        EXT_CHECK(g_ExtRegisters->GetIndexByName("gdtr", &indexGdtr));
        EXT_CHECK(g_ExtRegisters->GetIndexByName("gdtl", &indexGdtl));
        if (TargetMachine == IMAGE_FILE_MACHINE_AMD64) {
            EXT_CHECK(g_ExtRegisters->GetIndexByName("gs", &indexFs));
        }
        else if (TargetMachine == IMAGE_FILE_MACHINE_I386) {
            EXT_CHECK(g_ExtRegisters->GetIndexByName("fs", &indexFs));
        }

        ExtVerb("gdtr: %04x\n", indexGdtr);
        ExtVerb("gdtl: %04x\n", indexGdtl);
        ExtVerb("fs: %04x\n", indexFs);

        ULONG64 gdtr;
        ULONG64 gdtl;
        ULONG64 fs;

        DEBUG_VALUE v;
        EXT_CHECK(g_ExtRegisters->GetValue(indexGdtr, &v));
        ExtVerb("gdtr: %04x -> %p\n", indexGdtr, v.I64);
        gdtr = v.I64;
        EXT_CHECK(g_ExtRegisters->GetValue(indexGdtl, &v));
        gdtl = v.I64;
        ExtVerb("gdtl: %04x -> %p\n", indexGdtl, v.I64);
        EXT_CHECK(g_ExtRegisters->GetValue(indexFs, &v));
        fs = v.I64;
        ExtVerb("fs: %04x -> %p\n", indexFs, v.I64);

        GDTE fse;
        ZeroMemory(&fse, sizeof(fse));
        EXT_CHECK(TraceRead(gdtr + fs, &fse, sizeof(fse)));
        ULONG64 fs0 = ((ULONG64)fse.base0_15 +
                       ((ULONG64)fse.base16_23 << 16) |
                       ((ULONG64)fse.base24_31 << 24));
        ExtVerb("fs[0] = %p\n", fs0);

        // BUG: does not get fs offset from HAL!!!

        ProcessorContext *ppc;
        EXT_CHECK(TraceRead(fs0, &ppc, sizeof(ppc)));

        ProcessorContext pc;
        EXT_CHECK(ProcessorContextStruct.Read((ULONG64)ppc, &pc));

        ExtVerb("  _processor:           %p\n", pc._processor);
        ExtVerb("  exception:            %p\n", pc.exception);
        ExtVerb("  cpuId:                %p\n", pc.cpuRecord.id);
        ExtOut("%d: Int Stack: %p..%p\n",
               (int)pc.cpuRecord.id,
               pc.cpuRecord.interruptStackLimit, pc.cpuRecord.interruptStackBegin - 1);

        ThreadContext *ptc;
        EXT_CHECK(TraceRead(fs0+sizeof(void*), &ptc, sizeof(ptc)));

        ThreadContext tc;
        EXT_CHECK(ProcessorContextStruct.Read((ULONG64)ptc, &tc));

        ExtVerb("  threadContext:        %p\n", ptc);

        address = tc._thread;
        //// This code /\ needs to be replicated for ARM.
    }

    if (address == 0) {
        ExtErr("Null is invalid thread address.\n");
        return S_FALSE;
    }

    EXT_CHECK(ThreadStruct->Read(address, &thread));

    ULONG64 caddress[3];
    int currentStack = 0;
    caddress[0] = address + ThreadFields[0].offset; // Thread.context

    if (thread.context.next) {
        caddress[1] = thread.context.next;
        currentStack++;
        EXT_CHECK(ThreadContextStruct->Read(caddress[1], &tc));
        if (tc.next) {
            caddress[2] = tc.next;
            EXT_CHECK(ThreadContextStruct->Read(caddress[2], &tc));
            currentStack++;
        }
    }

    if (topStack == 0) {
        currentStack = 0;
    }
    else {
        if (priorStack != 0) {
            currentStack -= priorStack;
            if (currentStack < 0) {
                currentStack = 0;
            }
        }
    }

    EXT_CHECK(ThreadContextStruct->Read(caddress[currentStack], &tc));

    if (TargetMachine == IMAGE_FILE_MACHINE_I386) {
        ExtOut("  %p { tid=%03x pid=%03x eip=%p, ebp=%p, esp=%p %02x }\n",
               address,
               (ULONG)(tc.threadIndex == 0xffff ? 0xfff : tc.threadIndex),
               (ULONG)(tc.processId == 0xffff ? 0xfff : tc.processId),
               tc.threadRecord.spill.ip,
               tc.threadRecord.spill.bp,
               tc.threadRecord.spill.sp,
               (ULONG)tc.gcStates);

        X86_CONTEXT context;
        PVOID mmxRegs = NULL;
        PVOID stRegs = NULL;

        EXT_CHECK(g_ExtSymbols->GetScope(NULL, NULL, &context, sizeof(context)));
        EXT_CHECK(ThreadContextStruct->RawAccess(ThreadContextFields[0].offset, &mmxRegs));
        EXT_CHECK(ThreadContextStruct->RawAccess(ThreadContextFields[1].offset, &stRegs));

        context.Eip = (ULONG)tc.threadRecord.spill.ip;
        context.Esp = (ULONG)tc.threadRecord.spill.sp;
        context.Ebp = (ULONG)tc.threadRecord.spill.bp;
        context.Eax = (ULONG)tc.threadRecord.spill.ax;
        context.Ebx = (ULONG)tc.threadRecord.spill.bx;
        context.Ecx = (ULONG)tc.threadRecord.spill.cx;
        context.Edx = (ULONG)tc.threadRecord.spill.dx;
        context.Esi = (ULONG)tc.threadRecord.spill.si;
        context.Edi = (ULONG)tc.threadRecord.spill.di;
        context.EFlags = (ULONG)tc.threadRecord.spill.fl;

        // CONTEXT_FLOATING_POINT
        context.FloatSave.ControlWord = (ULONG)tc.threadRecord.spill.mmx.fcw;
        context.FloatSave.StatusWord = (ULONG)tc.threadRecord.spill.mmx.fsw;
        context.FloatSave.TagWord = (ULONG)tc.threadRecord.spill.mmx.ftw;
        context.FloatSave.ErrorOffset = (ULONG)tc.threadRecord.spill.mmx.ip;
        context.FloatSave.ErrorSelector = (ULONG)tc.threadRecord.spill.mmx.cs;
        context.FloatSave.DataOffset = (ULONG)tc.threadRecord.spill.mmx.dp;
        context.FloatSave.DataSelector = (ULONG)tc.threadRecord.spill.mmx.ds;

        memcpy((PBYTE)context.FloatSave.RegisterArea+0, (PBYTE)stRegs + 0x00, 10);
        memcpy((PBYTE)context.FloatSave.RegisterArea+10, (PBYTE)stRegs + 0x10, 10);
        memcpy((PBYTE)context.FloatSave.RegisterArea+20, (PBYTE)stRegs + 0x20, 10);
        memcpy((PBYTE)context.FloatSave.RegisterArea+30, (PBYTE)stRegs + 0x30, 10);
        memcpy((PBYTE)context.FloatSave.RegisterArea+40, (PBYTE)stRegs + 0x40, 10);
        memcpy((PBYTE)context.FloatSave.RegisterArea+50, (PBYTE)stRegs + 0x50, 10);
        memcpy((PBYTE)context.FloatSave.RegisterArea+60, (PBYTE)stRegs + 0x60, 10);
        memcpy((PBYTE)context.FloatSave.RegisterArea+70, (PBYTE)stRegs + 0x70, 10);
        memcpy(context.ExtendedRegisters, mmxRegs, 512);

        EXT_CHECK(g_ExtSymbols->SetScope(0, NULL, &context, sizeof(context)));
    }
    else if (TargetMachine == IMAGE_FILE_MACHINE_AMD64) {
        ExtOut("  %p { tid=%03x pid=%03x rip=%p, rbp=%p, rsp=%p %02x }\n",
               address,
               (ULONG)(tc.threadIndex == 0xffff ? 0xfff : tc.threadIndex),
               (ULONG)(tc.processId == 0xffff ? 0xfff : tc.processId),
               tc.threadRecord.spill.ip,
               tc.threadRecord.spill.bp,
               tc.threadRecord.spill.sp,
               (ULONG)tc.gcStates);

        X64_CONTEXT context;
        PVOID mmxRegs = NULL;

        EXT_CHECK(g_ExtSymbols->GetScope(NULL, NULL, &context, sizeof(context)));
        EXT_CHECK(ThreadContextStruct->RawAccess(ThreadContextFields[0].offset, &mmxRegs));

        // TODO: fix the extension to proper handle different architectures. Copy only
        //  these registers for now

        context.Rip = tc.threadRecord.spill.ip;
        context.Rsp = tc.threadRecord.spill.sp;
        context.Rbp = tc.threadRecord.spill.bp;
        context.Rax = tc.threadRecord.spill.ax;
        context.Rbx = tc.threadRecord.spill.bx;
        context.Rcx = tc.threadRecord.spill.cx;
        context.Rdx = tc.threadRecord.spill.dx;
        context.Rsi = tc.threadRecord.spill.si;
        context.Rdi = tc.threadRecord.spill.di;
        context.R8 = tc.threadRecord.spill.r8;
        context.R9 = tc.threadRecord.spill.r9;
        context.R10 = tc.threadRecord.spill.r10;
        context.R11 = tc.threadRecord.spill.r11;
        context.R12 = tc.threadRecord.spill.r12;
        context.R13 = tc.threadRecord.spill.r13;
        context.R14 = tc.threadRecord.spill.r14;
        context.R15 = tc.threadRecord.spill.r15;
        context.EFlags = (ULONG)tc.threadRecord.spill.fl;

        // CONTEXT_FLOATING_POINT
        memcpy(&context.FltSave, mmxRegs, 512);

        EXT_CHECK(g_ExtSymbols->SetScope(0, NULL, &context, sizeof(context)));
    }
    else if (TargetMachine == IMAGE_FILE_MACHINE_ARM) {
        ExtOut("  %p { tid=%03x pid=%03x pc=%p, sp=%p %02x }\n",
               address,
               (ULONG)(tc.threadIndex == 0xffff ? 0xfff : tc.threadIndex),
               (ULONG)(tc.processId == 0xffff ? 0xfff : tc.processId),
               tc.threadRecord.spill.pc,
               tc.threadRecord.spill.sp,
               (ULONG)tc.gcStates);

        ARM_CONTEXT context;

        EXT_CHECK(g_ExtSymbols->GetScope(NULL, NULL, &context, sizeof(context)));

        // TODO: fix the extension to proper handle different architectures. Copy only
        //  these registers for now

        context.R0 = (ULONG)tc.threadRecord.spill.r0;
        context.R1 = (ULONG)tc.threadRecord.spill.r1;
        context.R2 = (ULONG)tc.threadRecord.spill.r2;
        context.R3 = (ULONG)tc.threadRecord.spill.r3;
        context.R4 = (ULONG)tc.threadRecord.spill.r4;
        context.R5 = (ULONG)tc.threadRecord.spill.r5;
        context.R6 = (ULONG)tc.threadRecord.spill.r6;
        context.R7 = (ULONG)tc.threadRecord.spill.r7;
        context.R8 = (ULONG)tc.threadRecord.spill.r8;
        context.R9 = (ULONG)tc.threadRecord.spill.r9;
        context.R10 = (ULONG)tc.threadRecord.spill.r10;
        context.R11 = (ULONG)tc.threadRecord.spill.r11;
        context.R12 = (ULONG)tc.threadRecord.spill.r12;

        context.Pc = (ULONG)tc.threadRecord.spill.pc;
        context.Lr = (ULONG)tc.threadRecord.spill.lr;
        context.Sp = (ULONG)tc.threadRecord.spill.sp;
        context.Cpsr = (ULONG)tc.threadRecord.spill.cpsr;

        EXT_CHECK(g_ExtSymbols->SetScope(0, NULL, &context, sizeof(context)));
    }

    EXT_LEAVE();    // Macro includes: return status;
}
