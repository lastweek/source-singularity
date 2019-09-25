////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Hal.cpp
//
//  Note:   Kernel Only
//

#include "hal.h"
#include "halkd.h"

#include "strformat.cpp"

int __cdecl _cinit(void);

#if ISA_ARM
void SerialInit(UINT32 * uartBase);
void SerialOutHex(uint32 value);
void SerialOut(const char * str);
#define ArmSerialInit(x) SerialInit(x)
#define ArmSerialOut(x) SerialOut(x)
#define ArmSerialOutHex(x) SerialOutHex(x)
#else // ISA_ARM
#define ArmSerialInit(x)
#define ArmSerialOut(x)
#define ArmSerialOutHex(x)
#endif // ISA_ARM

//////////////////////////////////////////////////////////////////////////////
// Kernel methods
//
extern wchar_t _LinkDate[];

bartok_char *
Class_Microsoft_Singularity_Kernel::g_HalGetLinkDate()
{
    return (bartok_char *)_LinkDate;
}

void fail_assert(const char *expr)
{
    // TODO: wire up something useful here.
    __debugbreak();
}

//////////////////////////////////////////////////////////////////////////////////////////////////
//
Class_System_RuntimeType *CpuRuntimeType = &Class_Microsoft_Singularity_Hal_Cpu::_type;
Class_System_RuntimeType *PlatformRuntimeType = &Class_Microsoft_Singularity_Hal_Platform::_type;

Class_Microsoft_Singularity_Hal_Cpu *Class_Microsoft_Singularity_Hal_Platform::g_GetCurrentCpu()
{
    return (Class_Microsoft_Singularity_Hal_Cpu *)
        Class_Microsoft_Singularity_Processor::g_GetCurrentProcessorContext()->halCpu;
}

void Struct_Microsoft_Singularity_MpBootInfo::g_HalReleaseMpStartupLock()
{
    uint32 lockAddr =
        (uint32)Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->MpStartupLock32;
    if (lockAddr != 0) {
        *((uint16*) lockAddr) = 0;
    }
}

void InitCpu(Class_Microsoft_Singularity_Hal_Cpu *pi)
{
    ArmSerialOut("InitCpu0\n");
    ArmSerialOutHex(pi->Id);
    ArmSerialOut("\n");

    Class_Microsoft_Singularity_Hal_Cpu *hpi = (Class_Microsoft_Singularity_Hal_Cpu*) pi;

    hpi->postHeader.vtableObject = CpuRuntimeType->classVtable;

    ArmSerialOut("InitCpu1\n");

    Class_Microsoft_Singularity_Hal_Cpu::m_Initialize(hpi);

    ArmSerialOut("InitCpu2\n");

    Class_Microsoft_Singularity_Isal_Isa::g_InitializeCpuDispatchTable();

    ArmSerialOut("InitCpu3\n");
}

void ShutdownCpu(Class_Microsoft_Singularity_Hal_Cpu *pi)
{
#if ISA_IX86 || ISA_IX64
    // Disable Interrupts and then spin a screen icon waiting to be reset.
    Class_Microsoft_Singularity_Processor::g_DisableInterrupts();

    int cpu = pi->Id;
    for (int i = 0; i != i + 1; i++) {
        uint16* p = (uint16*)(0xb8000 + (cpu - 1) * 2 * 8);
        for (int r = 0; r < 8; r++) {
            uint16 t = (uint16)(i >> (28 - r * 4));
            t &= 0xf;
            if (t > 9) {
                t += 0x1f00 + 'a' - 10;
            }
            else {
                t += 0x1f00 + '0';
            }
            *p++ = t;
            if (Class_Microsoft_Singularity_DebugStub::g_PollForBreak() == true) {
                __debugbreak();
            }
            for (int i = 0; i < 50000; i++) {
                __nop();
            }
        }
    }
#endif
}

void InitPlatform(Class_Microsoft_Singularity_Hal_Platform *bi,
                  Class_Microsoft_Singularity_Hal_Cpu *pi)
{
    ArmSerialOut("InitPlatform0");

#ifndef ISA_ARM
    Class_Microsoft_Singularity_Isal_Isa::g_InitializeDispatchTable();
#endif

    InitCpu(pi);

    ArmSerialOut("InitPlatform2");

    Class_Microsoft_Singularity_Hal_Platform *nbi = (Class_Microsoft_Singularity_Hal_Platform *) bi;
    nbi->postHeader.vtableObject = PlatformRuntimeType->classVtable;

    // Call early init routines

    Class_Microsoft_Singularity_Hal_Platform::m_Initialize(nbi,
                                                      (Class_Microsoft_Singularity_Hal_Cpu *) pi);

    ArmSerialOut("InitPlatform3");

    kdprintf("DebugPort: %04x\n", nbi->DebugBasePort);

    ArmSerialOut("InitPlatform4");

    // Initialize the debugger hardware

    if (KdpSerialInit(nbi)) {
        nbi->DebuggerType = Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_SERIAL;
    }
    else {
        nbi->DebuggerType = Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_NONE;
    }

    ArmSerialOut("Calling Kernel.Main:\n");
}

void ShutdownPlatform(Class_Microsoft_Singularity_Hal_Platform *bi)
{
}

//////////////////////////////////////////////////////////////////////////////
//
//  These are the first instruction executed in the kernel.
//
extern "C" int __fastcall HalEntryPoint(
    Class_Microsoft_Singularity_Hal_Platform  *bi,
    Class_Microsoft_Singularity_Hal_Cpu *pi)
{
    ArmSerialInit((UINT32 *) 0xffd82300);
    ArmSerialOut("HalEntry 1\n");

    if (bi->Size != sizeof(Class_Microsoft_Singularity_Hal_Platform)) {
        __debugbreak();
        return Class_Microsoft_Singularity_Hal_Platform_ERROR_BAD_SIZE;
    }

    if (pi->Id == 0) {

        // Static C++ constructors.  Ideally, there would be none.
        _cinit();

        ArmSerialOut("HalEntry 2\n");

        // Initialize the target.
        Class_Microsoft_Singularity_Isal_Isa::g_Initialize(bi->CpuRecordPointerOffset,
                                                             bi->ThreadRecordPointerOffset);

        Class_Microsoft_Singularity_Isal_Isa::g_InitializeCpu(
            (Struct_Microsoft_Singularity_Isal_CpuRecord *)pi->CpuRecordPage,
            pi->Id,
            (UIntPtr) pi->KernelStackLimit);

        ArmSerialOut("HalEntry 3\n");

        // Initialize processor context
        ProcessorInitialize(pi);

        ArmSerialOut("HalEntry 4\n");

        // Assert that processor local store is working correctly
        if (Class_Microsoft_Singularity_Hal_Platform::g_GetCurrentCpu() != pi) {
            __debugbreak();
        }

        ArmSerialOut("HalEntry 6\n");

        // Set up native-only constants
        // Initialize platform (in a platform-specific way)
        InitPlatform(bi, pi);
        ArmSerialOut("HalEntry 7\n");

        // Initialize tracing
        Class_Microsoft_Singularity_Tracing::g_Initialize();

        ArmSerialOut("HalEntry 8\n");

        // Initialize debugger
        KdInitialize(bi);

        ArmSerialOut("HalEntry 9\n");

        // Initial breakpoint - uncomment me to do early debugging
        //if (bi->DebuggerType != Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_NONE) {
        //    __debugbreak();
        //}

        Class_Microsoft_Singularity_Kernel::g_Main();

        ShutdownPlatform(bi);
        // Native exits by returning back to the undump/bootloader
        return 0;
    }
    else {
        // Initialize the target cpu.
        Class_Microsoft_Singularity_Isal_Isa::g_InitializeCpu(
            (Struct_Microsoft_Singularity_Isal_CpuRecord *)pi->CpuRecordPage,
            pi->Id,
            (UIntPtr) pi->KernelStackLimit);

        // Initialize processor context
        ProcessorInitialize(pi);

        // Initialize platform processor
        InitCpu(pi);

        // Assert that processor local store is working correctly
        if (Class_Microsoft_Singularity_Hal_Platform::g_GetCurrentCpu() != pi) {
            __debugbreak();
        }

        int result = Class_Microsoft_Singularity_Kernel::g_MpMain(pi->Id);

        ShutdownCpu(pi);

        return Class_Microsoft_Singularity_Hal_Platform_SUCCESS;
    }
}
