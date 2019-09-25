////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ProcessEntry.cpp
//
//  Note:   Process Only
//

#include "hal.h"

int __cdecl _cinit(void);

//////////////////////////////////////////////////////////////////////////////
// debugging code.  Put it here for now.

void fail_assert(Class_System_String *message)
{
    Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print((bartok_char*)&message->m_firstChar,
                                                                   message->m_stringLength);
    //Struct_Microsoft_Singularity_V1_Services_DebugService::g_Break();
    Class_Microsoft_Singularity_DebugStub::g_Break();
}

//////////////////////////////////////////////////////////////////////////////
//

BOOL KdDebuggerNotPresent;
extern Class_System_RuntimeType * brtmainClass;
extern int (*brtmain)(ClassVector_Class_System_String *args);
extern int brtmainReturnsInt;

#if ISA_IX86

// Note: CallMain's return value is only meaningful if brtmainReturnsInt is true.
// Example:
//   int ret = CallMain(args);
//   if (!MainReturnsInt()) ret = 0;
__declspec(naked) int Class_Microsoft_Singularity_AppRuntime::
g_CallMain(ClassVector_Class_System_String *args)
{
    // To avoid creating an unmanaged stack frame, jmp directly to the main function:
    __asm {
        mov eax, brtmain;
        jmp eax;
    }
}

#endif

bool Class_Microsoft_Singularity_AppRuntime::g_MainReturnsInt()
{
    return (brtmainReturnsInt != 0);
}

void Class_Microsoft_Singularity_AppRuntime::g_SetDebuggerPresence(bool debuggerPresent)
{
    KdDebuggerNotPresent = !debuggerPresent;
}

//////////////////////////////////////////////////////////////////////////////
//
//  These are the first instruction executed in a process.
//
extern "C" int32 __fastcall RuntimeEntryPoint(int threadIndex)
{
    int32 ret = 0;

    if (threadIndex == -1) {
        // WARNING: When initializing an SIP, before making any other calls
        // into the HAL we need to make sure the HAL is initialized using
        // the following API.

        Class_Microsoft_Singularity_Isal_Isa::c_currentThreadOffset
            = Struct_Microsoft_Singularity_V1_Services_PlatformService::g_GetThreadContextOffset();
        Class_Microsoft_Singularity_Isal_Isa::c_currentCpuOffset
            = Struct_Microsoft_Singularity_V1_Services_PlatformService::g_GetProcessorContextOffset();
    }

    Struct_Microsoft_Singularity_ThreadContext * context =
        Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext();

    if (!Struct_Microsoft_Singularity_ThreadContext::m_IsInKernelMode(
        context)) {
        // fail assertion in uninitialized process mode:
        __debugbreak();
    }

    Struct_Microsoft_Singularity_ThreadContext::m_SetProcessMode(context);

    if (threadIndex == -1) {
        _cinit();

        Class_Microsoft_Singularity_Tracing::g_Initialize();
//        Class_Microsoft_Singularity_Tracing::g_Log(0, "RuntimeEntryPoint:Main");
#ifndef NO_MONITORING
        Class_Microsoft_Singularity_Monitoring::g_Initialize();
#endif

        ret = Class_Microsoft_Singularity_AppRuntime::g_AppStart(brtmainClass);
    }
    else {
//        Class_Microsoft_Singularity_Tracing::g_Log(0, "RuntimeEntryPoint:Thread");
        Class_System_Threading_Thread::g_ThreadStub(threadIndex);
    }

    Struct_Microsoft_Singularity_ThreadContext::m_SetKernelMode(context);

    return ret;
}
