/////////////////////////////////////////////////////////////////////////////
//
//  procs.cpp - Extension to find Singularity Processes.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
#include "singx86.h"

HRESULT DumpProcess(ULONG64 address, bool stack, bool detail)
{
    if (address == 0) {
        return S_FALSE;
    }

    HRESULT status = S_FALSE;
#if 0 // TODO: This needs to be implemented!
    HRESULT status = S_OK;
    Thread thread;

    EXT_CHECK(ThreadStruct->Read(address, &thread));

    if (stack) {
        ExtOut("  thread=%p { tid=%03x pid=%03x ebp=%p, esp=%p, eip=%p }\n",
               address,
               (ULONG)(thread.context.threadIndex == 0xffff ? 0xfff : thread.context.threadIndex),
               (ULONG)(thread.context.processId == 0xffff ? 0xfff : thread.context.processId),
               thread.context.threadRecord.spill.ip,
               thread.context.threadRecord.spill.bp,
               thread.context.threadRecord.spill.sp);

        DEBUG_STACK_FRAME frames[10];
        ULONG filled = 0;

        status = g_ExtControl->GetStackTrace(thread.context.threadRecord.spill.bp,
                                             thread.context.threadRecord.spill.sp,
                                             thread.context.threadRecord.spill.ip,
                                             frames,
                                             arrayof(frames),
                                             &filled);

        if (status == S_OK) {
            g_ExtClient->SetOutputLinePrefix("      ");
            g_ExtControl->OutputStackTrace(DEBUG_OUTPUT_NORMAL,
                                           frames,
                                           filled,
                                           detail ? (DEBUG_STACK_FRAME_ADDRESSES |
                                                     DEBUG_STACK_COLUMN_NAMES |
                                                     DEBUG_STACK_SOURCE_LINE) : 0);
        }
    }
    else {
        CHAR name[512];
        ULONG64 displacement = 0;

        status = g_ExtSymbols->GetNameByOffset((ULONG64)thread.context.threadRecord.spill.ip,
                                               name,
                                               arrayof(name),
                                               NULL,
                                               &displacement);
        if (status == S_OK) {
            ExtOut("  thread=%p { tid=%03x pid=%03x ebp=%p, esp=%p, eip=%p } %s+%I64d\n",
                   address,
                   (ULONG)(thread.context.threadIndex == 0xffff ? 0xfff : thread.context.threadIndex),
                   (ULONG)(thread.context.processId == 0xffff ? 0xfff : thread.context.processId),
                   thread.context.threadRecord.spill.ip,
                   thread.context.threadRecord.spill.bp,
                   thread.context.threadRecord.spill.sp,
                   name,
                   (LONG64)displacement);
        }
        else {
            ExtOut("  thread=%p { tid=%03x pid=%03x ebp=%p, esp=%p, eip=%p }\n",
                   address,
                   (ULONG)(thread.context.threadIndex == 0xffff ? 0xfff : thread.context.threadIndex),
                   (ULONG)(thread.context.processId == 0xffff ? 0xfff : thread.context.processId),
                   thread.context.threadRecord.spill.ip,
                   thread.context.threadRecord.spill.bp,
                   thread.context.threadRecord.spill.sp);
        }
    }
  Exit:
#endif
    return status;
}


EXT_DECL(procs) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;
    bool stack = false;
    bool detail = false;

    while (*args != '\0') {
        if (*args == '-' || *args == '/') {
            args++;
            switch (*args++) {
              case 'd': // detail
              case 'D':
                detail = !detail;
                break;
              case 's': // stack
              case 'S':
                stack = !stack;
                break;
            }
            while (*args != ' ') {
                args++;
            }
        }
        else {
            break;
        }
    }

    ULONG pointerSize = (g_ExtControl->IsPointer64Bit() == S_OK) ? 8 : 4;
    ULONG64 address = 0;
    ULONG64 procs = 0;
    ULONG type = 0;
    ULONG subtype = 0;
    ULONG64 module = 0;

    EXT_CHECK(g_ExtSymbols->GetOffsetByName(kernel_processTable, &address));
    EXT_CHECK(g_ExtSymbols->GetOffsetTypeId(address, &type, &module));
    EXT_CHECK(TraceReadPointer(1, address, &procs));
    ExtVerb("processTable: %p\n", procs);

    CHAR name[512];

    EXT_CHECK(g_ExtSymbols->GetTypeName(module, type, name, arrayof(name), NULL));
    ExtVerb("  processTable type: %s\n", name);
    int len = (int)strlen(name);
    if (len > 3 &&
        name[len-3] == '[' &&
        name[len-2] == ']' &&
        name[len-1] == '*') {
        name[len-3] = '\0';

        EXT_CHECK(g_ExtSymbols->GetTypeId(module, name, &subtype));
        EXT_CHECK(g_ExtSymbols->GetTypeName(module, subtype, name, arrayof(name), NULL));
        ExtVerb("  processTable[] type: %s\n", name);
    }

    ULONG lengthOffset = 0;
    EXT_CHECK(g_ExtSymbols->GetFieldOffset(module, type, "overall_length", &lengthOffset));

    ULONG valuesOffset = 0;
    EXT_CHECK(g_ExtSymbols->GetFieldOffset(module, type, "values", &valuesOffset));

    ULONG length = 0;
    EXT_CHECK(TraceRead(procs + lengthOffset, &length, sizeof(length)));
    ExtOut("processTable: %p [maximum %d entries]\n", procs, length);

    for (ULONG id = 0; id < length; id++) {
        ULONG64 process = 0;

        EXT_CHECK(TraceReadPointer(1, procs + valuesOffset + id * pointerSize, &process));
        if (process != 0) {
            if (detail) {
                ExtOut("      %p\n", process);
            }
            else {
                ExtOut("      %p\n", process);
            }
        }
    }

    EXT_LEAVE();    // Macro includes: return status;
}
