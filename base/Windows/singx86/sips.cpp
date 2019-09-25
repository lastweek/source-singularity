/////////////////////////////////////////////////////////////////////////////
//
//  sips.cpp - Extension to find Singularity SIPs.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
#include "singx86.h"

EXT_DECL(sips) // Defines: PDEBUG_CLIENT Client, PCSTR args
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
