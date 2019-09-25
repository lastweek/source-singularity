/////////////////////////////////////////////////////////////////////////////
//
//  log.cpp - Extension to find parse Singularity trace log.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
#include "singx86.h"

HRESULT FindBound(const char *symbol, ULONG64 *ptrval)
{
    HRESULT status = S_OK;
    ULONG64 address;

    EXT_CHECK(g_ExtSymbols->GetOffsetByName(symbol, &address));
    EXT_CHECK(g_ExtData->ReadPointersVirtual(1, address, ptrval));

  Exit:
    ExtVerb("Find(%s) = %p\n", symbol, *ptrval);
    return status;
}

HRESULT SetBound(const char *symbol, ULONG64 ptrval)
{
    HRESULT status = S_OK;
    ULONG64 address;

    EXT_CHECK(g_ExtSymbols->GetOffsetByName(symbol, &address));
    EXT_CHECK(g_ExtData->WritePointersVirtual(1, address, &ptrval));
  Exit:
    return status;
}

ULONG64 GetValue(PCSTR& args, bool fHex)
{
    ULONG base = fHex ? 16 : 10;
    if (*args == '0') {
        fHex = true;
        base = 16;
    }
    ULONG64 value = 0;

    while (*args && *args != ' ' && *args != '\t') {
        if (*args >= '0' && *args <= '9') {
            value = value * base + (*args++ - '0');
        }
        else if (*args >= 'A' && *args <= 'F' && fHex) {
            value = value * base + (*args++ - 'A') + 10;
        }
        else if (*args >= 'a' && *args <= 'f' && fHex) {
            value = value * base + (*args++ - 'a') + 10;
        }
        else {
            break;
        }
    }
    return value;
}

EXT_DECL(log) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    //
    //  Try the new diag too. The code above will become obsolete when the old tracing is completly
    //  removed
    //

    const char * defaultCommand = "!diagnose -s LegacyTracing -t System.LEGACY_LOG_ENTRY -l IP "
            "-y Msg -r Size|LinkOffset|Flags|Type|arg0|arg1|arg2|arg3|arg4|arg5|StrArg0|StrArg1 %s";


    CHAR command[512];
    _snprintf(command, sizeof(command), defaultCommand, args);

    status = g_ExtControl->Execute(DEBUG_OUTCTL_ALL_CLIENTS |
                                   DEBUG_OUTCTL_OVERRIDE_MASK |
                                   DEBUG_OUTCTL_NOT_LOGGED,
                                   command,
                                   DEBUG_EXECUTE_DEFAULT );

    EXT_LEAVE();    // Macro includes: return status;
}

