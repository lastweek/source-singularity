/////////////////////////////////////////////////////////////////////////////
//
//  threads.cpp - Extension to find Singularity threads.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
#include "singx86.h"

HRESULT DumpThread(ULONG64 thread, bool verbose, bool fullstack, bool detail, bool blocked);

EXT_DECL(stack) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    ULONG64 thread = 0;

    status = ExtEvalU64(&args, &thread);
    if (status != S_OK) {
        goto Exit;
    }

    CHAR prefix[256];
    EXT_CHECK(g_ExtClient->GetOutputLinePrefix(prefix, arrayof(prefix), NULL));
    DumpThread(thread, true, false, true, true);
    EXT_CHECK(g_ExtClient->SetOutputLinePrefix(prefix));

    EXT_LEAVE();    // Macro includes: return status;
}
