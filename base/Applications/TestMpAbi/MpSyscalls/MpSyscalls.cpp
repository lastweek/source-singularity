// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

#include "MpSyscalls.h"

// ascii table:
// http://www.lookuptables.com/asciifull.gif


__declspec(dllexport) int __fastcall Struct_Microsoft_Singularity_V1_Services_ProcessService::g_HelloProcessABI(int num)
{
    __asm {
        push ebx;
        mov  ebx, 0xb8000;
        add  ebx, 7688;
        mov  [ebx+0], 0x0048;
        mov  [ebx+1], 0x00e0;
        mov  [ebx+2], 0x0050;
        mov  [ebx+3], 0x00e0;
        mov  [ebx+4], 0x0041;
        mov  [ebx+5], 0x00e0;
        pop  ebx;
    }

    return Struct_Microsoft_Singularity_V1_Services_ProcessService::g_StubHelloProcessABI(num);
}


int entry()
{
    return 0;
}


