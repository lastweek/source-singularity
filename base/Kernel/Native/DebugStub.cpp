//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DebugStub.cpp: runtime support for debugging
//
//  Note:   Process Only
//

#include "hal.h"

void Class_Microsoft_Singularity_DebugStub::g_Break()
{
    __debugbreak();
}
