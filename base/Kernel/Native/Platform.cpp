////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Platform.cpp
//
//  Note:   Kernel Only
//

#include "hal.h"

void Class_Microsoft_Singularity_Hal_Platform::g_NativeKill(int32 action)
{
    Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->KillAction = action;

    void (__cdecl *pfKill)(void) = (void (__cdecl *)(void))Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->Kill32;

    pfKill();
    __debugbreak();
}
