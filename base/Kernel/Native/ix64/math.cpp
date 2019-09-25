////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Math.cpp
//
//  Note:
//

#define LITTL_ENDIAN

#include "hal.h"
 #pragma warning(disable: 4725)

int32 _ftoi(float64 v)
{
    return 1;
}

float64  _frnd(float64 v)
{
    return v;
}

// The following methods are not yet implemented.

float64 g_Sin(float64 v)
{
    return 0.0;
}

float64 Class_System_Math::g_Sinh(float64 v)
{
    return 0.0;
}

float64 Class_System_Math::g_Cosh(float64 v)
{
    return 0.0;
}

float64 Class_System_Math::g_Tanh(float64 v)
{
    return 0.0;
}

float64 Class_System_Math::g_Mod(float64 x, float64 y)
{
    return 0.0;
}
