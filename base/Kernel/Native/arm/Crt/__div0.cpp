//////////////////////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  This file contains ARM-specific FP code.
//

extern "C" int __rt_div0()
{
    // RaiseException(STATUS_INTEGER_DIVIDE_BY_ZERO, 0, 0, NULL);
    __debugbreak();
    return -1;
}
