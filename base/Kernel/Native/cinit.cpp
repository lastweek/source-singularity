////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   cinit.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"

//////////////////////////////////////////////////////////////////////////////

// Need to put the following marker variables into the .CRT section.
// The .CRT section contains arrays of function pointers.
// The compiler creates functions and adds pointers to this section
// for things like C++ global constructors.
//
// The XIA, XCA etc are group names with in the section.
// The compiler sorts the contributions by the group name.
// For example, .CRT$XCA followed by .CRT$XCB, ... .CRT$XCZ.
// The marker variables below let us get pointers
// to the beginning/end of the arrays of function pointers.
//
// For example, standard groups are
//  XCA used here, for begin marker
//  XCC "compiler" inits
//  XCL "library" inits
//  XCU "user" inits
//  XCZ used here, for end marker
//

typedef void (__cdecl *_PVFV)(void);
// typedef int  (__cdecl *_PIFV)(void);
typedef _PVFV _PIFV;

#pragma comment(linker, "/merge:.CRT=.DATA")

#pragma data_seg(".CRT$XIA", "DATA")
extern "C" _PIFV __xi_a[] = { NULL };                    // C initializers.

#pragma data_seg(".CRT$XIZ", "DATA")
extern "C" _PIFV __xi_z[] = { NULL };

#pragma data_seg(".CRT$XCA", "DATA")
extern "C" _PVFV __xc_a[] = { NULL };                    // C++ initializers.

#pragma data_seg(".CRT$XCZ", "DATA")
extern "C" _PVFV __xc_z[] = { NULL };

#pragma data_seg(".CRT$XPA", "DATA")
extern "C" _PVFV __xp_a[] = { NULL };                    // C pre-terminators.

#pragma data_seg(".CRT$XPZ", "DATA")
extern "C" _PVFV __xp_z[] = { NULL };

#pragma data_seg(".CRT$XTA", "DATA")
extern "C" _PVFV __xt_a[] = { NULL };                    // C terminators.

#pragma data_seg(".CRT$XTZ", "DATA")
extern "C" _PVFV __xt_z[] = { NULL };

#pragma data_seg()

// Walk an array of function pointers, call non-NULL ones.
static void __cdecl _initterm(_PVFV *pfbegin, _PVFV *pfend)
{
    for (; pfbegin < pfend; pfbegin++) {
        if (*pfbegin != NULL) {
            (**pfbegin)();
        }
    }
}

// Call all of the C++ static constructors.
//
int __cdecl _cinit(void)
{
    // do C initializations
    _initterm( __xi_a, __xi_z );

    // do C++ initializations
    _initterm( __xc_a, __xc_z );
    return 0;
}

int  __cdecl _cfini(void)
{
    // do C initializations
    _initterm( __xp_a, __xp_z );

    // do C++ terminations
    _initterm( __xt_a, __xt_z );
    return 0;
}
