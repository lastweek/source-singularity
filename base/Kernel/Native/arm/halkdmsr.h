///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   halkdnmsr
//
//  This module contain definitions used to define the valid
//  coprocessor registers that can be accessed via the read/write msr
//  functionality in the debugger.
//
//  Because the parameters are encoded in instructions rather than
//  carried in registers, an array of valid coprocessor registers would not
//  suffice.
//

//
// This file is included multiple times with different definitions of
// the VALID_COPROC_REGISTER macro.
//

VALID_COPROC_REGISTER(15, 0, 0, 0, 0)
VALID_COPROC_REGISTER(15, 0, 0, 0, 1)
VALID_COPROC_REGISTER(15, 0, 0, 0, 5)
VALID_COPROC_REGISTER(15, 0, 0, 1, 0)
VALID_COPROC_REGISTER(15, 0, 0, 1, 1)
VALID_COPROC_REGISTER(15, 0, 0, 1, 2)
VALID_COPROC_REGISTER(15, 0, 0, 1, 4)
VALID_COPROC_REGISTER(15, 0, 0, 1, 5)
VALID_COPROC_REGISTER(15, 0, 0, 1, 6)
VALID_COPROC_REGISTER(15, 0, 0, 1, 7)
VALID_COPROC_REGISTER(15, 0, 1, 0, 0)
VALID_COPROC_REGISTER(15, 0, 1, 0, 1)
VALID_COPROC_REGISTER(15, 0, 2, 0, 0)
VALID_COPROC_REGISTER(15, 0, 2, 0, 1)
VALID_COPROC_REGISTER(15, 0, 2, 0, 2)
VALID_COPROC_REGISTER(15, 0, 3, 0, 0)
VALID_COPROC_REGISTER(15, 0, 7, 5, 0)
VALID_COPROC_REGISTER(15, 0, 7, 5, 4)
VALID_COPROC_REGISTER(15, 0, 7, 5, 6)
VALID_COPROC_REGISTER(15, 0, 7, 7, 0)
VALID_COPROC_REGISTER(15, 0, 7, 10, 1)
VALID_COPROC_REGISTER(15, 0, 7, 10, 4)
VALID_COPROC_REGISTER(15, 0, 7, 10, 5)
VALID_COPROC_REGISTER(15, 0, 7, 14, 0)
VALID_COPROC_REGISTER(15, 0, 7, 15, 0)
VALID_COPROC_REGISTER(15, 0, 8, 7, 0)
VALID_COPROC_REGISTER(15, 0, 8, 7, 1)
VALID_COPROC_REGISTER(15, 0, 8, 7, 2)
VALID_COPROC_REGISTER(15, 0, 10, 2, 0)
VALID_COPROC_REGISTER(15, 0, 10, 2, 1)
VALID_COPROC_REGISTER(15, 0, 13, 0, 1)
VALID_COPROC_REGISTER(15, 0, 13, 0, 2)
VALID_COPROC_REGISTER(15, 0, 13, 0, 3)
VALID_COPROC_REGISTER(15, 0, 13, 0, 4)
