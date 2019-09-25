//////////////////////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  This file contains ARM-specific FP code.
//

typedef union _FP64Form
{
    struct
    {
        unsigned int MantLo : 28;
        unsigned int MantHi0 : 4;
        unsigned int MantHi1 : 20;
        unsigned int Exponent : 11;
        unsigned int SignBit  : 1;
    };
    struct
    {
        unsigned int ul0;
        unsigned int ul1;
    };
    double fp;
    unsigned __int64 ull;
} FP64Form, *PFP64Form;

extern "C"
double
__negd(
       double d1
      )
//++
//
//Routine Description:
//
//  negate the given double precision floating point value
//
//Arguments:
//
//  d1      - double precision values to be negated
//
//Return Value:
//
//  The negation of d1.
//
//--  
{
    FP64Form FpConv;

    FpConv.fp = d1;
    FpConv.SignBit ^= 1;

    return( FpConv.fp );
}
