//////////////////////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  This file contains ARM-specific FP code.
//

//
//  FP_CODE
//
//  Enumerated type containing all base FP operations that can raise exceptions.
//  This must agree with the defines in fpe.asm.
//
typedef enum
{
    _FpAddD,         // Add Double
    _FpAddS,         // Add Single
    _FpSubD,         // Subtract Double
    _FpSubS,         // Subtract Single
    _FpCmpD,         // Compare Double
    _FpCmpS,         // Compare Single
    _FpDivD,         // Divide Double
    _FpDivS,         // Divide Single
    _FpDToI,         // Convert Double To int
    _FpDToI64,       // Convert Double To __int64
    _FpDToS,         // Convert Double To Single
    _FpDToU,         // Convert Double To unsigned int
    _FpDToU64,       // Convert Double To unsigned __int64
    _FpIToS,         // Convert int To Single
    _FpMulD,         // Multiply Double
    _FpMulS,         // Multiply Single
    _FpSToD,         // Convert Single To Double
    _FpSToI,         // Convert Single To int
    _FpSToI64,       // Convert Single To __int64
    _FpSToU,         // Convert Single To unsigned int
    _FpSToU64,       // Convert Single To unsigned __int64
    _FpUToS,         // Convert unsigned int To Single
    _FpI64ToD,       // Convert __int64 To Double
    _FpI64ToS,       // Convert __int64 To Single
    _FpU64ToD,       // Convert unsigned __int64 To Double
    _FpU64ToS,       // Convert unsigned __int64 To Single
    _FpRndD          // Round to double integer
} FP_CODE;



//
// FP_VALUE
//
// A floating-point emulation routine supplies an FP_VALUE for each operand and
// the result.  The proper alias in the union is determined by the corresponding
// FP_OP.  This structure must be exactly 8 bytes big (corresponding to
// sizeof(double)).  Note that extended formats such as long double are not
// supported.

typedef union {
    float               Fp32Value;      // IEEE 32-bit floating-point value
    double              Fp64Value;      // IEEE 64-bit floating-point value
    int                 I32Value;       // Signed 32-bit integer value
    __int64             I64Value;       // Signed 64-bit integer value
    unsigned int        U32Value;       // Unsigned 32-bit integer value
    unsigned __int64    U64Value;       // Unsigned 64-bit integer value
    int                 CompareValue;   // One of _FPIEEE_COMPARE_RESULT enums
} FP_VALUE;



//
// FPExInfo
//
// This must match the defines for exception information in fpe.s.
//

typedef union
{
    unsigned int Raw;
    struct
    {
        unsigned int CauseInvalid    : 1;     // Bit 0
        unsigned int CauseZeroDivide : 1;     // Bit 1
        unsigned int CauseOverflow   : 1;     // Bit 2
        unsigned int CauseUnderflow  : 1;     // Bit 3
        unsigned int CauseInexact    : 1;     // Bit 4
        unsigned int Reserved2       : 15;    // Bits 19:5
        unsigned int Operation       : 5;     // Bits 24:20
        unsigned int Reserved1       : 7;     // Bits 31:25
    } Field;
} FPExInfo;



//++
//
//Routine Description:
//
//  This function accepts basic IEEE floating-point exception information from
//  a software emulation routine that detected the exception.  All of the
//  exception information is packaged into a standard _FPIEEE_RECORD structure
//  and passed to RaiseException.  On return from RaiseException, the structure
//  is unpacked, causing anything that the user changed to be reflected in the
//  floating-point status.  The calling parameters have been selected and
//  arranged for the convenience of the assembly language coded emulation
//  routines.
//
//  A user typically calls _fpieee_flt, the standard SEH exception filter for
//  IEEE floating-point exceptions, to gain access to the _FPIEEE_RECORD
//  structure.  On a system with hardware floating-point instructions, the
//  _fpieee_flt exception filter decodes the results of the floating-point trap
//  (often decoding instruction opcodes and other state left by the kernel) and
//  builds the _FPIEEE_RECORD structure itself.  But since the SH-3 uses
//  software floating-point emulation, we use the same reporting mechanism that
//  the math library uses.  In this case, _fpieee_flt detects that an
//  _FPIEEE_RECORD has already been created for the exception and simply passes
//  it through.
//
//Arguments:
//
//  ExInfo - Supplies the exception information regarding operation and cause.
//
//  Operand1 - Supplies the original first operand.
//
//  Operand2 - Supplies the original second operand.
//
//  Result - Supplies the default result if the user simply continues.
//
//Return Value:
//
//  The result, possibly modified by the user's exception handler, after return
//  from RaiseException.  The software emulation routine substitutes this value
//  for the result it returns.
//
//--

extern "C"
FP_VALUE
FPE_Raise (
    FPExInfo  ExInfo,
    FP_VALUE  Operand1,
    FP_VALUE  Operand2,
    FP_VALUE  Result
    )
{
    __debugbreak();
    return Result;
}
