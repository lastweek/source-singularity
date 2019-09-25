;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; Assembler source for FPA support code and emulator
; ==================================================
; Definitions for FPA instructions and registers. Also used by "fplib".
;
; Copyright (C) Advanced RISC Machines Limited, 1992-7. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

;===========================================================================

; FPSR fields
; -----------

IOC_pos         EQU     0
IOC_bit         EQU     1:SHL:IOC_pos
DZC_pos         EQU     1
DZC_bit         EQU     1:SHL:DZC_pos
OFC_pos         EQU     2
OFC_bit         EQU     1:SHL:OFC_pos
UFC_pos         EQU     3
UFC_bit         EQU     1:SHL:UFC_pos
IXC_pos         EQU     4
IXC_bit         EQU     1:SHL:IXC_pos
ND_pos          EQU     8
ND_bit          EQU     1:SHL:ND_pos
NE_pos          EQU     9
NE_bit          EQU     1:SHL:NE_pos
SO_pos          EQU     10
SO_bit          EQU     1:SHL:SO_pos
EP_pos          EQU     11
EP_bit          EQU     1:SHL:EP_pos
AC_pos          EQU     12
AC_bit          EQU     1:SHL:AC_pos
IOE_pos         EQU     16
IOE_bit         EQU     1:SHL:IOE_pos
DZE_pos         EQU     17
DZE_bit         EQU     1:SHL:DZE_pos
OFE_pos         EQU     18
OFE_bit         EQU     1:SHL:OFE_pos
UFE_pos         EQU     19
UFE_bit         EQU     1:SHL:UFE_pos
IXE_pos         EQU     20
IXE_bit         EQU     1:SHL:IXE_pos
SysID_pos       EQU     24
SysID_mask      EQU     &FF:SHL:SysID_pos

SysID_oldFPE    EQU     0x00
SysID_FPE       EQU     0x01
SysID_FPPC      EQU     0x80
; SysID_FPA       EQU     0x81    ;Already defined in "optcheck" file

;===========================================================================

; FPCR fields - many also valid for CPDO and CPRT instructions
; ------------------------------------------------------------

S2_pos          EQU     0
S2_mask         EQU     &F:SHL:S2_pos
S2_Ibit         EQU     &8:SHL:S2_pos
Op3_pos         EQU     4
Op3_mask        EQU     &1:SHL:Op3_pos
RM_pos          EQU     5
RM_mask         EQU     &3:SHL:RM_pos
Pr2_pos         EQU     7
Pr2_mask        EQU     &1:SHL:Pr2_pos
DA_pos          EQU     8
DA_bit          EQU     1:SHL:DA_pos
RE_pos          EQU     9
RE_bit          EQU     1:SHL:RE_pos
AB_pos          EQU     10
AB_bit          EQU     1:SHL:AB_pos
SB_pos          EQU     11
SB_bit          EQU     1:SHL:SB_pos
Ds_pos          EQU     12
Ds_mask         EQU     &7:SHL:Ds_pos
Op2_pos         EQU     15
Op2_mask        EQU     &1:SHL:Op2_pos
S1_pos          EQU     16
S1_mask         EQU     &7:SHL:S1_pos
Pr1_pos         EQU     19
Pr1_mask        EQU     &1:SHL:Pr1_pos
Op1_pos         EQU     20
Op1_mask        EQU     &F:SHL:Op1_pos
EO_pos          EQU     26
EO_bit          EQU     1:SHL:EO_pos
MO_pos          EQU     27
MO_bit          EQU     1:SHL:MO_pos
IE_pos          EQU     28
IE_bit          EQU     1:SHL:IE_pos
RU_pos          EQU     31
RU_bit          EQU     1:SHL:RU_pos

Pr_mask         EQU     Pr1_mask+Pr2_mask
Op_mask         EQU     Op1_mask+Op2_mask+Op3_mask

; Rounding mode values

RM_Nearest      EQU     0:SHL:RM_pos
RM_PlusInf      EQU     1:SHL:RM_pos
RM_MinusInf     EQU     2:SHL:RM_pos
RM_Zero         EQU     3:SHL:RM_pos

;===========================================================================

; Instruction fields - all coprocessor instructions
; -------------------------------------------------
;
; The following bit distinguishes CPRTs from CPDOs.

RTnotDO_pos     EQU     4
RTnotDO_bit     EQU     1:SHL:RTnotDO_pos

; The two recognised coprocessor numbers and the position and mask of the
; field in the instruction.

Coproc_pos      EQU     8
Coproc_mask     EQU     &F:SHL:Coproc_pos
Coproc_1        EQU     1:SHL:Coproc_pos
Coproc_2        EQU     2:SHL:Coproc_pos

; The following bit distinguishes CPDTs from CPRT/CPDOs.

RTDOnotDT_pos   EQU     25
RTDOnotDT_bit   EQU     1:SHL:RTDOnotDT_pos

; For instructions that take the undefined instruction exception vector, the
; following bit distinguishes coprocessor instructions from genuinely
; undefined instructions.

NotUndef_pos    EQU     27
NotUndef_bit    EQU     1:SHL:NotUndef_pos

Cond_pos        EQU     28
Cond_mask       EQU     &F:SHL:Cond_pos
Cond_EQ         EQU     &0:SHL:Cond_pos
Cond_NE         EQU     &1:SHL:Cond_pos
Cond_CS         EQU     &2:SHL:Cond_pos
Cond_CC         EQU     &3:SHL:Cond_pos
Cond_MI         EQU     &4:SHL:Cond_pos
Cond_PL         EQU     &5:SHL:Cond_pos
Cond_VS         EQU     &6:SHL:Cond_pos
Cond_VC         EQU     &7:SHL:Cond_pos
Cond_HI         EQU     &8:SHL:Cond_pos
Cond_LS         EQU     &9:SHL:Cond_pos
Cond_GE         EQU     &A:SHL:Cond_pos
Cond_LT         EQU     &B:SHL:Cond_pos
Cond_GT         EQU     &C:SHL:Cond_pos
Cond_LE         EQU     &D:SHL:Cond_pos
Cond_AL         EQU     &E:SHL:Cond_pos
Cond_NV         EQU     &F:SHL:Cond_pos

; CPDT-specific instruction fields
; --------------------------------

DT_offset_pos   EQU     0
DT_offset_mask  EQU     &FF:SHL:DT_offset_pos
DT_src_pos      EQU     12
DT_src_mask     EQU     &7:SHL:DT_src_pos
DT_dst_pos      EQU     12
DT_dst_mask     EQU     &7:SHL:DT_dst_pos
DT_pr2_pos      EQU     15
DT_pr2_mask     EQU     &1:SHL:DT_pr2_pos
DT_ARMreg_pos   EQU     16
DT_ARMreg_mask  EQU     &F:SHL:DT_ARMreg_pos
DT_LnotS_pos    EQU     20
DT_LnotS_bit    EQU     1:SHL:DT_LnotS_pos
DT_wb_pos       EQU     21
DT_wb_bit       EQU     1:SHL:DT_wb_pos
DT_pr1_pos      EQU     22
DT_pr1_mask     EQU     &1:SHL:DT_pr1_pos
DT_UnotD_pos    EQU     23
DT_UnotD_bit    EQU     1:SHL:DT_UnotD_pos
DT_PreIndex_pos EQU     24
DT_PreIndex_bit EQU     1:SHL:DT_PreIndex_pos

; CPRT-specific instruction fields
; --------------------------------
;
; The following FPCR fields also apply to CPRTs: S2_pos, S2_mask, S2_Ibit,
; Op3_pos, Op3_mask, RM_pos, RM_mask, Pr2_pos, Pr2_mask, S1_pos, S1_mask,
; Pr1_pos, Pr1_mask, Op1_pos, Op1_mask. (Note Op2_pos and Op2_mask are not
; included in this list.)

RT_ARMreg_pos   EQU     12
RT_ARMreg_mask  EQU     &F:SHL:RT_ARMreg_pos
RT_SnotL_pos    EQU     20
RT_SnotL_bit    EQU     1:SHL:RT_SnotL_pos

; The following is the full opcode mask for a CPRT, in which the Pr2_mask
; field is part of an ARM register number rather than of the opcode. It
; includes the Pr3_mask field, whose only purpose is to tell us that this
; *is* a CPRT rather than a CPDO

OpRT_mask       EQU     Op1_mask+Op3_mask

; The following bit distinguishes CMF(E)s from CNF(E)s.

CompNeg_pos     EQU     21
CompNeg_bit     EQU     1:SHL:CompNeg_pos

; The following bit distinguishes exception-causing comparisons from
; non-exception causing comparisons.

CompExc_pos     EQU     22
CompExc_bit     EQU     1:SHL:CompExc_pos

; CPDO-specific instruction fields
; --------------------------------
;
; The following FPCR fields also apply to CPDOs: S2_pos, S2_mask, S2_Ibit,
; Op3_pos, Op3_mask, RM_pos, RM_mask, Pr2_pos, Pr2_mask, Ds_pos, Ds_mask,
; Op2_pos, Op2_mask, S1_pos, S1_mask, Pr1_pos, Pr1_mask, Op1_pos, Op1_mask.

; The bit to indicate that the operation is monadic and not dyadic.

DO_monad_pos    EQU     15
DO_monad_bit    EQU     1:SHL:DO_monad_pos

; The bit to indicate that this is a subtraction (SUF or RSF) rather than an
; addition (ADF).

SubNotAdd_pos   EQU     21
SubNotAdd_bit   EQU     1:SHL:SubNotAdd_pos

; The bit to indicate that this is a reverse subtraction (RSF) rather than
; an addition or ordinary subtraction (ADF or SUF).

RSF_pos         EQU     20
RSF_bit         EQU     1:SHL:RSF_pos

; The bit to indicate that this is a reverse division (RDF or FRD) rather
; than a normal division (DVF or FDV).

RevDiv_pos      EQU     20
RevDiv_bit      EQU     1:SHL:RevDiv_pos

; The bit to indicate that this is a "fast" multiplication or division (FML,
; FDV or FRD), rather than the normal version (MUF, DVF or RDF).

Fast_pos        EQU     23
Fast_bit        EQU     1:SHL:Fast_pos

; The bit to indicate that a move-type instruction (MVF, MNF or ABS) is an
; MNF.

MNF_pos         EQU     20
MNF_bit         EQU     1:SHL:MNF_pos

; The bit to indicate that a move-type instruction (MVF, MNF or ABS) is an
; ABS.

ABS_pos         EQU     21
ABS_bit         EQU     1:SHL:ABS_pos

; The bit to indicate that this is a COS instruction rather than a SIN.

COSnotSIN_pos   EQU     20
COSnotSIN_bit   EQU     1:SHL:COSnotSIN_pos

; The bit to indicate that this is a ACS instruction rather than an ASN.

ACSnotASN_pos   EQU     22
ACSnotASN_bit   EQU     1:SHL:ACSnotASN_pos

; The bit to indicate that this is a LOG instruction rather than an LGN.

LOGnotLGN_pos   EQU     20
LOGnotLGN_bit   EQU     1:SHL:LOGnotLGN_pos

; The bit to indicate that this is a RPW instruction rather than a POW.

RPWnotPOW_pos   EQU     20
RPWnotPOW_bit   EQU     1:SHL:RPWnotPOW_pos

;===========================================================================

;
; Floating point formats.
;
; There are four floating point formats: Single, Double, Extended and
; Internal.  Single, Double and Extended are memory formats and
; Internal is the floating point register format.  (The FPE keeps the
; floating pointer registers in Internal format even through they are
; actually in memory somewhere.)  The FPE uses precisely the same
; Internal format as the FPA chip in order to allow the FPASC and FPE
; to share code.  STF converts from Internal format to Single, Double
; or Extended format.  LDF converts from Single, Double or Extended
; format to Internal format.
;
; All floating point values in memory must be aligned on 4 byte
;  boundaries.
;
; The Single and Double formats are specified by the ANSI/IEEE
; standard 754-1985.  They look like this:
;
; The Single format is 32 bits wide:
;
;  | Sign | Exponent | Fraction |
;
; The sign field is 1 bit wide the exponent field is 8 bits wide and
; the fraction field is 23 bits wide.  The exponent field is biased by
; 127 (i.e. an exponent of 1 is encoded as 0x80).  The fraction has an
; implicit leading 1 unless the number is denormalised (see table
; below).
;
; The following table summarises the Single format:
; Where: 's' is -1 if the sign bit is set and 1 if the sign bit is clear.
;        'e' is the value of the exponent field interpreted as unsigned.
;        'f' is the fraction field interpreted as binary digits
;
;  Exponent   Fraction   What it is       Value
;      0         0       signed zero      +0 or -0
;      0       non-zero  denorm. number   s * (0.f) * (2**(-126))
;    255         0       infinity         s * infinity
;    255       non-zero  NaN
;       otherwise        normal number    s * (1.f) * (2**(e-127))
;
; The Double format is 64 bits wide:
;
;     address:  | Sign | Exponent | Fraction high |
; address + 4:  |          Fraction low           |
;
; The sign field is 1 bit wide the exponent field is 11 bits wide and
; the fraction field is 52 bits wide (20 bits in Fraction high and 32
; in Fraction low).  The exponent is biased by 1023.  The fraction has
; an implicit leading 1 unless the number is denormalised (see table
; below).
;
; The following table summarises the Double format:
;
;  Exponent   Fraction   What it is       Value
;      0          0      signed zero      +0 or -0
;      0      non-zero   denorm. number   s * (0.f) * (2**(-1022))
;   2047          0      infinity         s * infinity
;   2047      non-zero   NaN
;       otherwise        normal number    s * (1.f) * (2**(e-1023))
;
; Extended format implements the IEEE Double Extended format. People
; wanting an IEEE Single Extended format should either use Double or
; Extended. Since the reasons the standard suggests for wanting to
; have Single Extended as well as Double Extended are upwards
; compatibility and speed, and the former doesn't really apply in our
; world, and some Double precision operations are faster than Extended
; ones (e.g. multiplication), I would actually recommend someone who
; wanted an IEEE Single Extended format to use Double, not Extended.
;
; The Extended format is 96 bits wide:
;
;     address:  | Sign | Reserved  | Exponent |
; address + 4:  | Units |    Fraction high    |
; address + 8:  |        Fraction low         |
;
; The sign field is 1 bit wide, the reserved field is 16 bits wide,
; the exponent field is 15 bits wide, the units field is 1 bit wide
; and the fraction is 63 bits wide (31 bits in Fraction high and 32 in
; Fraction low).  The exponent is biased by 16383 = 0x3FFF.  The Units
; bit is used instead of having the fraction have an implicit leading
; 1.  The Reserved bits are ignored when read and always written as 0.
;
; The floating point registers are kept in Internal format.  This is
; the same as Extended format except that the first word contains a
; new field:
;
; The Internal format is 96 bits wide:
;
;     address:  | Sign | Uncommon | Reserved  | Exponent |
; address + 4:  | Units |          Fraction high         |
; address + 8:  |              Fraction low              |
;
; The sign field is 1 bit wide, the uncommon field is 1 bit wide, the
; reserved field is 15 bits wide, the exponent field is 15 bits wide,
; the units field is 1 bit wide and the fraction is 63 bits wide (31
; bits in Fraction high and 32 in Fraction low).  The exponent is
; biased by 16383 = 0x3FFF.  The Units bit is used instead of having
; the fraction have an implicit leading 1.  The Reserved bits are
; ignored when read and always written as 0.
;
; SFM stores in Internal format.  When LFM is loading if the uncommon
; bit is set the memory is loaded unchanged.  If the uncommon bit is
; clear LFM will load it as an Extended number possibly setting the
; uncommon bit in the process.Another way of putting this is that LFM
; ORs the uncommon bit from memory with an uncommon bit calculated
; from the other fields of the number in memory.
;
; Extended numbers are interpreted as Internal numbers with the
; uncommon bit clear (which it is).
;
; The following table summarises the Exteded and Internal formats:
;
;  Exponent  Unit  Fraction   What it is       Value
;        0    0       0       signed zero      +0 or -0
;        0    0    non-zero   denorm. number   s * (0.f) * (2**(-16383))
;    32767    0       0       infinity         s * infinity
;    32767    1       0       *** Not a valid bit pattern (see note 1) ***
;    32767    x    non-zero   NaN              NaN
;    other    0    anything   *** Not a valid bit pattern (see note 2) ***
;    other    1    anything   normal number    s * (1.f) * (2**(e-16383))
;
;
;  Notes: 1. This bit pattern is known as an "anomalous infinity" in these
;            sources and is actually treated as s * infinity.
;         2. These bit patterns are known as "unnormalised numbers" in these
;            sources, and are actually treated as representing the value
;            s * (0.f) * (2**(e-16383)). While this behaviour is not part of
;            the architectural specification and should not be relied upon by
;            programmers, it is important to the correct treatment of the
;            intermediate result in the URD/NRM instruction pair in this
;            implementation, and so should not be changed.
;
;   Uncommon   Units   Exponent  Fraction  Notes   What it is
;     bit       bit
;      0         0      0x0000      0      (a)     A zero
;      0         0      0x0000   non-zero          Should not happen
;      0         0      0x4016      x      (b)     Result of URD
;      0         0      0x4033      x      (b)     Result of URD
;      0         0      0x403E      x      (b)     Result of URD
;      0         0      other       x              Should not happen
;      0         1      0x7FFF      x              Should not happen
;      0         1      other       x      (a)     Normalised number
;      1         0      0x0000      0              Should not happen
;      1         0      0x0000   non-zero  (a)     Extended denorm. number
;      1         0      0x7FFF      0      (a)     Extended infinity
;      1         0      0x7FFF   non-zero  (a,d-f) Extended NaN
;      1         0      other       0      (c)     Extended unnormalised zero
;      1         0      other    non-zero  (c)     Extended unnorm. number
;      1         1      0x3C00      0              Should not happen
;      1         1      0x3C00   non-zero  (a)     Double denormalised number
;      1         1      0x3F80      0              Should not happen
;      1         1      0x3F80   non-zero  (a)     Single denormalised number
;      1         1      0x407F      0      (a)     Single infinity
;      1         1      0x407F   non-zero  (a,e)   Single NaN
;      1         1      0x43FF      0      (a)     Double infinity
;      1         1      0x43FF   non-zero  (a,e)   Double NaN
;      1         1      0x7FFF      0      (c)     Anomalous ext. infinity
;      1         1      0x7FFF   non-zero  (a,d-f) Extended NaN
;      1         1      other       x              Should not happen
;
; Notes:
;
; (a) These bit patterns occur normally.
;     The original format is kept for NaNs because exceptions are
;     generated for signalling NaNs only when converting to a
;     different format.  The original format is kept for denormalised
;     numbers and infinites just because it is convenient.
;
; (b) These bit patterns  are the intermediate result of URD before NRM.
;     They are treated as unnormalized numbers.  URD followed by NRM
;     implements RND, or the IEEE "Round a floating point number to
;     another floating point number whose value is an integer"
;     operation (see section 5.5 "Round Floating-Point Number to
;     Integer Value" on page 11 of the standard).  If one of these
;     numbers is saved (SFM) and restored (LFM) the uncommon bit may
;     become set.  ("may" rather than "will" because the URD
;     instruction generally doesn't change numbers which are
;     sufficiently large to already have an integer value). The same
;     applies to STFE followed by LDFE (for the benefit of programs
;     which use that pair for register preservation &
;     restoration). This setting of the uncommon bit is OK because the
;     URD results are chosen so that setting the uncommon bit
;     transforms them into extended unnormalised numbers which have
;     the correct values for the results.
;
; (c) Bit patterns that technically have no meaning.
;     These can only be generated by abusing LDFE and LFM. See Notes 1
;     & 2 above.
;
; (d) These are indeed both "Extended NaN": the units bit is effectively a
;     "don't care" bit for extended NaNs. This is basically just a
;     consequence of extended precision having a units bit, while single and
;     double precision don't: the "anomalous extended infinity" is a similar
;     consequence.
;
; (e) The general rules about NaN processing are:
;
;     * If the top fraction bit is a 1, the NaN is a quiet NaN; if a 0, the
;       NaN is a signalling NaN. (N.B. This is the top fraction bit - i.e.
;       the second bit of the mantissa - rather than the units bit because
;       the units bit does not exist in all formats.)
;
;     * A format conversion on a NaN will truncate the fraction at the
;       appropriate point for a format narrowing, or extend it with zeros
;       for a format widening. If the original NaN was a signalling NaN, an
;       invalid operation exception is generated. If this exception is
;       untrapped, the result is also "quietened" by having its top fraction
;       bit set. (The net result of this is that the result always ends up
;       having its top fraction bit set and thus being a NaN rather than an
;       infinity, unless the result is generated by a trap handler - in this
;       latter case, the trap handler has the responsibility for producing
;       the "correct" result.)
;
;     * An operation on NaN operand(s) will generate an invalid operation
;       exception if any operand is a signalling NaN, as mandated by the
;       IEEE standard. If this doesn't happen, or if the exception is
;       untrapped, the result is produced by the following rules:
;
;       - If the operation is monadic, the result is obtained by
;         format-converting the operand NaN to the destination format of the
;         operation. (For some versions of the code, the invalid operation
;         exception is suppressed if the operation is MVF, MNF, ABS or STF
;         and no change of format occurs; for others, this doesn't happen.
;         See the discussion under "FPESigNaNCopy_Invalid" in the "main.s"
;         source file for more details of this.)
;
;       - If the operation is dyadic, the result is obtained by
;         format-converting the first operand to the destination format of
;         the operation if the first operand is a NaN, and otherwise by
;         format-converting the second operand similarly. (Note that this
;         rule pays no attention to which NaNs are signalling. In
;         particular, if the first operand is a quiet NaN and the second one
;         a signalling NaN, the second operand will generate the invalid
;         operation exception - but if the exception is untrapped, the first
;         operand will generate the result. This is done to match likely
;         future hardware behaviour.)
;
;     * If an invalid operation exception occurs for other reasons than a
;       NaN operand, and the exception is untrapped, the resulting quiet NaN
;       has units bit 0, top fraction bit 1, all other fraction bits 0, and
;       sign bit equal to what the operation would normally have produced -
;       e.g. EOR of the operand signs for infinity * 0; ((rounding mode =
;       "to -infinity") ? 1 : 0) for infinity - infinity; etc. (This is
;       again to match likely future hardware behaviour.)
;
; (f) The NE bit in the FPSR modifies the rules about extended NaNs when it
;     is 0. Basically, these rules cause extended precision to no longer be
;     a fully supported IEEE format, but are necessary to allow code that
;     uses STFE/LDFE for register preservation and restoration to use
;     signalling NaNs effectively. (I.e. basically code that uses the
;     "/fpe2" APCS option and some other legacy code.)
;
;     The problem for such code is that if extended precision is treated as
;     a fully supported IEEE precision, a register-preserving STFE normally
;     contains an implicit format conversion and so *must* generate an
;     exception. Having a procedure call generate an exception merely
;     because the calling procedure happens to have a signalling NaN in a
;     register isn't very desirable...
;
;     To deal with this, NE=0 provides a "legacy code compatibility" option
;     in which an extended precision NaN is regarded as being "really
;     single" or "really double", depending on whether the bottom bit of the
;     extended precision mantissa is 0 or 1 (respectively). Format
;     conversions from single or double precision to extended precision then
;     clear or set this bit appropriately in addition to the operations
;     described above, and never generate an invalid operation exception.
;     Format conversions from a "really single" extended signalling NaN to
;     single precision or from a "really double" extended signalling NaN to
;     double precision are regarded as not involving a change of precision
;     and thus not generating an invalid operation exception; ones from a
;     "really single" extended NaN to double precision or a "really double"
;     extended NaN to single precision still operate as normal.
;
;     NE=1 provides full IEEE compatibility, in which any conversion of a
;     signalling NaN from one of single, double or extended precision to
;     another will generate an invalid operation exception.
;
;     Note also that all this only applies to current systems like the
;     FPA+FPASC which don't generate invalid operation exceptions for copies
;     of signalling NaNs without change of format. Possible future hardware
;     systems which generate invalid operation exceptions on any copy of a
;     signalling NaN by an MVF, MNF, ABS or STF instruction will pay no
;     attention to the NE bit and only supply the full IEEE compatibility
;     option.

;===========================================================================

; Fields in top words of numbers
; ------------------------------

; Single precision fields:

SFrc_pos        EQU     0
SFrc_len        EQU     23
SFrc_mask       EQU     ((1:SHL:SFrc_len) - 1):SHL:SFrc_len
SExp_pos        EQU     23
SExp_len        EQU     8
SExp_mask       EQU     ((1:SHL:SExp_len) - 1):SHL:SExp_pos

; Double precision fields:

DFhi_pos        EQU     0
DFhi_len        EQU     20
DFhi_mask       EQU     ((1:SHL:DFhi_len) - 1):SHL:DFhi_len
DExp_pos        EQU     20
DExp_len        EQU     11
DExp_mask       EQU     ((1:SHL:DExp_len) - 1):SHL:DExp_pos

; Extended and internal precision fields:

EIExp_pos       EQU     0
EIExp_len       EQU     15
EIExp_mask      EQU     ((1:SHL:EIExp_len) - 1):SHL:EIExp_pos
IRsv_pos        EQU     15
IRsv_mask       EQU     &7FFF:SHL:IRsv_pos
ERsv_pos        EQU     15
ERsv_mask       EQU     &FFFF:SHL:ERsv_pos
Uncommon_pos    EQU     30
Uncommon_bit    EQU     1:SHL:Uncommon_pos

EIExp_mask_pt1  EQU     EIExp_mask:AND:&FF
EIExp_mask_pt2  EQU     EIExp_mask:AND:&FF00
                ASSERT  EIExp_mask_pt1:OR:EIExp_mask_pt2 = EIExp_mask
                ASSERT  EIExp_mask_pt1:AND:EIExp_mask_pt2 = 0

IRsv_mask_pt1   EQU     IRsv_mask:AND:&3FC000
IRsv_mask_pt2   EQU     IRsv_mask:AND:&3FC00000
                ASSERT  IRsv_mask_pt1:OR:IRsv_mask_pt2 = IRsv_mask
                ASSERT  IRsv_mask_pt1:AND:IRsv_mask_pt2 = 0

; Shared fields:

Sign_pos        EQU     31
Sign_bit        EQU     1:SHL:Sign_pos

; The following immediate mask will reduce a sign/uncommon/exponent word to
; just the exponent.

ToExp_mask      EQU     &FFFFFFFF - Sign_bit - Uncommon_bit
                ASSERT  EIExp_pos = 0   ;This mask won't do its job otherwise

; The minimum and maximum allowed exponents for single, double and extended
; precision numbers held in internal format.

SMin_Exp        EQU     &3F81
SMax_Exp        EQU     &407E
DMin_Exp        EQU     &3C01
DMax_Exp        EQU     &43FE
EMin_Exp        EQU     &0000
EMax_Exp        EQU     &7FFE

; The normal exponent bias in a single, a double and an extended or internal
; precision number. In the first two cases, the bias for a denormalised
; number is one smaller.

SExp_bias       EQU     &7F
DExp_bias       EQU     &3FF
EIExp_bias      EQU     &3FFF

; The special exponents for NaNs and infinities of various precisions.

NaNInfExp_Single        EQU     &407F
NaNInfExp_Double        EQU     &43FF
NaNInfExp_Extended      EQU     &7FFF

; The special exponents for denormalised numbers of various precisions.

DenormExp_Single        EQU     &3F80
DenormExp_Double        EQU     &3C00
DenormExp_Extended      EQU     &0000

; The bias adjustments for entry to overflow and underflow trap handlers.

TrapBiasAdjust_Single   EQU     &C0
TrapBiasAdjust_Double   EQU     &600
TrapBiasAdjust_Extended EQU     &6000

;===========================================================================

; Fields in other words of numbers
; --------------------------------

EIUnits_pos     EQU     31
EIUnits_bit     EQU     1:SHL:EIUnits_pos
EIFracTop_pos   EQU     30
EIFracTop_bit   EQU     1:SHL:EIFracTop_pos

;===========================================================================

; Comparison results
; ------------------

Comp_GT         EQU     &20000000
Comp_EQ         EQU     &60000000
Comp_LT         EQU     &80000000
Comp_Un_Orig    EQU     &10000000
Comp_Un_Alt     EQU     &30000000

;===========================================================================

; Floating point condition codes
;
; Here are the FPE/ARM condition code maps.  The FPE has an FPSR bit
; called AC that determines if the old mapping or new is used:
;
; With AC=0:
;
; Relation         Z  C  N  V
; ---------------------------
; EQUAL            1  1  0  0
; LESS THAN        0  0  1  0
; GREATER TNAN     0  1  0  0
; UNORDERED        0  0  0  1
;
; Code Nm Flags        Meaning           Floating point meaning
; ------------------------------------------------------------------
; 0000 EQ Z==1         equal             equal
; 0001 NE Z==0         not equal         not equal (includes unordered)
; 0010 HS C==1         higher or same    greater or equal
; 0011 LO C==0         lower than        less than or unordered
; 0100 MI N==1         negative          less than
; 0101 PL N==0         nonnegative       greater, equal, or unordered
; 0110 VS V==1         overflow          unordered
; 0111 VC V==0         not overflow      less, greater, or equal
; 1000 HI C==1 && Z==0 higher than       greater than
; 1001 LS C==0 || Z==1 lower or same     less, equal, or unordered
; 1010 GE N==V         greater or equal  greater or equal (same as 0010)
; 1011 LT N!=V         less than         less than or unordered (same as 0011)
; 1100 GT Z==0 && N==V greater than      greater than (same as 1000)
; 1101 LE Z==1 || N!=V less or equal     less, equal, or unordered (same as 1001)
; 1110 AL don't care   always            always
; 1111    don't care   never             never
;
; With AC=1:
;
; Relation         Z  C  N  V
; --- ------------------------
; EQUAL            1  1  0  0
; LESS THAN        0  0  1  0
; GREATER TNAN     0  1  0  0
; UNORDERED        0  1  0  1
;
; The only difference is the UNORDERED now sets both C and V.
; Now: C <==> greater than or equal or unordered
;
; This changes the  condition code table to:
;
; Code Nm Flags        Meaning           Floating point meaning
; --- ---------------------------------------------------------------
; 0000 EQ Z==1         equal             equal
; 0001 NE Z==0         not equal         not equal (includes unordered)
; 0010 HS C==1         higher or same    greater, equal, or unordered
; 0011 LO C==0         lower than        less than
; 0100 MI N==1         negative          less than
; 0101 PL N==0         nonnegative       greater, equal, or unordered
; 0110 VS V==1         overflow          unordered
; 0111 VC V==0         not overflow      less, greater, or equal
; 1000 HI C==1 && Z==0 higher than       greater or unordered
; 1001 LS C==0 || Z==1 lower or same     less or equal
; 1010 GE N==V         greater or equal  greater or equal
; 1011 LT N!=V         less than         less than or unordered
; 1100 GT Z==0 && N==V greater than      greater than
; 1101 LE Z==1 || N!=V less or equal     less, equal, or unordered
; 1110 AL don't care   always            always
; 1111    don't care   never             never
;
; Only the entries for 0010, 0011, 1000 and 1001 have changed.
;
; Now all floating point conditionals that can be expressed in C are
; available in one test.
;
; The ARM C compiler does not yet do the right thing for floating
; point comparisons.

;===========================================================================

; Invalid operation reason codes
; ------------------------------
;   These were once used to construct quiet NaNs which would give some
; indication what sort of operation created the NaN. They are now only used
; for some internal purposes, having been removed because it is very
; unlikely that any future hardware which handles NaNs will mimic this
; behaviour.
;   InvReas_InitNaN is not an invalid operation reason code; however, like
; all the others, it is related to a NaN that the system can generate. It is
; therefore placed in the same set of numbers.
;   InvReas_MsvOverflow and InvReas_MsvUnderflow are similar: NaNs
; (originally constructed from them) are used on entry to overflow and
; underflow trap handlers respectively to indicate that the result is so
; massively out of range that the IEEE-specified exponent bias adjustment
; (&C0 for single, &600 for double and &6000 for extended) is not enough to
; bring it in range.

InvReas_SigNaN          EQU     0       ;An operand is a signalling NaN
InvReas_InitNaN         EQU     1       ;(Used to generate initial NaNs)
InvReas_MsvOverflow     EQU     2       ;(Used for massive overflow)
InvReas_MsvUnderflow    EQU     3       ;(Used for massive underflow)
InvReas_MagSubInf       EQU     4       ;Magnitude subtraction of infinities
InvReas_InfTimes0       EQU     5       ;Infinity times zero
InvReas_0TimesInf       EQU     6       ;Zero times infinity
InvReas_0Div0           EQU     7       ;Zero divided by zero
InvReas_InfDivInf       EQU     8       ;Infinity divided by infinity
InvReas_InfRemX         EQU     9       ;RMF with 1st operand infinite
InvReas_XRem0           EQU     10      ;RMF of non-infinite number by zero
InvReas_SqrtNeg         EQU     11      ;Square root of a negative number
InvReas_FixQNaN         EQU     12      ;FIX applied to a quiet NaN
InvReas_FixInf          EQU     13      ;FIX applied to an infinity
InvReas_FixRange        EQU     14      ;FIX on an out-of-range number
InvReas_CompQNaN        EQU     15      ;CMFE/CNFE on a quiet NaN
InvReas_SinCosRange     EQU     16      ;SIN/COS on too big an argument
InvReas_SinCosInf       EQU     17      ;SIN/COS on an infinity
InvReas_TanRange        EQU     18      ;TAN on too big an argument
InvReas_TanInf          EQU     19      ;TAN on an infinity
InvReas_AsnAcsRange     EQU     20      ;ASN/ACS on too big an argument
InvReas_AsnAcsInf       EQU     21      ;ASN/ACS on an infinity
InvReas_PolZeroZero     EQU     22      ;POL on two zeros
InvReas_PolInfInf       EQU     23      ;POL on two infinities
InvReas_LgnLogNeg       EQU     24      ;LGN/LOG of a negative argument
InvReas_NegPowX         EQU     25      ;POW/RPW to do (negative)^X
InvReas_0PowNonpos      EQU     26      ;POW/RPW to do (zero)^(non-positive)
InvReas_BadInfPow       EQU     27      ;POW/RPW to do 1^(+/-infinity) or
                                        ; (+infinity)^0

;===========================================================================

        END
