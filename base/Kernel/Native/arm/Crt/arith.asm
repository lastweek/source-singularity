;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;
        
; arith.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

; > coresrc.s.arith
;
; Assembler source for FPA support code and emulator
; ==================================================
; Routines to do arithmetic.
;

; These routines work on numbers in the standard internal format.

;===========================================================================

        GBLS    NormaliseOp1_str
        GBLS    NormaliseOp1Neg_str
        GBLS    NormaliseOp2_str
        GBLS    NormDenormOp1_str
        GBLS    NormDenormOp2_str

        GBLS    ConvertNaNs_str
        GBLS    ConvertNaN1_str
        GBLS    ConvertNaN1Of2_str
        GBLS    ConvertNaN2Of2_str

        GBLL    FPLibWanted

 [ FPEWanted :LOR: FPASCWanted

NormaliseOp1_str        SETS    "NormaliseOp1"
NormaliseOp1Neg_str     SETS    "NormaliseOp1Neg"
NormaliseOp2_str        SETS    "NormaliseOp2"
NormDenormOp1_str       SETS    "NormDenormOp1"
NormDenormOp2_str       SETS    "NormDenormOp2"

ConvertNaNs_str         SETS    "ConvertNaNs"
ConvertNaN1_str         SETS    "ConvertNaN1"
ConvertNaN1Of2_str      SETS    "ConvertNaN1Of2"
ConvertNaN2Of2_str      SETS    "ConvertNaN2Of2"

FPLibWanted             SETL    {FALSE}

 |

NormaliseOp1_str        SETS    "__fp_normalise_op1"
NormaliseOp1Neg_str     SETS    "__fp_normalise_op1neg"
NormaliseOp2_str        SETS    "__fp_normalise_op2"
NormDenormOp1_str       SETS    "__fp_norm_denorm_op1"
NormDenormOp2_str       SETS    "__fp_norm_denorm_op2"

ConvertNaNs_str         SETS    "__fp_convert_NaNs"
ConvertNaN1_str         SETS    "__fp_convert_NaN1"
ConvertNaN1Of2_str      SETS    "__fp_convert_NaN_1Of2"
ConvertNaN2Of2_str      SETS    "__fp_convert_NaN_2Of2"

FPLibWanted             SETL    {TRUE}

   [ :LNOT: :DEF: normalise_s

        IMPORT  $NormaliseOp1_str
        IMPORT  $NormaliseOp1Neg_str
        IMPORT  $NormaliseOp2_str
        IMPORT  $NormDenormOp1_str
        IMPORT  $NormDenormOp2_str

        IMPORT  $ConvertNaNs_str
        IMPORT  $ConvertNaN1_str
        IMPORT  $ConvertNaN1Of2_str
        IMPORT  $ConvertNaN2Of2_str
   ]
        
 ]

        [ :DEF: normalise_s :LOR: FPEWanted :LOR: FPASCWanted

; Many of these routines use some standard entry and exit conventions. There
; are two such sets of conventions:
;
; STANDARD MONADIC OPERATION ENTRY AND EXIT
; -----------------------------------------
;
; Entry: OP1sue = Operand sign, uncommon, exponent;
;        OP1mhi = Operand mantissa, high word;
;        OP1mlo = Operand mantissa, low word;
;        Rfpsr  = FPSR;
;        Rins   = instruction (may be needed to determine the exact
;          operation and/or for traps);
;        Rwp, Rfp, Rsp hold their usual values;
;        R14    = return link.
; Exit:  OP1sue = the result's sign and uncommon bit; the remaining bits are
;          zero if the uncommon bit is 0, and set correctly for the final
;          result if the uncommon bit is 1;
;        OP1mhi, OP1mlo = the result's mantissa;
;        RNDexp (= OP2sue) = if the uncommon bit is 0, the result exponent,
;          which may be negative; otherwise corrupt;
;        Rarith is corrupt if the uncommon bit is 1; otherwise, if the
;          destination precision is extended, it holds the round bit (in bit
;          31) and the sticky bit (in bits 30:0), and if the destination
;          precision is single or double, it holds part of the sticky bit
;          (the remainder of which is held in bits below the round bit in
;          OP1mhi and OP1mlo);
;        OP2mhi, OP2mlo, Rtmp, Rtmp2 and R14 may be corrupt;
;        Rfpsr may be updated;
;        All other registers preserved.
;
; STANDARD DYADIC OPERATION ENTRY AND EXIT
; ----------------------------------------
;
; Entry: OP1sue = First operand sign, uncommon, exponent;
;        OP1mhi = First operand mantissa, high word;
;        OP1mlo = First operand mantissa, low word;
;        OP2sue = Second operand sign, uncommon, exponent;
;        OP2mhi = Second operand mantissa, high word;
;        OP2mlo = Second operand mantissa, low word;
;        Rfpsr  = FPSR;
;        Rins   = instruction (may be needed to determine the exact
;          operation and/or for traps);
;        Rwp, Rfp, Rsp hold their usual values;
;        R14    = return link.
; Exit:  OP1sue = the result's sign and uncommon bit; the remaining bits are
;          zero if the uncommon bit is 0, and set correctly for the final
;          result if the uncommon bit is 1;
;        OP1mhi, OP1mlo = the result's mantissa;
;        RNDexp (= OP2sue) = if the uncommon bit is 0, the result exponent,
;          which may be negative; otherwise corrupt;
;        Rarith is corrupt if the uncommon bit is 1; otherwise, if the
;          destination precision is extended, it holds the round bit (in bit
;          31) and the sticky bit (in bits 30:0), and if the destination
;          precision is single or double, it holds part of the sticky bit
;          (the remainder of which is held in bits below the round bit in
;          OP1mhi and OP1mlo);
;        OP2mhi, OP2mlo, Rtmp, Rtmp2 and R14 may be corrupt;
;        Rfpsr may be updated;
;        All other registers preserved.
;
; In both sets of conventions, the routine called is free to produce an
; incorrect result mantissa and rounding information, as long as it knows
; that it will in fact be rounded to the correct value.

;===========================================================================

; Routine to normalise the first or only operand. The biased exponent won't
; be taken below 0: instead, the number will be denormalised if normalising
; it would cause this to happen. Note that the result will never be marked
; as uncommon: any caller of this routine must deal with this itself if
; necessary.
; Entry: OP1sue = First operand sign, remaining bits junk;
;        OP1mhi, OP1mlo = First operand mantissa;
;        Rarith = First operand exponent, shifted to be left aligned in the
;          word;
;        Rwp, Rfp, Rsp contain their usual values;
;        R14 is the return link.
; Exit:  OP1sue = First operand sign and exponent (uncommon is always 0);
;        OP1mhi, OP1mlo updated;
;        Rarith, Rtmp, Rtmp2 and R14 may be corrupt;
;        All other registers preserved.

$NormDenormOp1_str

; Clear out the junk bits in OP1sue.

        AND     OP1sue,OP1sue,#Sign_bit

; Do we have to normalise by 32 bits or more?

        TEQ     OP1mhi,#0
        BEQ     NormDenormOp1_LongShift

; If not, find out how much we do have to shift by.

        MOV     Rtmp,#0                 ;Accumulate shift amount in Rtmp
        MOVS    Rtmp2,OP1mhi,LSR #16
        MOVEQ   OP1mhi,OP1mhi,LSL #16
        ADDEQ   Rtmp,Rtmp,#16
        MOVS    Rtmp2,OP1mhi,LSR #24
        MOVEQ   OP1mhi,OP1mhi,LSL #8
        ADDEQ   Rtmp,Rtmp,#8
        MOVS    Rtmp2,OP1mhi,LSR #28
        MOVEQ   OP1mhi,OP1mhi,LSL #4
        ADDEQ   Rtmp,Rtmp,#4
        MOVS    Rtmp2,OP1mhi,LSR #30
        MOVEQ   OP1mhi,OP1mhi,LSL #2
        ADDEQ   Rtmp,Rtmp,#2
        MOVS    Rtmp2,OP1mhi,LSR #31
        MOVEQ   OP1mhi,OP1mhi,LSL #1
        ADDEQ   Rtmp,Rtmp,#1

; Have we shifted too far? - i.e. by more than the exponent? If so, go back
; the excess distance. Then complete the shift - i.e. convert the single
; word shift into a two word shift - adjust the exponent if the exponent was
; greater than the shift amount (otherwise we leave it zero) and return.

        SUBS    Rtmp2,Rtmp,Rarith,LSR #32-EIExp_len     ;Shift amt. - exp.
        MOVHI   OP1mhi,OP1mhi,LSR Rtmp2
        MOVHI   Rtmp,Rarith,LSR #32-EIExp_len
        RSB     Rarith,Rtmp,#32
        ORR     OP1mhi,OP1mhi,OP1mlo,LSR Rarith
        MOV     OP1mlo,OP1mlo,LSL Rtmp
        SUBLO   OP1sue,OP1sue,Rtmp2,LSL #EIExp_pos      ;ADD exp.-shift amt.

  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC, LR
  ENDIF

NormDenormOp1_LongShift

; The top word is zero, so we need to shift by 32 bits or more. Or do we? -
; if the exponent is less than 32, we simply need to shift by the exponent.

        CMP     Rarith,#32:SHL:(32-EIExp_len)
        BLO     NormDenormOp1_ByExponent

; Now check the bottom word: if it is also zero, we simply need to
; denormalise to exponent 0.

        MOVS    OP1mhi,OP1mlo
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR           ;OP1sue/mhi/mlo are all already correct!
  ENDIF

        MOV     OP1mlo,#0

; The bottom word is non-zero, so we have a shift amount in the range 32-63.

        MOV     Rtmp,#32
        MOVS    Rtmp2,OP1mhi,LSR #16
        MOVEQ   OP1mhi,OP1mhi,LSL #16
        ADDEQ   Rtmp,Rtmp,#16
        MOVS    Rtmp2,OP1mhi,LSR #24
        MOVEQ   OP1mhi,OP1mhi,LSL #8
        ADDEQ   Rtmp,Rtmp,#8
        MOVS    Rtmp2,OP1mhi,LSR #28
        MOVEQ   OP1mhi,OP1mhi,LSL #4
        ADDEQ   Rtmp,Rtmp,#4
        MOVS    Rtmp2,OP1mhi,LSR #30
        MOVEQ   OP1mhi,OP1mhi,LSL #2
        ADDEQ   Rtmp,Rtmp,#2
        MOVS    Rtmp2,OP1mhi,LSR #31
        MOVEQ   OP1mhi,OP1mhi,LSL #1
        ADDEQ   Rtmp,Rtmp,#1

; Have we shifted too far? - i.e. by more than the exponent? If so, go back
; the excess distance. Note that this cannot require us to undo the shift
; from the bottom word to the top word, since we know the exponent was at
; least 32.
;   So we need to backshift if shift amount > exponent, and create a
; non-zero exponent if shift amount < exponent.

        SUBS    Rtmp2,Rtmp,Rarith,LSR #32-EIExp_len     ;Shift amt. - exp.
        MOVHI   OP1mhi,OP1mhi,LSR Rtmp2
        SUBLO   OP1sue,OP1sue,Rtmp2,LSL #EIExp_pos      ;ADD exp.-shift amt.
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF


NormDenormOp1_ByExponent

; We need to shift the mantissa left by the exponent, which is guaranteed to
; be less than 32, and to return a zero exponent (note that OP1sue is
; already set up for this).

        MOV     Rtmp,Rarith,LSR #32-EIExp_len
        RSB     Rtmp2,Rtmp,#32
        MOV     OP1mhi,OP1mhi,LSL Rtmp
        ORR     OP1mhi,OP1mhi,OP1mlo,LSR Rtmp2
        MOV     OP1mlo,OP1mlo,LSL Rtmp
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

;===========================================================================

; Routine to normalise the second operand. The biased exponent won't be
; taken below 0: instead, the number will be denormalised if normalising it
; would cause this to happen. Note that the result will never be marked
; as uncommon: any caller of this routine must deal with this itself if
; necessary.
; Entry: OP2sue = Second operand sign, remaining bits junk;
;        OP2mhi, OP2mlo = Second operand mantissa;
;        Rarith = Second operand exponent, shifted to be left aligned in the
;          word;
;        Rwp, Rfp, Rsp contain their usual values;
;        R14 is the return link.
; Exit:  OP2sue = Second operand sign and exponent (uncommon is always 0);
;        OP2mhi, OP2mlo updated;
;        Rarith, Rtmp, Rtmp2 and R14 may be corrupt;
;        All other registers preserved.

$NormDenormOp2_str

; Clear out the junk bits in OP2sue.

        AND     OP2sue,OP2sue,#Sign_bit

; Do we have to normalise by 32 bits or more?

        TEQ     OP2mhi,#0
        BEQ     NormDenormOp2_LongShift

; If not, find out how much we do have to shift by.

        MOV     Rtmp,#0                 ;Accumulate shift amount in Rtmp
        MOVS    Rtmp2,OP2mhi,LSR #16
        MOVEQ   OP2mhi,OP2mhi,LSL #16
        ADDEQ   Rtmp,Rtmp,#16
        MOVS    Rtmp2,OP2mhi,LSR #24
        MOVEQ   OP2mhi,OP2mhi,LSL #8
        ADDEQ   Rtmp,Rtmp,#8
        MOVS    Rtmp2,OP2mhi,LSR #28
        MOVEQ   OP2mhi,OP2mhi,LSL #4
        ADDEQ   Rtmp,Rtmp,#4
        MOVS    Rtmp2,OP2mhi,LSR #30
        MOVEQ   OP2mhi,OP2mhi,LSL #2
        ADDEQ   Rtmp,Rtmp,#2
        MOVS    Rtmp2,OP2mhi,LSR #31
        MOVEQ   OP2mhi,OP2mhi,LSL #1
        ADDEQ   Rtmp,Rtmp,#1

; Have we shifted too far? - i.e. by more than the exponent? If so, go back
; the excess distance. Then complete the shift - i.e. convert the single
; word shift into a two word shift - adjust the exponent if the exponent was
; greater than the shift amount (otherwise we leave it zero) and return.

        SUBS    Rtmp2,Rtmp,Rarith,LSR #32-EIExp_len     ;Shift amt. - exp.
        MOVHI   OP2mhi,OP2mhi,LSR Rtmp2
        MOVHI   Rtmp,Rarith,LSR #32-EIExp_len
        RSB     Rarith,Rtmp,#32
        ORR     OP2mhi,OP2mhi,OP2mlo,LSR Rarith
        MOV     OP2mlo,OP2mlo,LSL Rtmp
        SUBLO   OP2sue,OP2sue,Rtmp2,LSL #EIExp_pos      ;ADD exp.-shift amt.
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

NormDenormOp2_LongShift

; The top word is zero, so we need to shift by 32 bits or more. Or do we? -
; if the exponent is less than 32, we simply need to shift by the exponent.

        CMP     Rarith,#32:SHL:(32-EIExp_len)
        BLO     NormDenormOp2_ByExponent

; Now check the bottom word: if it is also zero, we simply need to
; denormalise to exponent 0.

        MOVS    OP2mhi,OP2mlo
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR           ;OP2sue/mhi/mlo are all already correct!
  ENDIF
        MOV     OP2mlo,#0

; The bottom word is non-zero, so we have a shift amount in the range 32-63.

        MOV     Rtmp,#32
        MOVS    Rtmp2,OP2mhi,LSR #16
        MOVEQ   OP2mhi,OP2mhi,LSL #16
        ADDEQ   Rtmp,Rtmp,#16
        MOVS    Rtmp2,OP2mhi,LSR #24
        MOVEQ   OP2mhi,OP2mhi,LSL #8
        ADDEQ   Rtmp,Rtmp,#8
        MOVS    Rtmp2,OP2mhi,LSR #28
        MOVEQ   OP2mhi,OP2mhi,LSL #4
        ADDEQ   Rtmp,Rtmp,#4
        MOVS    Rtmp2,OP2mhi,LSR #30
        MOVEQ   OP2mhi,OP2mhi,LSL #2
        ADDEQ   Rtmp,Rtmp,#2
        MOVS    Rtmp2,OP2mhi,LSR #31
        MOVEQ   OP2mhi,OP2mhi,LSL #1
        ADDEQ   Rtmp,Rtmp,#1

; Have we shifted too far? - i.e. by more than the exponent? If so, go back
; the excess distance. Note that this cannot require us to undo the shift
; from the bottom word to the top word, since we know the exponent was at
; least 32.
;   So we need to backshift if shift amount > exponent, and create a
; non-zero exponent if shift amount < exponent.

        SUBS    Rtmp2,Rtmp,Rarith,LSR #32-EIExp_len     ;Shift amt. - exp.
        MOVHI   OP2mhi,OP2mhi,LSR Rtmp2
        SUBLO   OP2sue,OP2sue,Rtmp2,LSL #EIExp_pos      ;ADD exp.-shift amt.
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

NormDenormOp2_ByExponent

; We need to shift the mantissa left by the exponent, which is guaranteed to
; be less than 32, and to return a zero exponent (note that OP2sue is
; already set up for this).

        MOV     Rtmp,Rarith,LSR #32-EIExp_len
        RSB     Rtmp2,Rtmp,#32
        MOV     OP2mhi,OP2mhi,LSL Rtmp
        ORR     OP2mhi,OP2mhi,OP2mlo,LSR Rtmp2
        MOV     OP2mlo,OP2mlo,LSL Rtmp
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

;===========================================================================

; Routine to float an integer. To fit in with the usual conventions, the
; entry point is given two labels, namely "FltFPE" and "FltFPASC".
;   The value returned is always a numeric value plus associated rounding
; information, with the uncommon bit clear.
; Entry: Rarith = integer;
;        Rfpsr  = FPSR;
;        Rins   = instruction (needed for traps);
;        Rwp, Rfp, Rsp hold their usual values;
;        R14    = return link.
; Exit:  OP1sue = the result's sign, with the remaining bits zero;
;        OP1mhi, OP1mlo = the result's mantissa;
;        RNDexp (= OP2sue) = the result exponent;
;        Rarith = 0 (i.e. the appropriate round and sticky information for
;          extended precision);
;        OP2mhi, OP2mlo, Rtmp, Rtmp2 and R14 may be corrupt;
;        Rfpsr may be updated;
;        All other registers preserved.

        [ FPEWanted
FltFPE
        ]

        [ FPASCWanted
FltFPASC
        ]

        CDebug1 3,"FltFPE/FPASC: operand =",Rarith

; Extract the sign and produce an unnormalised mantissa. In the process,
; detect the special case of a zero operand.

        MOV     OP1mlo,#0               ;Mantissa low word is always zero
        ANDS    OP1sue,Rarith,#Sign_bit ;Extract sign
        ASSERT  Sign_pos = 31
        RSBNE   OP1mhi,Rarith,#0        ;If -ve, 2's complement the integer
        MOVEQS  OP1mhi,Rarith           ;If +ve, copy and check for zero
        MOVEQ   RNDexp,#0               ;If zero, result exponent is zero
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR                   ; and return (Rarith is already 0)
  ENDIF

; If non-zero, set the approriate exponent and rounding information, then
; fall through into NormaliseOp1 to complete the job.

        MOV     RNDexp,#(EIExp_bias+31):AND:&FF00
        ORR     RNDexp,RNDexp,#(EIExp_bias+31):AND:&FF
        ASSERT  (EIExp_bias+31) <= &FFFF
        MOV     Rarith,#0

; Fall through to NormaliseOp1

;===========================================================================

; NB it is possible to fall through into this routine.

; Routine to normalise the result or first operand. Unlike the two routines
; above, this routine will normalise the exponent to a value less than zero
; if necessary, and it won't put the exponent back into OP1sue. Note that
; the result will never be marked as uncommon: any caller of this routine
; must deal with this itself if necessary.
; Entry: OP1mhi, OP1mlo = Result/first operand mantissa, which must not be
;          all zero;
;        RNDexp = Result/first operand exponent (in normal position in
;          word);
;        Rwp, Rfp, Rsp contain their usual values;
;        R14 is the return link.
; Exit:  OP1mhi, OP1mlo and RNDexp updated;
;        Rtmp, Rtmp2 and R14 may be corrupt;
;        All other registers preserved;
;        NE condition is true.

$NormaliseOp1_str
        TEQ     OP1mhi,#0                       ;Do full word shift if
        MOVEQ   OP1mhi,OP1mlo                   ; necessary
        MOVEQ   OP1mlo,#0
        SUBEQ   RNDexp,RNDexp,#32
        MOV     Rtmp,#0                         ;Counter for rest of shift
        MOVS    Rtmp2,OP1mhi,LSR #16            ;Shift top word by 16 if
        MOVEQ   OP1mhi,OP1mhi,LSL #16           ; necessary
        ADDEQ   Rtmp,Rtmp,#16
        MOVS    Rtmp2,OP1mhi,LSR #24            ;Shift top word by 8 if
        MOVEQ   OP1mhi,OP1mhi,LSL #8            ; necessary
        ADDEQ   Rtmp,Rtmp,#8
        MOVS    Rtmp2,OP1mhi,LSR #28            ;Shift top word by 4 if
        MOVEQ   OP1mhi,OP1mhi,LSL #4            ; necessary
        ADDEQ   Rtmp,Rtmp,#4
        MOVS    Rtmp2,OP1mhi,LSR #30            ;Shift top word by 2 if
        MOVEQ   OP1mhi,OP1mhi,LSL #2            ; necessary
        ADDEQ   Rtmp,Rtmp,#2
        MOVS    Rtmp2,OP1mhi,LSR #31            ;Shift top word by 1 if
        MOVEQ   OP1mhi,OP1mhi,LSL #1            ; necessary
        ADDEQ   Rtmp,Rtmp,#1
        RSBS    Rtmp2,Rtmp,#32                  ;Shift the bottom word by
        ORR     OP1mhi,OP1mhi,OP1mlo,LSR Rtmp2  ; the same amount and set NE
        MOV     OP1mlo,OP1mlo,LSL Rtmp
        SUB     RNDexp,RNDexp,Rtmp              ;Adjust exponent by shift
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR                           ; amount and return
  ENDIF

;===========================================================================

; Routine to normalise the second operand. Unlike the two routines above,
; this routine will normalise the exponent to a value less than zero if
; necessary, and it won't put the exponent back into OP1sue. Note that the
; result will never be marked as uncommon: any caller of this routine must
; deal with this itself if necessary.
; Entry: OP2mhi, OP2mlo = Second operand mantissa, which must not be all
;          zero;
;        RNDexp = Second operand exponent (in normal position in word);
;        Rwp, Rfp, Rsp contain their usual values;
;        R14 is the return link.
; Exit:  OP2mhi, OP2mlo and RNDexp updated;
;        Rtmp, Rtmp2 and R14 may be corrupt;
;        All other registers preserved;
;        NE condition is true.

$NormaliseOp2_str
        TEQ     OP2mhi,#0                       ;Do full word shift if
        MOVEQ   OP2mhi,OP2mlo                   ; necessary
        MOVEQ   OP2mlo,#0
        SUBEQ   RNDexp,RNDexp,#32
        MOV     Rtmp,#0                         ;Counter for rest of shift
        MOVS    Rtmp2,OP2mhi,LSR #16            ;Shift top word by 16 if
        MOVEQ   OP2mhi,OP2mhi,LSL #16           ; necessary
        ADDEQ   Rtmp,Rtmp,#16
        MOVS    Rtmp2,OP2mhi,LSR #24            ;Shift top word by 8 if
        MOVEQ   OP2mhi,OP2mhi,LSL #8            ; necessary
        ADDEQ   Rtmp,Rtmp,#8
        MOVS    Rtmp2,OP2mhi,LSR #28            ;Shift top word by 4 if
        MOVEQ   OP2mhi,OP2mhi,LSL #4            ; necessary
        ADDEQ   Rtmp,Rtmp,#4
        MOVS    Rtmp2,OP2mhi,LSR #30            ;Shift top word by 2 if
        MOVEQ   OP2mhi,OP2mhi,LSL #2            ; necessary
        ADDEQ   Rtmp,Rtmp,#2
        MOVS    Rtmp2,OP2mhi,LSR #31            ;Shift top word by 1 if
        MOVEQ   OP2mhi,OP2mhi,LSL #1            ; necessary
        ADDEQ   Rtmp,Rtmp,#1
        RSBS    Rtmp2,Rtmp,#32                  ;Shift the bottom word by
        ORR     OP2mhi,OP2mhi,OP2mlo,LSR Rtmp2  ; the same amount and set NE
        MOV     OP2mlo,OP2mlo,LSL Rtmp
        SUB     RNDexp,RNDexp,Rtmp              ;Adjust exponent by shift
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR                           ; amount and return
  ENDIF

;===========================================================================

; Routine to normalise the first operand. Like "NormaliseOp1", except that
; it increments the exponent in RNDexp by the shift amount, rather than
; decrementing it.
; Entry: OP1mhi, OP1mlo = Second operand mantissa, which must not be all
;          zero;
;        RNDexp = Exponent (in normal position in word);
;        Rwp, Rfp, Rsp contain their usual values;
;        R14 is the return link.
; Exit:  OP1mhi, OP1mlo and RNDexp updated;
;        Rtmp, Rtmp2 and R14 may be corrupt;
;        All other registers preserved;
;        NE condition is true.

$NormaliseOp1Neg_str
        TEQ     OP1mhi,#0                       ;Do full word shift if
        MOVEQ   OP1mhi,OP1mlo                   ; necessary
        MOVEQ   OP1mlo,#0
        ADDEQ   RNDexp,RNDexp,#32
        MOV     Rtmp,#0                         ;Counter for rest of shift
        MOVS    Rtmp2,OP1mhi,LSR #16            ;Shift top word by 16 if
        MOVEQ   OP1mhi,OP1mhi,LSL #16           ; necessary
        ADDEQ   Rtmp,Rtmp,#16
        MOVS    Rtmp2,OP1mhi,LSR #24            ;Shift top word by 8 if
        MOVEQ   OP1mhi,OP1mhi,LSL #8            ; necessary
        ADDEQ   Rtmp,Rtmp,#8
        MOVS    Rtmp2,OP1mhi,LSR #28            ;Shift top word by 4 if
        MOVEQ   OP1mhi,OP1mhi,LSL #4            ; necessary
        ADDEQ   Rtmp,Rtmp,#4
        MOVS    Rtmp2,OP1mhi,LSR #30            ;Shift top word by 2 if
        MOVEQ   OP1mhi,OP1mhi,LSL #2            ; necessary
        ADDEQ   Rtmp,Rtmp,#2
        MOVS    Rtmp2,OP1mhi,LSR #31            ;Shift top word by 1 if
        MOVEQ   OP1mhi,OP1mhi,LSL #1            ; necessary
        ADDEQ   Rtmp,Rtmp,#1
        RSBS    Rtmp2,Rtmp,#32                  ;Shift the bottom word by
        ORR     OP1mhi,OP1mhi,OP1mlo,LSR Rtmp2  ; the same amount and set NE
        MOV     OP1mlo,OP1mlo,LSL Rtmp
        ADD     RNDexp,RNDexp,Rtmp              ;Adjust exponent by shift
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR                           ; amount and return
  ENDIF

        ]

;===========================================================================

        [ :DEF: addsub_s :LOR: FPEWanted :LOR: FPASCWanted

; Routine to add, subtract or reverse subtract two internal format floating
; point numbers. It has two entry points: "AddSubFPE", which has an
; optimised fast track for both operands being common, and "AddSubFPASC",
; which avoids the test for this optimised fast track - since it should
; never happen. The second entry point lies a long way down in the source
; to avoid addressing constraints.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard dyadic operation entry and exit conventions - see top of
; this file.

        ASSERT  RNDexp = OP2sue ;We swap over from the use of OP2sue to that
                                ; of RNDexp partway through this routine.

        [ FPEWanted

AddSubFPE

        CDebug3 3,"AddSubFPE: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 3,"           op2 =",OP2sue,OP2mhi,OP2mlo

; Start by detecting the "fast track" case of both operands being common.

        TST     OP1sue,#Uncommon_bit
        TSTEQ   OP2sue,#Uncommon_bit
        BNE     AddSub_Uncommon

        ]

        [ FPLibWanted
__fp_addsub_common
        ]

AddSub_Common

        STMFD   Rsp!,{LR}               ;Register needed, and we may get a
                                        ; subroutine call

        CDebug3 4,"AddSub_Common: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 4,"               op2 =",OP2sue,OP2mhi,OP2mlo

; Both operands are zeros or normalised numbers. We can distinguish between
; them on the basis of the units bit. However, note that the standard
; algorithm for adding/subtracting floating point numbers (i.e. do an
; alignment shift on the one with the smaller exponent, add or subtract the
; mantissas, then do a normalisation shift if necessary) works equally well
; on all of these.

; This entry point is also called from AddSub_Uncommon to add or subtract
; operands which are zeros, normalised numbers or extended denormalised
; numbers. It works perfectly well on such numbers, provided it is
; recognised that the result mantissa may be unnormalised and non-zero.
;   Note that we know that the invalid operation and divide-by-zero
; exceptions won't occur - i.e. we don't need to preserve the operands. So
; we start by modifying the signs of the operands for SUF and RSF
; instructions.

        [ :LNOT: :DEF: addsub_s

        TST     Rins,#SubNotAdd_bit     ;Is it SUF/RSF, not ADF?
        EORNE   OP2sue,OP2sue,#Sign_bit ;If so, change op2 sign (assuming SUF)
        TST     Rins,#RSF_bit           ;Is it RSF, not ADF/SUF?
        EORNE   OP2sue,OP2sue,#Sign_bit ;If so, we shouldn't have changed op2
        EORNE   OP1sue,OP1sue,#Sign_bit ; sign and should have changed op1 sign

        ]

; We can consider this to be an addition from now on. Next, we'll deal with
; the basic exponent and sign calculation: the results of this may get
; modified later on.
;   This section will leave the prospective sign for the result in OP1sue,
; R14 containing the exclusive-OR of the signs (which determines later
; whether we do a magnitude addition or subtraction), RNDexp equal to the
; first operand exponent and Rarith equal to the exponent difference.

        ExpDiff Rtmp,Rarith,OP1sue,OP2sue       ;Get difference and op1 exp.
        EOR     R14,OP1sue,OP2sue               ;Make EOR of signs
        AND     OP1sue,OP1sue,#Sign_bit         ;Isolate prospective result sign
        MOV     RNDexp,Rarith,LSR #32-EIExp_len ;Right-align operand 1 exponent
        BHI     AddSub_Op2Shift
        MOVEQ   Rtmp2,Rtmp                      ;If EQ, Rtmp = Rtmp2 = 0
        BEQ     AddSub_ShiftDone                ; = correct guard/round/sticky

AddSub_Op1Shift

; Operand 1 needs shifting, and so operand 2's exponent is used for the
; result. Rarith currently contains exp1-exp2 = -(shift amount),
; left-aligned.

        RSB     Rarith,Rtmp,#0          ;Get shift amount = exp2 - exp1
        MOV     Rarith,Rarith,LSR #32-EIExp_len ;Right-align exponent difference
        ADD     RNDexp,RNDexp,Rarith    ;Resurrect operand 2 exponent

; Now denormalise (OP1mhi,OP1mlo) with a shift amount of Rarith, putting
; op1 guard/round/sticky bits into Rtmp, op2 guard/round/sticky bits into
; Rtmp2.

        Denorm  OP1mhi,OP1mlo,Rtmp,Rarith,Rtmp2,Rarith
        MOV     Rtmp2,#0                ;Operand 2 guard/round/sticky
        B       AddSub_ShiftDone

AddSub_Op2Shift

; Operand 2 needs shifting, and so we've already selected the correct result
; exponent. Furthermore, Rtmp currently contains exp1-exp2 = shift amount,
; left-aligned. So denormalise (OP2mhi,OP2mlo) with a shift amount of Rtmp,
; putting op1 guard/round/sticky bits into Rtmp, op2 guard/round/sticky bits
; into Rtmp2.

        MOV     Rarith,Rtmp,LSR #32-EIExp_len   ;Right-align exponent difference
        Denorm  OP2mhi,OP2mlo,Rtmp2,Rarith,Rtmp,Rarith
        MOV     Rtmp,#0                 ;Operand 1 guard/round/sticky

AddSub_ShiftDone

; We now have:
;   OP1sue:        Prospective result sign (= operand 1 sign);
;   OP1mhi/OP1mlo: Operand 1 mantissa, possibly shifted;
;   RNDexp:        Prospective result exponent (= MAX(operand exponents));
;   OP2mhi/OP2mlo: Operand 2 mantissa, possibly shifted;
;   Rarith:        Free;
;   Rfpsr:         FPSR;
;   Rtmp:          Operand 1 guard, round and sticky bits;
;   Rins:          Instruction;
;   Rtmp2:         Operand 2 guard, round and sticky bits;
;   Rwp,Rfp,Rsp:   Standard values;
;   R14:           Sign bit indicates magnitude subtraction/NOT addition;
; Now we need to split according to whether we need to do a magnitude
; addition or a magnitude subtraction.

        TST     R14,#Sign_bit
        BNE     AddSub_MagSub

AddSub_MagAdd

; Perform the magnitude addition. Note first that we have no need for a
; guard bit in this case, so we are going to regard the guard/round/sticky
; bits in Rtmp[31/30/29:0] and Rtmp2[31/30/29:0] as simply being
; round/sticky bits in Rtmp[31/30:0] and Rtmp2[31/30:0]. Secondly, note that
; since we know that at least one of Rtmp and Rtmp2 is zero, we can simply
; add these round/sticky bit representations to get the result round/sticky
; representation.

        ADDS    Rarith,Rtmp,Rtmp2       ;Will not in fact generate C=1
        ADCS    OP1mlo,OP1mlo,OP2mlo
        ADCS    OP1mhi,OP1mhi,OP2mhi

; If C=0, we're done. Otherwise, we've got to adjust the exponent, mantissa,
; round and sticky bits.

  IF Interworking :LOR: Thumbing
        LDMCCFD Rsp!,{LR}
        BXCC    LR
  ELSE
        LDMCCFD Rsp!,{PC}
  ENDIF
        ADD     RNDexp,RNDexp,#1
        MOVS    OP1mhi,OP1mhi,RRX
        MOVS    OP1mlo,OP1mlo,RRX
        ORR     Rarith,Rarith,Rarith,LSL #1     ;Sticky receives all of old
        MOV     Rarith,Rarith,RRX               ; round/sticky; round is new
  IF Interworking :LOR: Thumbing
        LDMFD   Rsp!,{LR}
        BX      LR
  ELSE
        LDMFD   Rsp!,{PC}
  ENDIF


AddSub_MagSub

; We need to do a magnitude subtraction of OP2mhi/OP2mlo/Rtmp2 from
; OP1mhi/OP1mlo/Rtmp. The prospective result exponent in RNDexp has been
; made right already, but if the subtraction comes out negative, we will
; have to change the sign of the result. Note we can subtract the
; guard/round/sticky representations in Rtmp and Rtmp2, because we know one
; of them is entirely zero.

        SUBS    Rarith,Rtmp,Rtmp2
        SBCS    OP1mlo,OP1mlo,OP2mlo
        SBCS    OP1mhi,OP1mhi,OP2mhi

; If the subtraction (which was of unsigned numbers) came out negative, we
; need to reverse the sign of the result and 2's complement the mantissa -
; again including the guard/round/sticky part.

        BCS     AddSub_MagSub_Normalise
        EOR     OP1sue,OP1sue,#Sign_bit
        RSBS    Rarith,Rarith,#0
        RSCS    OP1mlo,OP1mlo,#0
        RSC     OP1mhi,OP1mhi,#0

AddSub_MagSub_Normalise

; Now we need to normalise the result. This is slightly tricky, because in
; the case of subtracting the largest possible number with one exponent from
; the smallest number of the next exponent (e.g. 1-(1-2^(-64))), the leading
; bit of the result is actually the round bit. We can divide into two cases:
;
;   (a) The exponent difference was 0 or 1: in this case, the number may be
;       normalised by up to 64 bits, but the current round and sticky bits
;       are guaranteed to be 0 - this ensures that the eventual sticky bit
;       is guaranteed to be zero, and that the round bit is also zero if a
;       non-zero normalisation shift is required;
;
;   (b) The exponent difference was 2 or more: in this case, the number can
;       be normalised by at most one bit, but the eventual sticky bit may be
;       non-zero.
;
; So we will first try to normalise by 1 bit, bringing the guard bit into the
; mantissa if necessary.

        TST     OP1mhi,#EIUnits_bit     ;Already normalised?
  IF Interworking :LOR: Thumbing
        LDMNEFD Rsp!,{LR}               ;Return if so
        BXNE    LR
  ELSE
        LDMNEFD Rsp!,{PC}               ;Return if so
  ENDIF
        ADDS    Rarith,Rarith,Rarith    ;Shift mhi/mlo/guard/round/sticky
        ADCS    OP1mlo,OP1mlo,OP1mlo    ; left by one bit to form new
        ADC     OP1mhi,OP1mhi,OP1mhi    ; mhi/mlo/round/sticky
        SUB     RNDexp,RNDexp,#1

; If the result is normalised now, we're done. Otherwise, we know that a
; normalisation shift of 1-63 is still required, that the exponent
; difference was 0 or 1, and thus that the new round and sticky bits are
; both zero.
;   However, at this point, we need to look out for the case of a magnitude
; subtraction of two equal numbers - for which we need to apply the special
; IEEE sign rule (i.e. -0 if rounding to -infinity, otherwise +0).

        TST     OP1mhi,#EIUnits_bit     ;Normalised now?
  IF Interworking :LOR: Thumbing
        LDMNEFD Rsp!,{LR}               ;Return if so
        BXNE    LR
  ELSE
        LDMNEFD Rsp!,{PC}               ;Return if so
  ENDIF

        ORRS    LR,OP1mhi,OP1mlo        ;Is result zero?
        BLNE    $NormaliseOp1_str       ;If not, complete normalisation
  IF Interworking :LOR: Thumbing
        LDMNEFD Rsp!,{LR}               ; and return (note NormaliseOp1
        BXNE    LR
  ELSE
        LDMNEFD Rsp!,{PC}               ; and return (note NormaliseOp1
  ENDIF


; We know the result is a zero, with sign determined by the rounding mode.
; Everything except the sign and exponent has been correctly set already,
; so we test the rounding mode, set the sign and exponent, and return.

        [ :DEF: addsub_s
          MOV   dOPh, #0
          MOV   dOPl, #0
          ASSERT dOPh = fOP :LOR: dOPl = fOP
 ;         ADD   sp,sp,#4        ; Pop link register off the stack
 ;         VReturn
  IF Interworking :LOR: Thumbing
          LDMFD   Rsp!,{LR}
          BX      LR
  ELSE
          LDMFD Rsp!,{PC}
  ENDIF

        |
          AND   Rtmp,Rins,#RM_mask
          TEQ   Rtmp,#RM_MinusInf
          MOVEQ OP1sue,#Sign_bit
          MOVNE OP1sue,#0
          MOV   RNDexp,#0

  IF Interworking :LOR: Thumbing
          LDMFD Rsp!,{LR}
          BX      LR
  ELSE
          LDMFD Rsp!,{PC}
  ENDIF

 
        ]

        ]                               ; Conditional assembly of AddSub

;===========================================================================

        [ :DEF: mul_s :LOR: FPEWanted :LOR: FPASCWanted

; Routine to multiply or fast-multiply two internal format floating point
; numbers. It has two entry points: "MultFPE", which has an optimised fast
; track for both operands being common, and "MultFPASC", which avoids the
; test for this optimised fast track - since it should never happen. The
; second entry point lies a long way down in the source to avoid addressing
; constraints.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard dyadic operation entry and exit conventions - see top of
; this file.

        ASSERT  RNDexp = OP2sue ;We swap over from the use of OP2sue to that
                                ; of RNDexp partway through this routine.

        [ FPEWanted

MultFPE

        CDebug3 3,"MultFPE: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 3,"         op2 =",OP2sue,OP2mhi,OP2mlo

; Start by detecting the "fast track" case of both operands being common.

        TST     OP1sue,#Uncommon_bit
        TSTEQ   OP2sue,#Uncommon_bit
        BNE     Mult_Uncommon

; If either operand is a zero, the product is a zero. Because the numbers
; are common and assumed not to be unnormalised URD results, we can check
; for zeros by means of the units bits.

        ANDS    Rtmp,OP1mhi,OP2mhi
        ASSERT  EIUnits_pos = 31
        BPL     Mult_Zero

; Both operands may now be assumed to be normalised numbers. Produce the
; result sign and the prospective result exponent.

        ]

        [ :DEF: mul_s :LOR: FPEWanted

        [ FPLibWanted
__fp_mult_common
        ]

        AND     Rtmp,OP1sue,#ToExp_mask
        AND     Rtmp2,OP2sue,#ToExp_mask
        EOR     OP1sue,OP1sue,OP2sue    ;Produce result sign
        AND     OP1sue,OP1sue,#Sign_bit
        ADD     RNDexp,Rtmp,Rtmp2
        SUB     RNDexp,RNDexp,#(EIExp_bias-1):AND:&FF00
        SUB     RNDexp,RNDexp,#(EIExp_bias-1):AND:&FF
        ASSERT  (EIExp_bias-1) < &10000 ;Result exponent if mantissa
                                        ; overflow is exp1+exp2-bias+1

        ]

; This subsidiary entry point deals with multiplying two normalised
; mantissas together and adjusting the exponent if necessary.
; Entry: OP1sue = the result's sign, with an uncommon bit of 0 - the
;          remaining bits are zero;
;        OP1mhi = First operand mantissa, high word;
;        OP1mlo = First operand mantissa, low word;
;        RNDexp = Prospective result exponent, which may be negative; this
;          needs to be decremented if mantissa overflow doesn't occur;
;        OP2mhi = Second operand mantissa, high word;
;        OP2mlo = Second operand mantissa, low word;
;        Rins   = instruction (may be needed to discriminate between MUF and
;          FML);
;        Rwp, Rfp, Rsp hold their usual values;
;        R14    = return link.
; Exit:  OP1sue = the result's sign, with an uncommon bit of 0; the
;          remaining bits are zero;
;        OP1mhi, OP1mlo = the result's mantissa;
;        RNDexp = the result exponent, which may be negative;
;        Rarith holds the round bit (in bit 31) and the sticky bit (in bits
;          30:0) if the destination precision is extended; if the
;          destination precision is single or double, it holds part of the
;          sticky bit (the remainder of which is held in bits below the
;          round bit in OP1mhi and OP1mlo);
;        OP2mhi, OP2mlo, Rtmp, Rtmp2 and R14 may be corrupt;
;        All other registers preserved.

Mult_Mantissas

; We will split into various lines, depending on the operands:
;
;   if ((OP1mlo = 0) AND (OP2mlo = 0))
;     do 32x32->64 multiplication of OP1mhi by OP2mhi;
;   if ((OP1mlo = 0) AND (OP2mlo != 0))
;     do 32x64->96 multiplication of OP1mhi by (OP2mhi,OP2mlo);
;   if ((OP1mlo != 0) AND (OP2mlo = 0))
;     do 64x32->96 multiplication of (OP1mhi,OP1mlo) by OP2mhi;
;   if ((OP1mlo != 0) AND (OP2mlo != 0))
;     do 64x32->128 multiplication of (OP1mhi,OP1mlo) by (OP2mhi,OP2mlo);
;
; In each case, this is then followed by code to deal with the case of no
; mantissa overflow (i.e. the top bit of the product was zero) and to create
; the round and sticky bits.
;
; This is all designed to make multiplications involving single precision
; numbers, immediate constants and/or FLTed integers as efficient as
; possible.
;
; If the instruction is an FML, we simply assume that both mantissa low
; words are zero.

        [ FPEWanted

        TST     Rins,#Fast_bit
        BNE     Mult_32x32

        ]

        TEQ     OP1mlo,#0
        BEQ     Mult_32xX

Mult_64xX

        TEQ     OP2mlo,#0
        BEQ     Mult_64x32

Mult_64x64

        STMFD   Rsp!,{OP1sue,Rfpsr,Rins,LR}

; We do this multiplication by applying the trick (described in Knuth
; section 4.3.3) for reducing the obvious algorithm involving four 32x32
; multiplications to just three plus some additions and sign manipulations,
; by means of the formula:
;
;   (a1*2^32 + a0) * (b1*2^32 + b0)
;     = a1*b1*(2^64+2^32) + (a1-a0)*(b0-b1)*2^32 + a0*b0*(2^32+1)
;
; This has to be done carefully: the a1*b1 and a0*b0 multiplications are
; straightforward 32x32 multiplications, but each of a1-a0 and b0-b1 is in
; the range -2^32+1 < x < 2^32-1. To see what effect this has, we need to
; look at what we will get if we simply do the a1-a0 and b0-b1 subtractions,
; then multiply the results as unsigned numbers:
;
; (A) If a1-a0 >= 0, b0-b1 >= 0:
;       product obtained = (a1-a0)*(b0-b1)
;
; (B) If a1-a0 >= 0, b0-b1 < 0:
;       product obtained = (a1-a0)*(b0-b1+2^32)
;                        = (a1-a0)*(b0-b1) + (a1-a0)*2^32
;
; (C) If a1-a0 < 0, b0-b1 >= 0:
;       product obtained = (a1-a0+2^32)*(b0-b1)
;                        = (a1-a0)*(b0-b1) + (b0-b1)*2^32
;
; (D) If a1-a0 < 0, b0-b1 < 0:
;       product obtained = (a1-a0+2^32)*(b0-b1+2^32)
;                        = (a1-a0)*(b0-b1) + ((a1-a0)+(b0-b1))*2^32 + 2^64
;                        = (a1-a0)*(b0-b1)
;                            + ((a1-a0+2^32) + (b0-b1+2^32))*2^32 - 2^64
;
; So to get the real value of (a1-a0)*(b0-b1), we must look at the signs of
; a1-a0 and b0-b1: if a1-a0 is in fact negative, we must subtract the
; calculated value of b0-b1 from the high word of the calculated product; if
; b0-b1 is in fact negative, we must subtract the calculated value of a1-a0
; from the high word of the calculated product; and finally we must add 2^64
; if both were negative.
;
; This last step is awkward. However, note that (a1-a0)*(b0-b1) is actually
; guaranteed to lie in the range -2^64 < x < 2^64, which means that it is
; sufficient to calculate its value modulo 2^64 (i.e. disregarding carries
; out of the high word and the possible addition of 2^64), provided we take
; care to get the sign word right.
;
; We do the 32x32 multiplications by means of standard macros. First
; multiply a1*b1 = OP1mhi*OP2mhi into (OP1sue,Rfpsr).

        Split16 OP1sue,Rfpsr,OP1mhi
        Mul64   OP1sue,Rfpsr,OP1sue,Rfpsr,OP2mhi,,,Rarith,Rtmp,Rtmp2

; Multiply a0*b0 = OP1mlo*OP2mlo into (Rins,R14).

        Split16 Rins,R14,OP1mlo
        Mul64   Rins,R14,Rins,R14,OP2mlo,,,Rarith,Rtmp,Rtmp2

; Next, we need to calculate a1*b1*(2^64+2^32) + a0*b0*(2^32+1)
;
;   = (2^32+1) * (a1*b1*2^32 + a0*b0)
;
; Note that a1*b1*2^32 + a0*b0 <= (2^32-1)*(2^32-1)*(2^32+1)
; = (2^32-1)*(2^64-1) < 2^96 and that (2^32+1) * (a1*b1*2^32 + a0*b0)
; <= (2^32+1)*(2^32-1)*(2^32-1)*(2^32+1) = (2^64-1)^2 < 2^128, so the
; calculations can be done respectively in 3- and 4-word unsigned
; arithmetic.

        ADDS    Rfpsr,Rfpsr,Rins        ;Put a1*b1*2^32 + a0*b0 into
        ADC     OP1sue,OP1sue,#0        ; (OP1sue,Rfpsr,R14)
        ADDS    Rins,Rfpsr,R14          ;Then multiply by 2^32+1, putting
        ADCS    Rfpsr,Rfpsr,OP1sue      ; result in (OP1sue,Rfpsr,Rins,R14)
        ADC     OP1sue,OP1sue,#0

; Calculate a1-a0 = OP1mhi-OP1mlo into Rtmp,
;           b0-b1 = OP2mlo-OP2mhi into Rtmp2,
;           addend to high word of calculated (a1-a0)*(b0-b1) product into
;             Rarith, and
;           correct sign of (a1-a0)*(b0-b1) product into OP1mhi.
; The sign word is 0 for a positive or zero result, &FFFFFFFF for a negative
; result - i.e. it is the word which, when prefixed to the 64-bit product
; calculated otherwise, gives us the true result as a 96-bit signed number.
;   Getting this right is slightly tricky, because of the possibilities of
; a1-a0 and b0-b1 being zero and thus invalidating the usual EOR rule about
; the sign. The key to the code below is that if Rtmp = a1-a0 comes out as
; 0, OP1mhi and OP1mlo come out as zero and Rtmp2 never gets set - but this
; last doesn't matter, since zero times anything is zero!
;   Note also that we don't care about carries out of the addend, since they
; go into the sign word, which we are getting right by other means.

        SUBS    Rtmp,OP1mhi,OP1mlo              ;Rtmp := a1-a0
        MOV     OP1mhi,#0                       ;Sign if a1-a0,b0-b1 both +ve
        MOV     Rarith,#0                       ;Addend if both +ve
        MVNLO   OP1mhi,OP1mhi                   ;If a1-a0 -ve, adjust sign and
        SUBLO   Rarith,OP2mhi,OP2mlo            ; addend = -(b0-b1) = b1-b0
        SUBNES  Rtmp2,OP2mlo,OP2mhi             ;Rtmp2 := b0-b1
        MOVEQ   OP1mhi,#0                       ;Override sign if b0-b1 = 0
        MVNLO   OP1mhi,OP1mhi                   ;If b0-b1 -ve, adjust sign and
        SUBLO   Rarith,Rarith,Rtmp              ; addend += -(a1-a0)

; Finish calculating the real value of (a1-a0)*(b0-b1) into
; (OP1mhi,OP1mlo,Rarith). I.e. multiply Rtmp by Rtmp2, adding OP1mlo into the
; high word and putting the result in (OP1mlo,Rarith). OP1mhi is already OK.

        Split16 OP2mhi,OP2mlo,Rtmp
        Mul64   OP1mlo,Rarith,OP2mhi,OP2mlo,Rtmp2,Rarith,,Rtmp,Rtmp2,OP1mlo

; Now add a1*b1*(2^64+2^32) + a0*b0*(2^32+1) and (a1-a0)*(b0-b1)*2^32
; together, putting the result in (OP1mhi,OP1mlo,Rarith,R14). Note the low
; word is in R14 already.

        ADDS    Rarith,Rins,Rarith
        ADCS    OP1mlo,Rfpsr,OP1mlo
        ADCS    OP1mhi,OP1sue,OP1mhi

; Transfer R14 into the sticky bit, without affecting flags. Also make
; certain we don't affect the guard or round bits.

        ORR     R14,R14,R14,LSL #2
        ORR     Rarith,Rarith,R14,LSR #2

; If result is normalised, return. Otherwise normalise by shifting left one
; bit.

  IF Interworking :LOR: Thumbing
        LDMMIFD Rsp!,{OP1sue,Rfpsr,Rins,LR}
        BXMI    LR
  ELSE
        LDMMIFD Rsp!,{OP1sue,Rfpsr,Rins,PC}
  ENDIF

        ADDS    Rarith,Rarith,Rarith
        ADCS    OP1mlo,OP1mlo,OP1mlo
        ADC     OP1mhi,OP1mhi,OP1mhi
        SUB     RNDexp,RNDexp,#1
  IF Interworking :LOR: Thumbing
        LDMFD   Rsp!,{OP1sue,Rfpsr,Rins,LR}
        BX      LR
  ELSE
        LDMFD   Rsp!,{OP1sue,Rfpsr,Rins,PC}
  ENDIF


Mult_64x32

; To perform this multiplication, we do two 32x32 multiplications, then add
; the results together. We use the standard macros for the purpose.

        Split16 OP2mlo,Rarith,OP2mhi
        Mul64   OP2mhi,OP1mhi,OP2mlo,Rarith,OP1mhi,,,Rtmp,Rtmp2,OP2mhi
        Mul64   OP2mlo,Rarith,OP2mlo,Rarith,OP1mlo,,,Rtmp,Rtmp2,OP1mlo
        ADDS    OP1mlo,OP2mlo,OP1mhi
        ADCS    OP1mhi,OP2mhi,#0

; If the top bit was clear, we need to shift the product, round and sticky
; bits left by one bit and decrement the exponent. Otherwise, everything is
; ready for the return.

  IF Interworking :LOR: Thumbing
        BXMI    LR
  ELSE
        MOVMI   PC,LR
  ENDIF

        ADDS    Rarith,Rarith,Rarith
        ADCS    OP1mlo,OP1mlo,OP1mlo
        ADC     OP1mhi,OP1mhi,OP1mhi
        SUB     RNDexp,RNDexp,#1
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF


Mult_32xX

        TEQ     OP2mlo,#0
        BEQ     Mult_32x32

Mult_32x64

; To perform this multiplication, we do two 32x32 multiplications, then add
; the results together. We use the standard macros for the purpose.

        Split16 OP1mlo,Rarith,OP1mhi
        Mul64   OP1mhi,OP2mhi,OP1mlo,Rarith,OP2mhi,,,Rtmp,Rtmp2,OP1mhi
        Mul64   OP1mlo,Rarith,OP1mlo,Rarith,OP2mlo,,,Rtmp,Rtmp2,OP2mlo
        ADDS    OP1mlo,OP1mlo,OP2mhi
        ADCS    OP1mhi,OP1mhi,#0

; If the top bit was clear, we need to shift the product, round and sticky
; bits left by one bit and decrement the exponent. Otherwise, everything is
; ready for the return.

  IF Interworking :LOR: Thumbing
        BXMI    LR
  ELSE
        MOVMI   PC,LR
  ENDIF

        ADDS    Rarith,Rarith,Rarith
        ADCS    OP1mlo,OP1mlo,OP1mlo
        ADC     OP1mhi,OP1mhi,OP1mhi
        SUB     RNDexp,RNDexp,#1
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        [ FPLibWanted
        KEEP    |$F__fp_mult_fast_common|
|$F__fp_mult_fast_common|
__fp_mult_fast_common
; This code duplicated from about for the fast case.
        AND     Rtmp,OP1sue,#ToExp_mask
        AND     Rtmp2,OP2sue,#ToExp_mask
        EOR     OP1sue,OP1sue,OP2sue    ;Produce result sign
        AND     OP1sue,OP1sue,#Sign_bit
        ADD     RNDexp,Rtmp,Rtmp2
        SUB     RNDexp,RNDexp,#(EIExp_bias-1):AND:&FF00
        SUB     RNDexp,RNDexp,#(EIExp_bias-1):AND:&FF
        ASSERT  (EIExp_bias-1) < &10000 ;Result exponent if mantissa
                                        ; overflow is exp1+exp2-bias+1

        ]

Mult_32x32

; Only the high words of the operand mantissas need to be multiplied
; together. Use the standard macros for this purpose.

        Split16 OP2mlo,Rarith,OP2mhi
        Mul64   OP1mhi,OP1mlo,OP2mlo,Rarith,OP1mhi,,S,Rtmp,Rtmp2,OP1mhi

; The round and sticky bits are always going to be zero.

        MOV     Rarith,#0

; If the top bit was clear, we need to shift the product left one bit and
; decrement the exponent. Otherwise we're done.

  IF Interworking :LOR: Thumbing
        BXMI    LR
  ELSE
        MOVMI   PC,LR
  ENDIF

        ADDS    OP1mlo,OP1mlo,OP1mlo
        ADC     OP1mhi,OP1mhi,OP1mhi
        SUB     RNDexp,RNDexp,#1

  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]                               ; Conditional compilation of Mult

;===========================================================================

        [ :DEF: div_s :LOR: FPEWanted :LOR: FPASCWanted

; Routine to divide, reverse-divide, fast-divide or fast-reverse-divide two
; internal format floating point numbers. It has two entry points: "DivFPE",
; which has an optimised fast track for both operands being common, and
; "DivFPASC", which avoids the test for this optimised fast track - since it
; should rarely happen. The second entry point lies a long way down in the
; source to avoid addressing constraints.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard dyadic operation entry and exit conventions - see top of
; this file.

        ASSERT  RNDexp = OP2sue ;We swap over from the use of OP2sue to that
                                ; of RNDexp partway through this routine.

        [ FPEWanted

DivFPE

        CDebug3 3,"DivFPE: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 3,"        op2 =",OP2sue,OP2mhi,OP2mlo

; Start by detecting the "fast track" case of both operands being common.

        TST     OP1sue,#Uncommon_bit
        TSTEQ   OP2sue,#Uncommon_bit
        BNE     Div_Uncommon

; If either operand is a zero, we need to take special action. Because the
; numbers are common and assumed not to be unnormalised URD results, we can
; check for zeros by means of the units bits.

        ANDS    Rtmp,OP1mhi,OP2mhi
        ASSERT  EIUnits_pos = 31
        BPL     Div_Zero

; Both operands may now be assumed to be normalised numbers. We now know
; that we are not going to need to know the operands for trap purposes, so
; we can swap them if this is a normal division rather than a reverse
; division.

        TST     Rins,#RevDiv_bit
        BNE     Div_Common_Swapped

        ]

        [ FPLibWanted
__fp_div_common
        ]

        MOV     Rtmp,OP1sue
        MOV     OP1sue,OP2sue
        MOV     OP2sue,Rtmp
        MOV     Rtmp,OP1mhi
        MOV     OP1mhi,OP2mhi
        MOV     OP2mhi,Rtmp
        MOV     Rtmp,OP1mlo
        MOV     OP1mlo,OP2mlo
        MOV     OP2mlo,Rtmp

        [ FPLibWanted
        KEEP    |$F__fp_rdv_common|
|$F__fp_rdv_common|
__fp_rdv_common
        ]

Div_Common_Swapped

; Produce the result sign and the prospective result exponent.

        AND     Rtmp,OP1sue,#ToExp_mask
        AND     Rtmp2,OP2sue,#ToExp_mask
        EOR     OP1sue,OP1sue,OP2sue    ;Produce result sign
        AND     OP1sue,OP1sue,#Sign_bit
        SUB     RNDexp,Rtmp2,Rtmp
        ADD     RNDexp,RNDexp,#EIExp_bias:AND:&FF00
        ADD     RNDexp,RNDexp,#EIExp_bias:AND:&FF
        ASSERT  EIExp_bias < &10000     ;Result exponent if no mantissa
                                        ; underflow is exp1-exp2+bias

; This subsidiary entry point deals with dividing a normalised mantissa by
; another and adjusting the exponent if necessary.
; Entry: OP1sue = the result's sign, with an uncommon bit of 0 - the
;          remaining bits are zero;
;        OP1mhi = Divisor mantissa, high word;
;        OP1mlo = Divisor mantissa, low word;
;        RNDexp = Prospective result exponent, which may be negative; this
;          needs to be decremented if mantissa underflow occurs;
;        OP2mhi = Dividend mantissa, high word;
;        OP2mlo = Dividend mantissa, low word;
;        Rins   = instruction (needed to determine precision; may be needed
;          to discriminate between normal and fast divisions);
;        Rwp, Rfp, Rsp hold their usual values;
;        R14    = return link.
; Exit:  OP1sue = the result's sign, with an uncommon bit of 0; the
;          remaining bits are zero;
;        OP1mhi, OP1mlo = the result's mantissa;
;        RNDexp = the result exponent, which may be negative;
;        Rarith holds the round bit (in bit 31) and the sticky bit (in bits
;          30:0) if the destination precision is extended; if the
;          destination precision is single or double, it holds part of the
;          sticky bit (the remainder of which is held in bits below the
;          round bit in OP1mhi and OP1mlo);
;        OP2mhi, OP2mlo, Rtmp, Rtmp2 and R14 may be corrupt;
;        All other registers preserved.

Div_Mantissas

        STMFD   Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,LR}

        CDebug2 4,"Div_Mantissas: dividend =",OP2mhi,OP2mlo
        CDebug2 4,"               divisor  =",OP1mhi,OP1mlo
        CDebug1 4,"               exponent =",RNDexp

; We will do the mantissa division by an algorithm which is a hybrid between
; Newton-Raphson approximation and ordinary long division: this results in
; division being done to IEEE accuracy, yet more than 50% faster than the
; straightforward long division technique. A summary of the algorithm is:
;
;   (a) Use table look-up to get an initial approximation to the reciprocal
;       of the divisor;
;
;   (b) Use two iterations of Newton-Raphson to improve the reciprocal
;       approximation to one with about 15 bits accuracy;
;
;   (c) Do long division base 2^13, using the reciprocal approximation to
;       determine the result "digits" - which are in fact fixed point
;       numbers with 13 bits before the binary point and 3 after it;
;
;   (d) Resolve the exact values of the last three bits by ordinary long
;       division;
;
;   (e) Adjust the exponent and shift the mantissa if mantissa underflow
;       occurs, and create the sticky bit.
;
; Exact details of the algorithm appear in comments next to the relevant
; parts of the code below.
;
; The long division is performed for 2 steps for single precision, 4 steps
; for double precision and 5 steps for extended precision, producing 2*13+3
; = 29, 4*13+3 = 55 and 5*13+3 = 68 bits respectively, plus a sticky bit in
; each case.
;
; Note that this algorithm has been specifically tailored to the software
; environment - e.g. the availability of 32x32->32 bit multiplication and
; the fact that negative partial remainders during the long division will
; cause problems. This leads to some apparently strange bits of code below -
; e.g. getting less accuracy from a Newton-Raphson iteration than might
; appear to be available, in order to preserve knowledge of the sign of the
; error.
;
; In what follows, we will refer to the true mathematical value of the
; dividend mantissa as P, that of the divisor as D, that of the reciprocal
; of the divisor as R and that of the quotient as Q. So Q = P/D = P*R are
; exact mathematical relationships. Also, we have P = (2^32*OP1mhi +
; OP1mlo)*2^(-63), D = (2^32*OP2mhi + OP2mlo)*2^(-63).

; First step: initialise by breaking the divisor up into 16-bit chunks,
; held in (OP1sue,Rfpsr,Rins,R14).

        Split16 OP1sue,Rfpsr,OP1mhi
        Split16 Rins,R14,OP1mlo

; Second step: use table look-up to get an approximation to R. Specifically,
; we load Rarith with an 8-bit value such that we know:
;
;   R <= Rarith*2^(-7) < R + 2^(-6)

        [ CoreDebugging = 0
          ADR     Rarith,Recip_Table-128        ;-128 to cancel units bit
        |
          ADRL    Rarith,Recip_Table-128        ;-128 to cancel units bit
        ]
        LDRB    Rarith,[Rarith,OP1sue,LSR #8]

        CDebug1 5,"Table look-up approx'n is",Rarith

; Third step: use a Newton-Raphson iteration to improve this to an 11-bit
; value in Rarith such that:
;
;   R < Rarith*2^(-10) < R + 2^(-9)
;
; Details: Let W be the current value of Rarith, so we have:
;
;   R <= W*2^(-7) < R + 2^(-6)
;
; Let X be the first 16 bits of D (i.e. OP1sue), incremented by 1. This has
; the property that:
;
;   D < X*2^(-15) <= D + 2^(-15)
;
; Suppose further that W*2^(-7) = R+e, with 0 <= e < 2^(-6), and X*2^(-15) =
; D+f, with 0 < f <= 2^(-15).
;
; Now let Y = W * (2^23 - X*W), which is a calculation that can be performed
; without overflowing a word. This is equivalent to:
;
;   Y*2^(-29) = W*2^(-7) * (2 - X*2^(-15) * W*2^(-7))
;
;             = (R+e) * (2 - (D+f)*(R+e))
;
;             = (R+e) * (2 - (1 + D*e + R*f + e*f)), since D*R=1 exactly,
;
;             = (R+e) * (1 - D*e - R*f - e*f)
;
;             = R + e - e - D*e*e - R*R*f - R*e*f - R*e*f - e*e*f, since D*R=1,
;
;             = R - D*e*e - R*R*f - 2*R*e*f - e*e*f
;
; Since R > 0, D > 0, e >= 0 and f > 0, this is clearly less than R. On the
; other hand, we know that R <= 1, D < 2, e < 2^(-6) and f <= 2^(-15). So:
;
;   R > Y*2^(-29)
;     > R - 2^(-11) - 2^(-15) - 2^(-20) - 2^(-27)
;
; Now let Z be Y shifted right 19 bits. This gives us:
;
;   Y*2^(-29) - 2^(-10) < Z*2^(-10) <= Y*2^(-29)
;
; Combining the inequalities, we get:
;
;   R - 2^(-9) < R - 2^(-11) - 2^(-15) - 2^(-20) - 2^(-27) - 2^(-10)
;              < Y*2^(-29) - 2^(-10)
;              < Z*2^(-10)
;              <= Y*2^(-29)
;              < R
;
; So if we put Rarith = Z+2, we get:
;
;   R < Rarith*2^(-10) < R + 2^(-9),
;
; as desired.

        MLA     Rtmp,OP1sue,Rarith,Rarith       ;Rtmp := (X-1)*W + W = X*W
        RSB     Rtmp,Rtmp,#1:SHL:23             ;Rtmp := 2^23 - X*W
        MUL     Rarith,Rtmp,Rarith              ;Rarith := W*(2^23 - X*W) = Y
        MOV     Rarith,Rarith,LSR #19           ;Shift right 19 bits and add
        ADD     Rarith,Rarith,#2                ; 2 to get new approximation

        CDebug1 5,"First N-R approx'n is",Rarith

; Fourth step: use a Newton-Raphson iteration to improve this to a 16-bit
; value in Rarith such that:
;
;   R - 2^(-15) < Rarith*2^(-16) < R
;
; Details: Let W be the current value of Rarith, so we have:
;
;   R < W*2^(-10) < R + 2^(-9)
;
; Let X be the first 19 bits of D (i.e. the top 19 bits of OP1mhi),
; incremented by 1. This has the property that:
;
;   D < X*2^(-18) <= D + 2^(-18)
;
; Suppose further that W*2^(-10) = R+e, with 0 < e < 2^(-9), and X*2^(-18)
; = D+f, with 0 < f <= 2^(-18).
;
; Now let Y = W * (2^29 - X*W): part of this calculation will require 2-word
; arithmetic. This is equivalent to:
;
;   Y*2^(-38) = W*2^(-10) * (2 - X*2^(-18) * W*2^(-10))
;
;             = (R+e) * (2 - (D+f)*(R+e))
;
;             = R - D*e*e - R*R*f - 2*R*e*f - e*e*f, as in the third step.
;
; Since R > 0, D > 0, e >= 0 and f > 0, this is clearly less than R. On the
; other hand, we know that R <= 1, D < 2, e < 2^(-9) and f <= 2^(-18). So:
;
;   R > Y*2^(-38)
;     > R - 2^(-17) - 2^(-18) - 2^(-26) - 2^(-36)
;
; Now let Z be Y shifted right 22 bits. This gives us:
;
;   Y*2^(-38) - 2^(-16) < Z*2^(-16) <= Y*2^(-38)
;
; Combining the inequalities, we get:
;
;   R - 2^(-15) < R - 2^(-17) - 2^(-18) - 2^(-26) - 2^(-36) - 2^(-16)
;               < Y*2^(-38) - 2^(-16)
;               < Z*2^(-16)
;               <= Y*2^(-38)
;               < R
;
; So if we put Rarith = Z, we get the desired inequality.

        MOV     Rtmp,OP1mhi,LSR #13             ;Rtmp := X-1
        MLA     Rtmp2,Rtmp,Rarith,Rarith        ;Rtmp2 := (X-1)*W + W = X*W
        RSB     Rtmp2,Rtmp2,#1:SHL:29           ;Rtmp2 := 2^29 - X*W
        Split16 Rtmp,Rtmp2,Rtmp2                ;Rtmp/Rtmp2 := top/bottom half
        MUL     OP1mlo,Rtmp2,Rarith             ;OP1mhi, OP1mlo := two
        MUL     OP1mhi,Rtmp,Rarith              ; parts of product with W
        ADD     Rarith,OP1mhi,OP1mlo,LSR #16    ;Rarith := Y >> 16
        MOV     Rarith,Rarith,LSR #6            ;Rarith := Y >> 22

        CDebug1 5,"Second N-R approx'n is",Rarith

; Fifth step: initialise the partial remainder - its binary point lies to
; the right of bit 30 of its top word to line up well with the results of
; later multiplications.

        MOVS    OP2mhi,OP2mhi,LSR #1
        MOVS    OP2mlo,OP2mlo,RRX
        MOVCC   OP2sue,#0
        MOVCS   OP2sue,#TopBit

; Sixth step: do the first iteration of the long division process. The
; register allocation during this is:
;
; OP1sue, Rfpsr, Rins, R14: Divisor, in 16-bit chunks; its binary point is
;                           considered to lie to the right of bit 15 of
;                           OP1sue;
; OP1mhi, OP1mlo:           Quotient so far (Rarith joins into this near the
;                           end of the calculation); its binary point is
;                           considered to lie to the right of bit 31 of
;                           OP1mhi;
; OP2mhi, OP2mlo, OP2sue:   Partial remainder; its binary point is
;                           considered to lie to the right of bit 30 of
;                           OP2mhi;
; Rarith:                   16-bit reciprocal approximation, until near the
;                           end of the calculation; its binary point lies to
;                           the *left* of bit 15;
; Rtmp, Rtmp2:              Temporaries.
;
; Some of these registers (OP1mhi and OP1mlo) only become set some way into
; the calculation: until they do become set, they should be regarded as
; being 0.
;
; The details of iteration N (for N=0 to 4) of the long division process
; are:
;
; Let D be the divisor represented by (OP1sue,Rfpsr,Rins,R14), and let R =
; 1/D be its reciprocal. Let A be the reciprocal approximation represented
; by Rarith from now until near the end of the calculation - i.e. A =
; Rarith*2^(-16). We know that:
;
;   1 <= D < 2;
;   0.5 < R <= 1;
;   R-2^(-15) < A < R
;
; Let Q[N] be the quotient represented by those of OP1mhi, OP1mlo and Rarith
; that have become set at the end of iteration N-1/start of iteration N -
; i.e.:
;
;   Q[0]      = 0;
;   Q[1],Q[2] = (OP1mhi at appropriate time) * 2^(-31);
;   Q[3],Q[4] = (OP1mhi at appropriate time) * 2^(-31)
;               + (OP1mlo at appropriate time) * 2^(-63);
;   Q[5]      = (OP1mhi at appropriate time) * 2^(-31)
;               + (OP1mlo at appropriate time) * 2^(-63)
;               + (Rarith at appropriate time) * 2^(-95);
;
; Let P[N] be the partial remainder represented by those of OP2mhi, OP2mlo
; and OP2sue that have become set at the end of iteration N-1/start of
; iteration N - i.e.:
;
;   P[i] = (OP2mhi at appropriate time) * 2^(-30)
;          + (OP2mlo at appropriate time) * 2^(-62)
;          + (OP2sue at appropriate time) * 2^(-94);
;
; Finally, let P be the original dividend - i.e. P is the current value of
; OP2mhi*2^(-31) + OP2mlo*2^(-63).
;
; For i=0, we can clearly make the following three statements:
;
;   (a) Q[i] is a multiple of 2^(-13*i-2);
;
;   (b) P[i] is a multiple of 2^(-65);
;
;   (c) P = Q[i]*D + P[i]*2^(-13*i);
;
;   (d) 0 < P[i] < 2;
;
; since Q[0] = 0 and P[0] = P. The algorithm will result in the same
; statements being true for i = 1, 2, 3, 4 and 5 as well.
;
; Iteration i of the algorithm is:
;
;   Papprox = P[i], rounded down to a multiple of 2^(-15);
;   digit   = Papprox * A, rounded down to a multiple of 2^(-15);
;   P[i+1]  = (P[i] - digit*D) * 2^13
;   Q[i+1]  = Q[i] + digit*2^(-13*i)
;
; Proof that the three statements above are true for all i: we will do this
; by induction. We already know that they are true for i=0. So suppose they
; are true for i=N. Then:
;
; (a) Q[i+1] = Q[i] + digit*2^(-13*i)
;            = (multiple of 2^(-13*i-2)) + (multiple of 2^(-15))*2^(-13*i)
;            = multiple of 2^(-13*i-15)
;            = multiple of 2^(-13*(i+1)-2).
;
; (b) P[i+1] = (P[i] - digit*D) * 2^13
;            = 2^13 * (multiple of 2^(-65)
;                      - (multiple of 2^(-15)) * (multiple of 2^(-63)))
;            = multiple of 2^(-65).
;
; (c) P = Q[i]*D + P[i]*2^(-13*i)
;       = (Q[i+1] - digit*2^(-13*i)) * D
;         + (P[i+1]*2^(-13) + digit*D) * 2^(-13*i)
;       = Q[i+1]*D + P[i+1]*2^(-13*i-13)
;       = Q[i+1]*D + P[i+1]*2^(-13*(i+1)).
;
; (d) First, since Papprox = P[i] rounded down to a multiple of 2^(-15) and
;     R-2^(-15) < A < R, we have Papprox = P[i]-e and A = R-f, where 0 <= e
;     < 2^(-15) and 0 < f < 2^(-15). Then, since digit = Papprox * A rounded
;     down to a multiple of 2^(-15), we have digit = Papprox * A - g, where
;     0 <= g < 2^(-15). Putting these together, we have:
;
;       digit = (P[i]-e)*(R-f) - g
;             = P[i]*R - P[i]*f - e*R + e*f - g
;
;     Since everything is non-negative, 'digit' is clearly at most P[i]*R.
;     Conversely, since P[i] < 2, R <= 1, e < 2^(-15), f < 2^(-15) and g <
;     2^(-15), we have:
;
;       P[i]*R > digit
;              > P[i]*R - 2*2^(-15) - 2^(-15)*1 - 2^(-15)
;              = P[i]*R - 2^(-13)
;
;     Or:
;
;       0 < P[i]*R - digit < 2^(-13)
;
;     Multiplying by D, which is known to satisfy 1 <= D < 2:
;
;       0 < P[i] - digit*D < 2^(-12)
;
;     Multiplying by 2^(13):
;
;       0 < P[i+1] < 2
;
; Notes:
;
; (1) The subtraction to create P[i] is done by subtracting the four 16x16
;     products formed from the digit and the 16-bit chunks of the divisor
;     from the partial remainder. Two of these 32-bit products are aligned
;     with the partial remainder and thus don't cause any problems. The
;     other two are both mis-aligned by 16 bits. One way to subtract them
;     would be to do a double word shift on them and subtract the results
;     from the partial remainder: this takes 2 instructions to form the
;     central shifted word and 3 for the subtraction (two of which are
;     "shift and subtracts"). However, this makes use of one register more
;     than we have. So the code below makes use of a trick, based on the
;     fact that if we subtract the top 16 bits and the bottom 16 bits of the
;     central shifted word separately, only one of the subtractions can
;     cause a borrow. So if we've got a borrow after the first one, we do
;     the second one without setting the condition codes, knowing that it
;     won't cause a borrow; if we don't, we set the condition codes on the
;     result of the second subtraction.
;
; (2) The multiplication operands are generally ordered to maximise the
;     chance of early termination. This means that all but the top chunk of
;     the divisor are good second operands to the multiplication, the digit
;     is next best, and the top chunk of the divisor is the least good.
;
; (3) The above is in fact not exactly true, due to the fact that it saves
;     some cycles not to shift P[1] and P[3] left by 13 bits, but to wait
;     until P[2] and P[4] are generated, then shift them left 26 bits.

        MOV     Rtmp,OP2mhi,LSR #15     ;Rtmp := Papprox
        MUL     Rtmp2,Rarith,Rtmp       ;Rtmp2 := Papprox * A
        MOV     Rtmp2,Rtmp2,LSR #16     ;Rtmp2 := digit
        MUL     Rtmp,Rtmp2,Rins         ;Subtract digit*D from P[0] to
        SUBS    OP2mlo,OP2mlo,Rtmp      ; form P[1]*2^(-13) - this requires
        MUL     Rtmp,OP1sue,Rtmp2       ; 4 multiplications and subtractions
        SBC     OP2mhi,OP2mhi,Rtmp      ; at various alignments
        MUL     Rtmp,Rtmp2,R14
        SUBS    OP2sue,OP2sue,Rtmp,LSL #16
        SBCS    OP2mlo,OP2mlo,Rtmp,LSR #16
        MUL     Rtmp,Rtmp2,Rfpsr
        SUBCC   OP2mlo,OP2mlo,Rtmp,LSL #16  ;Already got a borrow
        SUBCSS  OP2mlo,OP2mlo,Rtmp,LSL #16  ;No borrow yet - try for one
        SBC     OP2mhi,OP2mhi,Rtmp,LSR #16
        MOV     OP1mhi,Rtmp2,LSL #16    ;OP1mhi := Q[1]

        CDebug1 5,"1st iter'n: quotient so far =",OP1mhi
        CDebug3 5,"          partial remainder =",OP2mhi,OP2mlo,OP2sue

; Seventh step: second iteration. At the end of this step, we check whether
; the multiplication is single precision and branch out to termination code
; if so.

        MOV     Rtmp,OP2mhi,LSR #2      ;Rtmp := Papprox
        MUL     Rtmp2,Rarith,Rtmp       ;Rtmp2 := Papprox * A
        MOV     Rtmp2,Rtmp2,LSR #16     ;Rtmp2 := digit
        MUL     Rtmp,Rtmp2,Rins         ;Subtract digit*D from P[1]*2^(-13)
        SUBS    OP2sue,OP2sue,Rtmp,LSL #19  ; to form P[2]*2^(-26) - this
        SBCS    OP2mlo,OP2mlo,Rtmp,LSR #13  ; requires 4 multiplications and
        MUL     Rtmp,OP1sue,Rtmp2       ; subtractions at various alignments
        SUBCC   OP2mlo,OP2mlo,Rtmp,LSL #19  ;Already got a borrow
        SUBCSS  OP2mlo,OP2mlo,Rtmp,LSL #19  ;No borrow yet - try for one
        SBC     OP2mhi,OP2mhi,Rtmp,LSR #13
        MUL     Rtmp,Rtmp2,R14
        SUBS    OP2sue,OP2sue,Rtmp,LSL #3
        SBCS    OP2mlo,OP2mlo,Rtmp,LSR #29
        MUL     Rtmp,Rtmp2,Rfpsr
        SUBCC   OP2mlo,OP2mlo,Rtmp,LSL #3   ;Already got a borrow
        SUBCSS  OP2mlo,OP2mlo,Rtmp,LSL #3   ;No borrow yet - try for one
        SBC     OP2mhi,OP2mhi,Rtmp,LSR #29
        MOV     OP2mhi,OP2mhi,LSL #26   ;Shift by 26 bits to form P[2]
        ORR     OP2mhi,OP2mhi,OP2mlo,LSR #6
        MOV     OP2mlo,OP2mlo,LSL #26
        ORR     OP2mlo,OP2mlo,OP2sue,LSR #6
        MOV     OP2sue,OP2sue,LSL #26
        ADD     OP1mhi,OP1mhi,Rtmp2,LSL #3  ;OP1mhi := Q[2]

        CDebug1 5,"2nd iter'n: quotient so far =",OP1mhi
        CDebug3 5,"          partial remainder =",OP2mhi,OP2mlo,OP2sue

        LDR     Rtmp,[Rsp,#12]          ;Recover instruction

        [ FPEWanted :LOR: FPASCWanted

        TST     Rtmp,#Pr1_mask          ;Check for single precision
        TSTEQ   Rtmp,#Pr2_mask
        BEQ     Div_Single

        |

        TST     Rtmp,#Single_mask       ;Use a simpler encoding
        BNE     Div_Single

        ]

; Eighth step: third iteration.

        MOV     Rtmp,OP2mhi,LSR #15     ;Rtmp := Papprox
        MUL     Rtmp2,Rarith,Rtmp       ;Rtmp2 := Papprox * A
        MOV     Rtmp2,Rtmp2,LSR #16     ;Rtmp2 := digit
        MUL     Rtmp,Rtmp2,Rins         ;Subtract digit*D from P[2] to
        SUBS    OP2mlo,OP2mlo,Rtmp      ; form P[3]*2^(-13) - this requires
        MUL     Rtmp,OP1sue,Rtmp2       ; 4 multiplications and subtractions
        SBC     OP2mhi,OP2mhi,Rtmp      ; at various alignments
        MUL     Rtmp,Rtmp2,R14
        SUBS    OP2sue,OP2sue,Rtmp,LSL #16
        SBCS    OP2mlo,OP2mlo,Rtmp,LSR #16
        MUL     Rtmp,Rtmp2,Rfpsr
        SUBCC   OP2mlo,OP2mlo,Rtmp,LSL #16  ;Already got a borrow
        SUBCSS  OP2mlo,OP2mlo,Rtmp,LSL #16  ;No borrow yet - try for one
        SBC     OP2mhi,OP2mhi,Rtmp,LSR #16
        MOV     OP1mlo,Rtmp2,LSL #22    ;(OP1mhi,OP1mlo) := Q[3]
        ADD     OP1mhi,OP1mhi,Rtmp2,LSR #10

        CDebug2 5,"3rd iter'n: quotient so far =",OP1mhi,OP1mlo
        CDebug3 5,"          partial remainder =",OP2mhi,OP2mlo,OP2sue

; Ninth step: fourth iteration. At the end of this step, we check whether
; the multiplication is double precision and branch out to termination code
; if so.

        MOV     Rtmp,OP2mhi,LSR #2      ;Rtmp := Papprox
        MUL     Rtmp2,Rarith,Rtmp       ;Rtmp2 := Papprox * A
        MOV     Rtmp2,Rtmp2,LSR #16     ;Rtmp2 := digit
        MUL     Rtmp,Rtmp2,Rins         ;Subtract digit*D from P[3]*2^(-13)
        SUBS    OP2sue,OP2sue,Rtmp,LSL #19  ; to form P[4]*2^(-26) - this
        SBCS    OP2mlo,OP2mlo,Rtmp,LSR #13  ; requires 4 multiplications and
        MUL     Rtmp,OP1sue,Rtmp2       ; subtractions at various alignments
        SUBCC   OP2mlo,OP2mlo,Rtmp,LSL #19  ;Already got a borrow
        SUBCSS  OP2mlo,OP2mlo,Rtmp,LSL #19  ;No borrow yet - try for one
        SBC     OP2mhi,OP2mhi,Rtmp,LSR #13
        MUL     Rtmp,Rtmp2,R14
        SUBS    OP2sue,OP2sue,Rtmp,LSL #3
        SBCS    OP2mlo,OP2mlo,Rtmp,LSR #29
        MUL     Rtmp,Rtmp2,Rfpsr
        SUBCC   OP2mlo,OP2mlo,Rtmp,LSL #3   ;Already got a borrow
        SUBCSS  OP2mlo,OP2mlo,Rtmp,LSL #3   ;No borrow yet - try for one
        SBC     OP2mhi,OP2mhi,Rtmp,LSR #29
        MOV     OP2mhi,OP2mhi,LSL #26   ;Shift by 26 bits to form P[4]
        ORR     OP2mhi,OP2mhi,OP2mlo,LSR #6
        MOV     OP2mlo,OP2mlo,LSL #26
        ORR     OP2mlo,OP2mlo,OP2sue,LSR #6
        MOV     OP2sue,OP2sue,LSL #26
        ADDS    OP1mlo,OP1mlo,Rtmp2,LSL #9  ;(OP1mhi,OP1mlo) := Q[4]
        ADC     OP1mhi,OP1mhi,#0

        CDebug2 5,"4th iter'n: quotient so far =",OP1mhi,OP1mlo
        CDebug3 5,"          partial remainder =",OP2mhi,OP2mlo,OP2sue

        LDR     Rtmp,[Rsp,#12]          ;Recover instruction

        [ FPEWanted :LOR: FPASCWanted

        TST     Rtmp,#Pr1_mask          ;Check for double precision
        BEQ     Div_Double

        |

        TST     Rtmp,#Double_mask
        BNE     Div_Double

        ]

; Tenth step: fifth iteration. We can enter the extended precision
; termination code at the end of this iteration, since we know it must be an
; extended precision division.

        MOV     Rtmp,OP2mhi,LSR #15     ;Rtmp := Papprox
        MUL     Rtmp2,Rarith,Rtmp       ;Rtmp2 := Papprox * A
        MOV     Rtmp2,Rtmp2,LSR #16     ;Rtmp2 := digit
        MUL     Rtmp,Rtmp2,Rins         ;Subtract digit*D from P[4] to
        SUBS    OP2mlo,OP2mlo,Rtmp      ; form P[5]*2^(-13) - this requires
        MUL     Rtmp,OP1sue,Rtmp2       ; 4 multiplications and subtractions
        SBC     OP2mhi,OP2mhi,Rtmp      ; at various alignments
        MUL     Rtmp,Rtmp2,R14
        SUBS    OP2sue,OP2sue,Rtmp,LSL #16
        SBCS    OP2mlo,OP2mlo,Rtmp,LSR #16
        MUL     Rtmp,Rtmp2,Rfpsr
        SUBCC   OP2mlo,OP2mlo,Rtmp,LSL #16  ;Already got a borrow
        SUBCSS  OP2mlo,OP2mlo,Rtmp,LSL #16  ;No borrow yet - try for one
        SBC     OP2mhi,OP2mhi,Rtmp,LSR #16
        MOV     OP2mhi,OP2mhi,LSL #14   ;Shift by 14 bits to form 2*P[5]
        ORR     OP2mhi,OP2mhi,OP2mlo,LSR #18
        MOV     OP2mlo,OP2mlo,LSL #14
        ORR     OP2mlo,OP2mlo,OP2sue,LSR #18
        MOV     OP2sue,OP2sue,LSL #14
        MOV     Rarith,Rtmp2,LSL #28    ;(OP1mhi,OP1mlo,Rarith) := Q[5]
        ADDS    OP1mlo,OP1mlo,Rtmp2,LSR #4
        ADC     OP1mhi,OP1mhi,#0

        CDebug3 5,"5th iter'n: quotient so far =",OP1mhi,OP1mlo,Rarith
        CDebug3 5,"          partial remainder =",OP2mhi,OP2mlo,OP2sue

Div_Extended

; We've completed the main work for an extended precision division. We've
; now got the divisor D in (OP1sue,Rfpsr,Rins,R14), the quotient Q[5] in
; (OP1mhi,OP1mlo,Rarith) and twice the partial remainder P[5] in
; (OP2mhi,OP2mlo,OP2sue) such that:
;
;   (a) Q[5] is a multiple of 2^(-67);
;
;   (b) P[5] is a multiple of 2^(-65);
;
;   (c) P = Q[5]*D + P[5]*2^(-65);
;
;   (d) 0 < P[5] < 2;
;
; The main problem with this is that P[5]*2^(-65) may be almost 2^(-64),
; while Q[5] is a multiple of 2^(-67). To know the correct IEEE answer, we
; have to make the partial remainder be less than the "quantum" in the
; quotient - i.e. less than 2^(-67) in this case. Without doing this, we
; can't calculate the sticky bit accurately: we know that a non-zero partial
; remainder at this point represents a string of quotient bits which are not
; all zero, but if they overlap the quotient bits we've already calculated,
; we don't know whether adding the bits together in the area of overlap
; would result in a string of all zero bits and thus a sticky bit of 0.
;
; We deal with this by doing three bits worth of ordinary long division. To
; save on multi-word additions and problems about carry flag use, we put the
; bits calculated into R14 and only add them into the quotient once at the
; end.
;
; Note that generating twice P[5] above with the binary point to the right
; of bit 30 of OP2mhi is equivalent to generating P[5] with the binary point
; to the right of bit 31 - i.e. to generating it in the position we want it
; to be for the code that follows. This is a trick we only use for extended
; precision, since for the other precisions, we need to be ready for another
; iteration of the algorithm above as well as for the termination code.

        ORR     OP1sue,Rfpsr,OP1sue,LSL #16     ;Reform divisor
        ORR     Rfpsr,R14,Rins,LSL #16

        MOV     R14,#0                  ;Initialise extra bits

        SUBS    Rtmp2,OP2mlo,Rfpsr      ;First extra bit: trial subtraction
        SBCS    Rtmp,OP2mhi,OP1sue      ; of divisor from partial remainder
        MOVCS   OP2mlo,Rtmp2            ;If bit is 1, really do subtraction
        MOVCS   OP2mhi,Rtmp
        ADC     R14,R14,R14             ;Accumulate bit

        MOV     Rins,#0                 ;Initialise overflow word
        ADDS    OP2sue,OP2sue,OP2sue    ;Second extra bit: shift partial
        ADCS    OP2mlo,OP2mlo,OP2mlo    ; remainder
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     Rins,Rins,Rins
        SUBS    Rtmp2,OP2mlo,Rfpsr      ;Trial subtraction of divisor
        SBCS    Rtmp,OP2mhi,OP1sue      ; from partial remainder
        SBCS    Rins,Rins,#0
        MOVCS   OP2mlo,Rtmp2            ;If bit is 1, really do subtraction
        MOVCS   OP2mhi,Rtmp
        ADC     R14,R14,R14             ;Accumulate bit

        MOV     Rins,#0                 ;Initialise overflow word
        ADDS    OP2sue,OP2sue,OP2sue    ;Third extra bit: shift partial
        ADCS    OP2mlo,OP2mlo,OP2mlo    ; remainder
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     Rins,Rins,Rins
        SUBS    Rtmp2,OP2mlo,Rfpsr      ;Trial subtraction of divisor
        SBCS    Rtmp,OP2mhi,OP1sue      ; from partial remainder
        SBCS    Rins,Rins,#0
        MOVCS   OP2mlo,Rtmp2            ;If bit is 1, really do subtraction
        MOVCS   OP2mhi,Rtmp
        ADC     R14,R14,R14             ;Accumulate bit

        CDebug1 5,"Extra bits to add in are",R14

; (OP1mhi,OP1mlo,Rarith) now contains 68 bits of quotient, R14 three extra
; bits that need to be added into its low end and (OP2mhi,OP2mlo) the final
; partial remainder. (We've shifted all the extra bits out of OP2sue, and the
; overflow word Rins must be zero at this point.)
;   This is enough bits to provide guard and round bits, plus 2 bits
; contributing to the sticky bit and enough information to complete
; generating it. We will finish generating it by setting bit 0 of Rarith if
; the partial remainder is non-zero.

        ORRS    Rtmp,OP2mhi,OP2mlo
        ORRNE   Rarith,Rarith,#1

; Now add the three extra bits into the quotient and test for mantissa
; underflow.

        ADDS    Rarith,Rarith,R14,LSL #28   ;Add extra bits into quotient
        ADCS    OP1mlo,OP1mlo,#0
        ADCS    OP1mhi,OP1mhi,#0

; If no mantissa underflow, we're ready to return. Otherwise, we must
; recover the spilled registers (to get hold of the result exponent), shift
; the mantissa left one bit, decrement the exponent and return.

  IF Interworking :LOR: Thumbing
        LDMMIFD Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,LR}
        BXMI    LR
  ELSE
        LDMMIFD Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,PC}
  ENDIF

        LDMFD   Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,LR}
        ADDS    Rarith,Rarith,Rarith
        ADCS    OP1mlo,OP1mlo,OP1mlo
        ADC     OP1mhi,OP1mhi,OP1mhi
        SUB     OP2sue,OP2sue,#1
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Div_Double

; We've completed the main work for a double precision division. We've now
; got the divisor D in (OP1sue,Rfpsr,Rins,R14), the quotient Q[4] in
; (OP1mhi,OP1mlo,Rarith) and the partial remainder P[4] in
; (OP2mhi,OP2mlo,OP2sue) such that:
;
;   (a) Q[4] is a multiple of 2^(-54);
;
;   (b) P[4] is a multiple of 2^(-65);
;
;   (c) P = Q[4]*D + P[4]*2^(-52);
;
;   (d) 0 < P[4] < 2;
;
; The main problem with this is that P[4]*2^(-52) may be almost 2^(-51),
; while Q[4] is a multiple of 2^(-54). To know the correct IEEE answer, we
; have to make the partial remainder be less than the "quantum" in the
; quotient - i.e. less than 2^(-54) in this case. Without doing this, we
; can't calculate the sticky bit accurately: we know that a non-zero partial
; remainder at this point represents a string of quotient bits which are not
; all zero, but if they overlap the quotient bits we've already calculated,
; we don't know whether adding the bits together in the area of overlap
; would result in a string of all zero bits and thus a sticky bit of 0.
;
; We deal with this by doing three bits worth of ordinary long division. To
; save on multi-word additions and problems about carry flag use, we put the
; bits calculated into R14 and only add them into the quotient once at the
; end.

        ORR     OP1sue,Rfpsr,OP1sue,LSL #16     ;Reform divisor
        ORR     Rfpsr,R14,Rins,LSL #16

        MOV     R14,#0                  ;Initialise extra bits

        ADDS    OP2sue,OP2sue,OP2sue    ;First extra bit: shift partial
        ADCS    OP2mlo,OP2mlo,OP2mlo    ; remainder
        ADC     OP2mhi,OP2mhi,OP2mhi
        SUBS    Rtmp2,OP2mlo,Rfpsr      ;Trial subtraction of divisor from
        SBCS    Rtmp,OP2mhi,OP1sue      ; partial remainder
        MOVCS   OP2mlo,Rtmp2            ;If bit is 1, really do subtraction
        MOVCS   OP2mhi,Rtmp
        ADC     R14,R14,R14             ;Accumulate bit

        MOV     Rins,#0                 ;Initialise overflow word
        ADDS    OP2sue,OP2sue,OP2sue    ;Second extra bit: shift partial
        ADCS    OP2mlo,OP2mlo,OP2mlo    ; remainder
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     Rins,Rins,Rins
        SUBS    Rtmp2,OP2mlo,Rfpsr      ;Trial subtraction of divisor
        SBCS    Rtmp,OP2mhi,OP1sue      ; from partial remainder
        SBCS    Rins,Rins,#0
        MOVCS   OP2mlo,Rtmp2            ;If bit is 1, really do subtraction
        MOVCS   OP2mhi,Rtmp
        ADC     R14,R14,R14             ;Accumulate bit

        MOV     Rins,#0                 ;Initialise overflow word
        ADDS    OP2sue,OP2sue,OP2sue    ;Third extra bit: shift partial
        ADCS    OP2mlo,OP2mlo,OP2mlo    ; remainder
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     Rins,Rins,Rins
        SUBS    Rtmp2,OP2mlo,Rfpsr      ;Trial subtraction of divisor
        SBCS    Rtmp,OP2mhi,OP1sue      ; from partial remainder
        SBCS    Rins,Rins,#0
        MOVCS   OP2mlo,Rtmp2            ;If bit is 1, really do subtraction
        MOVCS   OP2mhi,Rtmp
        ADC     R14,R14,R14             ;Accumulate bit

        CDebug1 5,"Extra bits to add in are",R14

; (OP1mhi,OP1mlo) now contains 55 bits of quotient, R14 three extra bits
; that need to be added into its low end and (OP2mhi,OP2mlo) the final
; partial remainder. (We've shifted all the extra bits out of OP2sue, and
; the overflow word Rins must be zero at this point.)
;   This is enough bits to provide guard and round bits, plus enough
; information to generate the sticky bit. We do this by setting Rarith to
; zero if the partial remainder is zero, non-zero if the partial remainder
; is non-zero. Note that since we know rounding will take place to double
; precision, we don't mind having the sticky bit overflow into the extended
; precision round bit.

        ORR     Rarith,OP2mhi,OP2mlo

; Now add the three extra bits into the quotient and test for mantissa
; underflow.

        ADDS    OP1mlo,OP1mlo,R14,LSL #9    ;Add extra bits into quotient
        ADCS    OP1mhi,OP1mhi,#0

; If no mantissa underflow, we're ready to return. Otherwise, we must
; recover the spilled registers (to get hold of the result exponent), shift
; the mantissa left one bit, decrement the exponent and return.

  IF Interworking :LOR: Thumbing
        LDMMIFD Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,LR}
        BXMI    LR
  ELSE
        LDMMIFD Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,PC}
  ENDIF

        LDMFD   Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,LR}
        ADDS    OP1mlo,OP1mlo,OP1mlo
        ADC     OP1mhi,OP1mhi,OP1mhi
        SUB     OP2sue,OP2sue,#1
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Div_Single

; We've completed the main work for a single precision division. We've now
; got the divisor D in (OP1sue,Rfpsr,Rins,R14), the quotient Q[2] in
; (OP1mhi,OP1mlo,Rarith) and the partial remainder P[2] in
; (OP2mhi,OP2mlo,OP2sue) such that:
;
;   (a) Q[2] is a multiple of 2^(-28);
;
;   (b) P[2] is a multiple of 2^(-65);
;
;   (c) P = Q[2]*D + P[2]*2^(-26);
;
;   (d) 0 < P[2] < 2;
;
; The main problem with this is that P[2]*2^(-26) may be almost 2^(-25),
; while Q[2] is a multiple of 2^(-28). To know the correct IEEE answer, we
; have to make the partial remainder be less than the "quantum" in the
; quotient - i.e. less than 2^(-28) in this case. Without doing this, we
; can't calculate the sticky bit accurately: we know that a non-zero partial
; remainder at this point represents a string of quotient bits which are not
; all zero, but if they overlap the quotient bits we've already calculated,
; we don't know whether adding the bits together in the area of overlap
; would result in a string of all zero bits and thus a sticky bit of 0.
;
; We deal with this by doing three bits worth of ordinary long division.

        ORR     OP1sue,Rfpsr,OP1sue,LSL #16     ;Reform divisor
        ORR     Rfpsr,R14,Rins,LSL #16

        ADDS    OP2sue,OP2sue,OP2sue    ;First extra bit: shift partial
        ADCS    OP2mlo,OP2mlo,OP2mlo    ; remainder
        ADC     OP2mhi,OP2mhi,OP2mhi
        SUBS    Rtmp2,OP2mlo,Rfpsr      ;Trial subtraction of divisor from
        SBCS    Rtmp,OP2mhi,OP1sue      ; partial remainder
        MOVCS   OP2mlo,Rtmp2            ;If bit is 1, really do subtraction
        MOVCS   OP2mhi,Rtmp
        ADDCS   OP1mhi,OP1mhi,#1:SHL:5  ;Add bit to quotient

        MOV     Rins,#0                 ;Initialise overflow word
        ADDS    OP2sue,OP2sue,OP2sue    ;Second extra bit: shift partial
        ADCS    OP2mlo,OP2mlo,OP2mlo    ; remainder
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     Rins,Rins,Rins
        SUBS    Rtmp2,OP2mlo,Rfpsr      ;Trial subtraction of divisor
        SBCS    Rtmp,OP2mhi,OP1sue      ; from partial remainder
        SBCS    Rins,Rins,#0
        MOVCS   OP2mlo,Rtmp2            ;If bit is 1, really do subtraction
        MOVCS   OP2mhi,Rtmp
        ADDCS   OP1mhi,OP1mhi,#1:SHL:4  ;Add bit to quotient

        MOV     Rins,#0                 ;Initialise overflow word
        ADDS    OP2sue,OP2sue,OP2sue    ;Third extra bit: shift partial
        ADCS    OP2mlo,OP2mlo,OP2mlo    ; remainder
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     Rins,Rins,Rins
        SUBS    Rtmp2,OP2mlo,Rfpsr      ;Trial subtraction of divisor
        SBCS    Rtmp,OP2mhi,OP1sue      ; from partial remainder
        SBCS    Rins,Rins,#0
        MOVCS   OP2mlo,Rtmp2            ;If bit is 1, really do subtraction
        MOVCS   OP2mhi,Rtmp
        ADDCS   OP1mhi,OP1mhi,#1:SHL:3  ;Add bit to quotient

        CDebug1 5,"Quotient after adding in extra bits is",R14

; (OP1mhi,OP1mlo,Rarith) now contains 29 bits of quotient and (OP2mhi,OP2mlo)
; the final partial remainder. (We've shifted all the extra bits out of
; OP2sue, and the overflow word Rins must be zero at this point.)
;   This is enough bits to provide guard and round bits, plus 3 bits
; contributing to the sticky bit and enough information to complete
; generating it. We will finish generating it by setting Rarith to zero if
; the partial remainder zero, non-zero if the partial remainder is non-zero.
;   We must also set the low word of the result mantissa to 0.

        ORR     Rarith,OP2mhi,OP2mlo
        MOV     OP1mlo,#0

; Now test for mantissa underflow. If no mantissa underflow, we're ready to
; return. Otherwise, we must recover the spilled registers (to get hold of
; the result exponent), shift the mantissa left one bit, decrement the
; exponent and return.

        TEQ     OP1mhi,#0

  IF Interworking :LOR: Thumbing
        LDMMIFD Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,LR}
        BXMI    LR
  ELSE
        LDMMIFD Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,PC}
  ENDIF

        LDMFD   Rsp!,{OP1sue,OP2sue,Rfpsr,Rins,LR}
        MOV     OP1mhi,OP1mhi,LSL #1
        SUB     OP2sue,OP2sue,#1

  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

;===========================================================================

; Reciprocal approximation table
; ------------------------------
;
; This table contains 128 entries, indexed by the first 7 fractional bits of
; a normalised divisor mantissa D. The value Rapprox obtained has the
; property that:
;
;   1/D <= Rapprox*2^(-7) < 1/D + 2^(-6)
;
; In fact, entry N in the table is calculated by the formula:
;
;   Entry(N) = 2^14 divided by (128+N), rounded up to an integer.
;
; Proof that this is correct: if the first 7 fractional bits of D are N, we
; know that:
;
;   (128+N)*2^(-7) <= D < (129+N)*2^(-7)
;
; This gives us:
;   (2^7)/(129+N) < 1/D <= (2^7)/(128+N)
;
; Next, we have:
;   1/(128+N) - 1/(129+N) = 1/((128+N)*(129+N))
;                         < 1/(128*128)
;                         = 2^(-14)
;
; Multiplying by 2^7 and rearranging:
;   (2^7)/(128+N) - 2^(-7) < (2^7)/(129+N)
;
; So:
;   (2^7)/(128+N) - 2^(-7) < 1/D <= (2^7)/(128+N)
;
; Or:
;   1/D <= (2^7)/(128+N) < 1/D + 2^(-7)
;
; If we round (2^7)/(128+N) up to a multiple of 2^(-7), we increase it by
; less than 2^(-7), giving us:
;
;   1/D <= (2^7)/(128+N) rounded up to a multiple of 2^(-7) < 1/D + 2^(-64)
;
; But (2^7)/(128+N) rounded up to a multiple of 2^(-7) is Entry(N)*2^(-7),
; giving us the desired property.

Recip_Table BytesStart

        GBLA    Rec_tmp
Rec_tmp SETA    0
        WHILE   Rec_tmp < 128
        DCB     (16384+127+Rec_tmp)/(128+Rec_tmp)
Rec_tmp SETA    Rec_tmp+1
        WEND

        BytesEnd

        ]                               ; Conditional assembly of Div

;===========================================================================

        [ :DEF: fmod_s :LOR: FPEWanted :LOR: FPASCWanted

; Routine to perform the IEEE remainder function. It has the usual two 
; labels on its entry point.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard dyadic operation entry and exit conventions - see top of
; this file.

        ASSERT  RNDexp = OP2sue ;We swap over from the use of OP2sue to that
                                ; of RNDexp partway through this routine.

        [ FPEWanted
RemFPE
        ]

        [ FPASCWanted
RemFPASC
        ]

        CDebug3 3,"RemFPASC/FPE: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 3,"              op2 =",OP2sue,OP2mhi,OP2mlo

        [ FPEWanted :LOR: FPASCWanted

; Start by detecting the "fast track" case of both operands being common.

        TST     OP1sue,#Uncommon_bit
        TSTEQ   OP2sue,#Uncommon_bit
        BNE     Rem_Uncommon

; If the second operand is a zero, we've got an invalid operation.
; Otherwise, if the first operand is a zero, the result is equal to the
; first operand.

        ORRS    Rarith,OP2mhi,OP2mlo
        MOVEQ   Rtmp,#InvReas_XRem0
        BEQ     InvalidOperation2ForSDE

        ORRS    Rarith,OP1mhi,OP1mlo
        BEQ     Rem_FirstOperand_Zero

        ]

; Both operands may now be assumed to be normalised numbers - now to deal
; with signs and exponents.
;
; We're going to generate the remainder by a long-division-like algorithm,
; which can be summarised as follows:
;
;   partial remainder = ABS(op1); sign = SIGN(op1);
;   FOR I = (op1 exponent) TO ((op2 exponent)-1) STEP -1
;     Trial subtract (partial remainder) from (op2 mantissa)*2^I;
;     IF strictly negative THEN
;       partial remainder := 2*(op2 mantissa)*2^I - (partial remainder);
;       sign := NOT(sign);
;   NEXT
;   IF (partial remainder) = 0
;     THEN result = 0, with sign SIGN(op1);
;     ELSE result = (-1)^(sign) * (partial remainder);
;
; We're clearly going to keep both the current sign and the original sign
; around: we'll do this in the top two bits of OP1sue. We'll also need to
; know the prospective result exponent (in OP2sue = RNDexp) and the number
; of iterations of the loop (in Rarith). However, note that if the
; calculated number of iterations is 0 or less, this means that the result
; is equal to the first operand. So we'll take care to calculate this number
; before disturbing the first operand in any way.
;
; Note also that the sign of the second operand is totally irrelevant, now
; that we've got past the stage of there being any potential invalid operation
; or divide-by-zero exceptions.

Rem_Common

        STMFD   Rsp!,{LR}               ;Because we'll need the register, we
                                        ; may well call NormaliseOp1, and to
                                        ; match the Rem_Uncommon path.

        AND     RNDexp,OP2sue,#ToExp_mask       ;Second operand exponent
        SUB     RNDexp,RNDexp,#1                ;Prospective result exponent
        AND     Rarith,OP1sue,#ToExp_mask       ;First operand exponent
        SUBS    Rarith,Rarith,RNDexp            ;Number of iterations - 1

Rem_ExponentsDone

        AND     OP1sue,OP1sue,#Sign_bit         ;All cases want this
        ADDLT   RNDexp,Rarith,RNDexp            ;Recover first operand exp.
        MOVLT   Rarith,#0                       ;And return first operand
  IF Interworking :LOR: Thumbing
        BXLT    LR
  ELSE
        MOVLT   PC,LR                           ; exactly
  ENDIF


; Prepare for the main loop and branch into it.

        MOV     OP1sue,OP1sue,ASR #1            ;Make a copy of the sign, in
                                                ; case the result is zero
        MOV     LR,#0                           ;Top word of the partial
                                                ; remainder

        CDebug2 4,"Entering RMF loop: Rarith, LR",Rarith,LR
        CDebug3 4," op1",OP1sue,OP1mhi,OP1mlo
        CDebug3 4," op2",RNDexp,OP2mhi,OP2mlo

        B       Rem_Loop_Entry

Rem_Loop_Shift

; Shift the partial remainder left by 1 bit, using a bit of trickery to do
; each word in 1 cycle.

        MOV     LR,OP1mhi,LSR #31
        ADDS    OP1mlo,OP1mlo,OP1mlo
        ADC     OP1mhi,OP1mhi,OP1mhi

Rem_Loop_Entry

; Do the trial subtraction of divisor - partial remainder; if it comes out
; non-negative, keep the previous partial remainder.

        RSBS    Rtmp,OP1mlo,OP2mlo
        RSCS    Rtmp2,OP1mhi,OP2mhi
        RSCS    LR,LR,#0
        BCS     Rem_Loop_End

; Otherwise, use the trial division result to form a new partial remainder
; equal to 2*divisor minus old partial remainder, and note that the sign of
; the partial remainder has changed.

        ADDS    OP1mlo,Rtmp,OP2mlo
        ADC     OP1mhi,Rtmp2,OP2mhi
        EOR     OP1sue,OP1sue,#Sign_bit

Rem_Loop_End

; Loop until finished. Note the partial remainder is completely contained in
; OP2mhi and OP2mlo at this point.

        SUBS    Rarith,Rarith,#1
        BGE     Rem_Loop_Shift

; The result will always be exact.

        MOV     Rarith,#0

; If we've now got a partial remainder of exactly zero, the result is zero,
; with sign equal to that of the original first operand. Otherwise, we've
; got to normalise the result.

        ORRS    Rtmp,OP1mhi,OP1mlo
        MOVEQ   OP1sue,OP1sue,LSL #1    ;Recover copy of original sign
        MOVEQ   RNDexp,#0
        ANDNE   OP1sue,OP1sue,#Sign_bit
        BLNE    $NormaliseOp1_str

; And return.

  IF Interworking :LOR: Thumbing
        LDMFD   Rsp!,{LR}
        BX      LR
  ELSE
        LDMFD   Rsp!,{PC}
  ENDIF


        ]                               ; Conditional assembly of Rem/mod

;===========================================================================

        [ :DEF: sqrt_s :LOR: FPEWanted :LOR: FPASCWanted

; Routine to take the square root of an internal format floating point
; number. Unlike the dyadic arithmetic instructions, only one entry point is
; required: we do however give it two labels for the sake of consistent
; naming.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;   This routine will not work correctly with an input which is an
; unnormalised URD result, or an invalid internal format number.
;
; Uses standard monadic operation entry and exit conventions - see top of
; this file.

        [ FPEWanted
SqrtFPE
        ]

        [ FPASCWanted
SqrtFPASC
        ]

        [ :LNOT: :DEF: sqrt_s

        CDebug3 3,"SqrtFPE/FPASC: operand =",OP1sue,OP1mhi,OP1mlo

; Start by splitting according to whether the operand is common or uncommon.
; The code to deal with uncommon operands lies a long way down in the
; source, to avoid addressability problems.

        TST     OP1sue,#Uncommon_bit
        BNE     Sqrt_Uncommon

; If the operand is a zero, the product is the same zero. Because the
; operand is common and assumed not to be an unnormalised URD result, we can
; check for zeros by means of the units bit.

        TST     OP1mhi,#EIUnits_bit
        BEQ     Sqrt_Zero

; The operand may now be assumed to be a normalised number. If it is
; negative, we have an invalid operation exception. Otherwise, the result
; sign is positive (equal to the operand sign) and we need to produce the
; result exponent.
;   We produce the result exponent by adding the exponent bias to the
; already biased exponent, producing (unbiased exponent) + 2*bias, then
; shifting right by one bit, producing ((unbiased exponent) DIV 2) + bias.
; We set the condition codes on this last instruction in order to transfer
; the least significant bit of the unbiased exponent into C.
        
        ]

        [ FPLibWanted
__fp_sqrt_common
        ]

Sqrt_Common

        AND     RNDexp,OP1sue,#ToExp_mask ;Extract operand exponent

        [ FPEWanted :LOR: FPASCWanted

        ANDS    OP1sue,OP1sue,#Sign_bit ;Isolate sign bit & check positive
        MOVNE   Rtmp,#InvReas_SqrtNeg
        BNE     InvalidOperation1ForSDE

        |

        ANDS    OP1sue,OP1sue,#Sign_bit ;Isolate sign bit
        ORRNE   OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BXNE    LR
  ELSE
        MOVNE   PC,LR        
  ENDIF
        
        ]

        ADD     RNDexp,RNDexp,#EIExp_bias:AND:&FF00
        ADD     RNDexp,RNDexp,#EIExp_bias:AND:&FF
        ASSERT  (EIExp_bias-1) < &10000 ;Result exponent if mantissa
                                        ; overflow is (exp+bias) DIV 2
        MOVS    RNDexp,RNDexp,LSR #1

; This subsidiary entry point deals with taking the square root of a
; normalised mantissa.
; Entry: OP1sue = the result's sign, with an uncommon bit of 0 - the
;          remaining bits are zero;
;        OP1mhi = Operand mantissa, high word;
;        OP1mlo = Operand mantissa, low word;
;        RNDexp = Prospective result exponent;
;        Rins   = instruction (needed to determine the precision);
;        Rwp, Rfp, Rsp hold their usual values;
;        R14    = return link;
;        C      = least significant bit of operand's unbiased exponent.
; Exit:  OP1sue = the result's sign (always positive), with an uncommon bit
;          of 0; the remaining bits are zero;
;        OP1mhi, OP1mlo = the result's mantissa;
;        RNDexp = the result exponent;
;        Rarith holds the round bit (in bit 31) and the sticky bit (in bits
;          30:0) if the destination precision is extended; if the
;          destination precision is single or double, it holds part of the
;          sticky bit (the remainder of which is held in bits below the
;          round bit in OP1mhi and OP1mlo);
;        OP2mhi, OP2mlo, Rtmp, Rtmp2 and R14 may be corrupt;
;        All other registers preserved.
;
; Note that the result exponent is in fact always equal to the prospective
; result exponent: the process of taking the square root always results in a
; normalised mantissa. (Subsequent rounding may of course lead to mantissa
; overflow, but the raw unrounded result mantissa is always normalised.)

Sqrt_Mantissa

        CDebug2 4,"SqrtFPE/FPASC: mantissa =",OP1mhi,OP1mlo
        CDebug1 4,"               sign     =",OP1sue
        CDebug1 4,"               exponent =",RNDexp

; We do the square root by the standard "long square root" algorithm. (There
; is an optimisation possibility here, of doing square roots by
; Newton-Raphson followed by a final correction. This only applies to the
; FPASC, since the FPE's division is too slow for there to be any
; possibility of this making a profit - even the FPA's division will have to
; be used very carefully for it to have a hope of working.)
;
; A description of the long square root algorithm follows:
;
; The problem is to take the square root of a mantissa M in the range 1 <= M
; < 4. An initial approximation R[0]=1 to the root has the property that it
; is the rounded-down root to 0 places after the binary point - i.e. that
; R[0] is a multiple of 2^(-0) and R[0] <= Sqrt(M) < R[0] + 2^(-0). We will
; evaluate successive approximations R[i] to the root such that R[i] is the
; correct rounded-down root to i places after the binary point - i.e. that
; R[i] is a multiple of 2^(-i) and R[i] <= Sqrt(M) < R[i] + 2^(-i). If we
; know R[24], R[53] or R[64] respectively for single, double or extended
; precision, and in addition know whether the result is exact (i.e. whether
; R[i] = Sqrt(M) exactly), we have enough information to provide all the
; required fractional bits and the round and sticky bits, and so to
; calculate the correct IEEE square root. (Note that a guard bit is not
; required: the infinite precision square root of M will not suffer mantissa
; overflow or underflow, and so its finite precision approximations can only
; suffer mantissa overflow during rounding, not prior to rounding.)
;
; So we will use a partial remainder P[i] = M - R[i]^2; initially, P[0] =
; M-1. Next, we know that R[i+1] is either equal to R[i] or to R[i] +
; 2^(-i-1), depending on whether the next bit of the root is 0 or 1. To
; determine which, we need to know whether R[i] + 2^(-i-1) <= Sqrt(M): if it
; is, the next bit of the root is 1; if it isn't, the next bit of the root
; is 0.
;
; This is equivalent to asking whether (R[i] + 2^(-i-1))^2 <= M, i.e. to
; whether:
;
;   R[i]^2 + R[i]*2^(-i) + 2^(-2*i-2) <= M
;
; or to whether:
;
;   R[i]*2^(-i) + 2^(-2*i-2) <= P[i]
;
; If it is, then R[i+1] = R[i] - 2^(-i-1) and:
;
;   P[i+1] = M - R[i+1]^2
;          = M - (R[i] + 2^(-i-1))^2
;          = M - R[i]^2 - R[i]*2^(-i) - 2^(-2*i-2)
;          = P[i] - R[i]*2^(-i) - 2^(-2*i-2)
;
; If it isn't, then R[i+1] = R[i] and P[i+1] = M - R[i+1]^2 = M - R[i]^2 =
; P[i].
;
; So the long square root algorithm can be stated as follows, where N=24, 53
; or 64 respectively for single, double or extended precision:
;
; (1) Initialise: R[0] = 1, P[0] = M-1;
;
; (2) For i=0 to N-1:
;       Do a trial subtraction of R[i]*2^(-i) + 2^(-2*i-2) from P[i];
;       If result >= 0, put R[i+1] = R[i] + 2^(-i-1), P[i+1] = result of
;         trial subtraction;
;       Else put R[i+1] = R[i], P[i+1] = P[i];
;
; (3) The units, fractional and round bits of the result are in R[N], while
;     the sticky bit is 0 if P[N] = 0, 1 if P[N] > 0.
;
; Note that P[i] = M - R[i]^2
;                < M - (Sqrt(M) - 2^(-i))^2
;                = M - M + Sqrt(M)*2^(-i+1) - 2^(-2*i)
;                = Sqrt(M)*2^(-i+1) - 2^(-2*i)
;                < 2^(-i+2)
;
; So P[i] decreases greatly in magnitude during the long square root
; process. If we use it straightforwardly, this will result in a lot of
; spurious subtractions of bits known to be zero from other bits known to be
; zero during the algorithm. So instead, let us define Q[i] = P[i]*2^(i-1)
; and recast the algorithm in terms of Q[i]:
;
; (1) Initialise: R[0] = 1, Q[0] = (M-1)/2;
;
; (2) For i=0 to N-1:
;       Do a trial subtraction of R[i] + 2^(-i-2) from 2*Q[i];
;       If result >= 0, put R[i+1] = R[i] + 2^(-i-1), Q[i+1] = result of
;         trial subtraction;
;       Else put R[i+1] = R[i], Q[i+1] = 2*Q[i];
;
; (3) The units, fractional and round bits of the result are in R[N], while
;     the sticky bit is 0 if Q[N] = 0, 1 if Q[N] > 0.
;
; Introducing a travelling bit variable T[i] to represent 2^(-i-2) and
; rephrasing in terms of shifts:
;
; (1) Initialise: R[0] = 1, Q[0] = (M-1)/2, T[0] = 2^(-2);
;
; (2) For i=0 to N-1:
;       Do a trial subtraction of R[i] + T[i] from Q[i] << 1;
;       If result >= 0, put R[i+1] = R[i] + (T[i] << 1),
;                           Q[i+1] = (Q[i] << 1) - (R[i]+T[i]);
;       Else put R[i+1] = R[i], Q[i+1] = Q[i] << 1;
;
; (3) The units, fractional and round bits of the result are in R[N], while
;     the sticky bit is 0 if Q[N] = 0, 1 if Q[N] > 0.
;
; This is more-or-less the algorithm we use, though we split into different
; sections depending on how far the travelling bit has been shifted down so
; far, to avoid doing multi-word arithmetic until we have to.
;
; One thing we do have to look at is the precision required for Q[i]. We
; know that 0 < Q[i] = P[i]*2^(i-1) < 2^(-i+2)*2^(i-1) = 2, so one place
; before the binary point is enough. Initially, Q[0] = (M-1)/2 is a multiple
; of 2^(-64), requiring 64 places after the binary point, or 65 bits in
; total - one bit more than 2 words. This is highly inconvenient, but we can
; get around it by noticing that if M < 2, then the first two bits of the
; result are definitely 1.0, and we have R[1] = 1.0, Q[1] = M-1 and T[0] =
; 2^(-2). So Q[1] is a multiple of 2^(-63) and can be represented in two
; words. On the other hand, if M >= 2, then Q[0] = (M-1)/2 is a multiple of
; 2^(-63) and can also be represented by two words. This transforms the
; algorithm to:
;
; IF M < 1 THEN
;
;   (1) Initialise: R[1] = 1.0, Q[1] = M-1, T[1] = 2^(-3);
;
;   (2) For i=1 to N-1:
;         Do a trial subtraction of R[i] + T[i] from Q[i] << 1;
;         If result >= 0, put R[i+1] = R[i] + (T[i] << 1),
;                             Q[i+1] = (Q[i] << 1) - (R[i]+T[i]);
;         Else put R[i+1] = R[i], Q[i+1] = Q[i] << 1;
;
;   (3) The units, fractional and round bits of the result are in R[N], while
;       the sticky bit is 0 if Q[N] = 0, 1 if Q[N] > 0.
;
; ELSE
;
;   (1') Initialise: R[0] = 1, Q[0] = (M-1)/2, T[0] = 2^(-2);
;
;   (2') For i=0 to N-1:
;          Do a trial subtraction of R[i] + T[i] from Q[i] << 1;
;          If result >= 0, put R[i+1] = R[i] + (T[i] << 1),
;                              Q[i+1] = (Q[i] << 1) - (R[i]+T[i]);
;          Else put R[i+1] = R[i], Q[i+1] = Q[i] << 1;
;
;   (3') The units, fractional and round bits of the result are in R[N], while
;        the sticky bit is 0 if Q[N] = 0, 1 if Q[N] > 0.
;
; ENDIF
;
; Now Q[i] can be represented in two words up to the point where the trial
; subtraction produces results that overflow two words. We have the
; following situation at various iterations, remembering that T[i] = 2^(-i-1):
;
; For i < 30: R[i] and T[i] can be represented by 1 word, with the binary
;   point to the right of bit 31; Q[i+1] requires two words, with the trial
;   subtraction being performed on the top word only.
;
; For 30 <= i < 62: R[i] can be represented by 2 words, with the binary point
;   to the right of bit 31 of the top word (strictly, the low word isn't
;   required for R[30]); T[i] can be represented by 1 word, now with an
;   implicit word of zeros above it and the binary point to the right of bit
;   31 of this implicit word; Q[i+1] still requires two words, with the trial
;   subtraction occurring on both words;
;
; For i=62: R[i] can be represented by 2 words, with the binary point to the
;   right of bit 31 of the top word; T[i] can be represented by 1 word, now
;   with two implicit words of zeros above it and the binary point to the
;   right of bit 31 of the more significant of the two words; Q[i+1] still
;   contains two words, but a third word is required for the trial
;   subtraction.
;
; For i=63: R[i] now requires 3 words, with the binary point to the right of
;   bit 31 of the most significant word; T[i] can be represented by 1 word,
;   now with two implicit words of zeros above it and the binary point to
;   the right of bit 31 of the more significant of the two words; Q[i+1] will
;   require 3 words to represent it, with the trial subtraction occurring on
;   all three words.
;
; So we will actually perform the square root in 5 stages:
;
; (A) Initialisation and iterations with 0 <= i < 30. Terminated after i=23
;     for single precision.
; (B) Iterations with 30 <= i < 62. Terminated after i=52 for double
;     precision, not done at all for single precision.
; (C) Iteration with i=62. Only done for extended precision.
; (D) Iteration with i=63. Only done for extended precision.
; (E) Sticky bit construction. Done separately for single/double and
;     extended precisions.
;
; Register usage:
;   OP1mhi, OP1mlo: R[i] (the root so far); Rarith is also involved in this
;     at the end of the i=63 iteration.
;   OP2mhi, OP2mlo: Q[i] (the shifted partial remainder).
;   Rarith: temporary register.
;   Rtmp: T[i] (the travelling bit);
;   Rtmp2: loop counter.

; Initialise remainder (Q[0] for odd exponent, Q[1] for even exponent)

        SUBCC   OP2mhi,OP1mhi,#TopBit   ;Subtract 1 for even exponent
        SUBCS   OP2mhi,OP1mhi,#TopBit:SHR:1 ;Shift left, subtract 1 and shift
                                            ; right for odd exponent
        MOV     OP2mlo,OP1mlo           ;Bottom word is unaffected either way

; Initialise travelling bit. Due to the loop unwinding below, we actually
; want T[0] for an odd exponent, T[1] << 1 for an even exponent: both of
; these are 2^(-2).

        MOV     Rtmp,#TopBit:SHR:2

; Initialise result - both R[1] = 1.0 for even exponents and R[0] = 1 for
; odd exponents require the same bit pattern.

        MOV     OP1mhi,#TopBit
        MOV     OP1mlo,#0

; Initialise the loop counter. This is a bit esoteric: it contains minus the
; number of times the first loop below is executed in its top four bits,
; plus the number of times the second loop is exceuted in its bottom 4 bits.
; The idea is that the first loop adds 1 << 28 to it until it becomes
; positive, then the second subtracts one from it until it becomes zero.
;   This is the only time we actually need to look at the precision bits in
; the instruction!
;   Note that we must take great care not to change the C flag in this code.

 [ FPEWanted :LOR: FPASCWanted

        MOV     Rtmp2,#((-5):SHL:28) + 8        ;Correct value for extended
        [ Pr1_mask < &100                       ;I.e. if immediate won't set C
          TST     Rins,#Pr1_mask                ;Z := 1 if single/double
        |
          MOV     Rarith,Rins,LSR #Pr1_pos
          TST     Rarith,#(Pr1_mask:SHR:Pr1_pos)
        ]
        MOVEQ   Rtmp2,#((-5):SHL:28) + 6        ;Correct value for double
        [ Pr2_mask < &100                       ;I.e. if immediate won't set C
          TSTEQ   Rins,#Pr2_mask                ;Z := 1 if single
        |
          MOVEQ   Rarith,Rins,LSR #Pr2_pos
          TSTEQ   Rarith,#(Pr2_mask:SHR:Pr2_pos)
        ]
        MOVEQ   Rtmp2,#((-4):SHL:28) + 0        ;Correct value for single

 |

; Single precision square root is not allowed. Extended is though.

        [ Double_mask < &100
          TST   Rins,#Double_mask
        |
          MOV   Rarith,Rins,LSR #Double_pos
          TST   Rarith,#(Double_mask:SHR:Double_pos)
        ]
        MOVEQ   Rtmp2,#((-5):SHL:28) + 8
        MOVNE   Rtmp2,#((-5):SHL:28) + 6
 ]

; We now require the iterations with 0 <= i < 30 to be done - i.e.:
;
;   23 iterations for single precision, even exponent (1<=i<=23);
;   24 iterations for single precision, odd exponent (0<=i<=23);
;   29 iterations for double/extended precision, even exponent (1<=i<=29);
;   30 iterations for double/extended precision, odd exponent (0<=i<=29).
;
; We unwind this loop to produce 6 copies of the code, and branch in after
; the first one for even exponents.

        BCC     Sqrt_Loop1A

Sqrt_Loop1

; First copy of code

        ADDS    OP2mlo,OP2mlo,OP2mlo    ;Get Q[i] << 1 - note top bit goes
        ADCS    OP2mhi,OP2mhi,OP2mhi    ; into C

        ORR     Rarith,OP1mhi,Rtmp      ;And R[i] + T[i] - note no overlap
        CMPCC   OP2mhi,Rarith           ;Trial subtraction - always works
                                        ; if (Q[i] << 1) >= 2.
        SUBCS   OP2mhi,OP2mhi,Rarith    ;Do real subtraction if trial works
        ORRCS   OP1mhi,OP1mhi,Rtmp,LSL #1 ;Put 1 in result if trial works

Sqrt_Loop1A

; Second copy of code - similar to first copy except we use Rtmp >> 1
; instead of Rtmp.

        ADDS    OP2mlo,OP2mlo,OP2mlo
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ORR     Rarith,OP1mhi,Rtmp,LSR #1
        CMPCC   OP2mhi,Rarith
        SUBCS   OP2mhi,OP2mhi,Rarith
        ORRCS   OP1mhi,OP1mhi,Rtmp

; Third copy of code - similar to first copy except we use Rtmp >> 2
; instead of Rtmp.

        ADDS    OP2mlo,OP2mlo,OP2mlo
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ORR     Rarith,OP1mhi,Rtmp,LSR #2
        CMPCC   OP2mhi,Rarith
        SUBCS   OP2mhi,OP2mhi,Rarith
        ORRCS   OP1mhi,OP1mhi,Rtmp,LSR #1

; Fourth copy of code - similar to first copy except we use Rtmp >> 3
; instead of Rtmp.

        ADDS    OP2mlo,OP2mlo,OP2mlo
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ORR     Rarith,OP1mhi,Rtmp,LSR #3
        CMPCC   OP2mhi,Rarith
        SUBCS   OP2mhi,OP2mhi,Rarith
        ORRCS   OP1mhi,OP1mhi,Rtmp,LSR #2

; Fifth copy of code - similar to first copy except we use Rtmp >> 4
; instead of Rtmp.

        ADDS    OP2mlo,OP2mlo,OP2mlo
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ORR     Rarith,OP1mhi,Rtmp,LSR #4
        CMPCC   OP2mhi,Rarith
        SUBCS   OP2mhi,OP2mhi,Rarith
        ORRCS   OP1mhi,OP1mhi,Rtmp,LSR #3

; Sixth copy of code - similar to first copy except we use Rtmp >> 5
; instead of Rtmp.

        ADDS    OP2mlo,OP2mlo,OP2mlo
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ORR     Rarith,OP1mhi,Rtmp,LSR #5
        CMPCC   OP2mhi,Rarith
        SUBCS   OP2mhi,OP2mhi,Rarith
        ORRCS   OP1mhi,OP1mhi,Rtmp,LSR #4

; Now update the travelling bit and loop counter, then loop if required.

        ADDS    Rtmp2,Rtmp2,#1:SHL:28   ;Increment loop counter
        MOV     Rtmp,Rtmp,ROR #6        ;ROR rather than LSR to set up
        BLT     Sqrt_Loop1              ; for next loop.

; If the result is exact at this point, we can obviously return with all the
; remaining fractional bits, the round bit and the sticky bit equal to 0. If
; the result is not exact but the precision is single, we can return with a
; sticky bit of 1. We only continue if the result is inexact and the
; precision is double or extended.

        ORRS    Rarith,OP2mhi,OP2mlo
        CMPNE   Rtmp,#TopBit:SHR:26     ;Will be EQ for single, NE for
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR                   ; double or extended
  ENDIF


; Next, we need to do the iterations with 30 <= i < 62 - i.e.:
;
;   32 iterations for extended precision (30<=i<=61);
;   23 iterations for double precision (30<=i<=52).
;
; This is a bit awkward from the point of view of unwinding the loop, so we
; will instead do 24 iterations for double precision and unwind the loop to
; produce 4 copies of the code. The extra iteration for double precision is
; wasted work but does no harm.

        STMFD   Rsp!,{Rfpsr,Rins,LR}    ;We need a few more registers

Sqrt_Loop2

        ADDS    OP2mlo,OP2mlo,OP2mlo    ;Get Q[i] << 1,
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     LR,LR,LR                ; putting overflow bit into LR[0]

        ORR     Rarith,OP1mlo,Rtmp      ;(OP1mhi,Rarith) := R[i] + T[i]
        SUBS    Rins,OP2mlo,Rarith      ;Do trial subtraction, which
        SBCS    Rfpsr,OP2mhi,OP1mhi
        MOVCCS  LR,LR,LSR #1            ; always works if (Q[i] << 1) >= 2.

        MOVCS   OP2mlo,Rins             ;Use subtraction result if
        MOVCS   OP2mhi,Rfpsr            ; successful
        ORRCS   OP1mlo,OP1mlo,Rtmp,LSL #1  ;And put a 1 in the result
        ORRCS   OP1mhi,OP1mhi,Rtmp,LSR #31 ;(NB Rtmp may be &80000000)

; Second copy of code - similar to first copy except we use Rtmp >> 1 in
; place of Rtmp, and don't need to worry about putting the 1 into OP1mhi.

        ADDS    OP2mlo,OP2mlo,OP2mlo
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     LR,LR,LR
        ORR     Rarith,OP1mlo,Rtmp,LSR #1
        SUBS    Rins,OP2mlo,Rarith
        SBCS    Rfpsr,OP2mhi,OP1mhi
        MOVCCS  LR,LR,LSR #1
        MOVCS   OP2mlo,Rins
        MOVCS   OP2mhi,Rfpsr
        ORRCS   OP1mlo,OP1mlo,Rtmp

; Third copy of code - similar to first copy except we use Rtmp >> 2 in
; place of Rtmp, and don't need to worry about putting the 1 into OP1mhi.

        ADDS    OP2mlo,OP2mlo,OP2mlo
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     LR,LR,LR
        ORR     Rarith,OP1mlo,Rtmp,LSR #2
        SUBS    Rins,OP2mlo,Rarith
        SBCS    Rfpsr,OP2mhi,OP1mhi
        MOVCCS  LR,LR,LSR #1
        MOVCS   OP2mlo,Rins
        MOVCS   OP2mhi,Rfpsr
        ORRCS   OP1mlo,OP1mlo,Rtmp,LSR #1

; Fourth copy of code - similar to first copy except we use Rtmp >> 3 in
; place of Rtmp, and don't need to worry about putting the 1 into OP1mhi.

        ADDS    OP2mlo,OP2mlo,OP2mlo
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     LR,LR,LR
        ORR     Rarith,OP1mlo,Rtmp,LSR #3
        SUBS    Rins,OP2mlo,Rarith
        SBCS    Rfpsr,OP2mhi,OP1mhi
        MOVCCS  LR,LR,LSR #1
        MOVCS   OP2mlo,Rins
        MOVCS   OP2mhi,Rfpsr
        ORRCS   OP1mlo,OP1mlo,Rtmp,LSR #2

; Now update the travelling bit and loop counter, then loop if required.

        SUBS    Rtmp2,Rtmp2,#1          ;Decrement loop counter
        MOV     Rtmp,Rtmp,ROR #4        ;ROR rather than LSR to set up
        BNE     Sqrt_Loop2              ; for last couple of iterations.

; If the remainder is zero at this point, we've got an exact result: the
; last fractional bit, the round bit and the sticky bit must all be zero.
;   Otherwise, we know that the result will *not* be exact, since each of
; the last two iterations either doesn't change the partial remainder (thus
; leaving it non-zero) or subtracts a value with a 1 in a less significant
; bit than the lowest bit currently in the partial remainder, which must
; leave it non-zero.
;   So we can now return if either the result is currently exact or if it is
; inexact and the precision is double, taking care to make Rarith zero in
; the first case and non-zero in the second. We only need to perform the
; rest of the division if the precision is extended and the result is
; currently inexact - which implies that it will also ultimately be inexact
; and thus that the sticky bit is 1.

        ORRS    Rarith,OP2mhi,OP2mlo
        CMPNE   Rtmp,#TopBit:SHR:24     ;Will be EQ for double, NE for
  IF Interworking :LOR: Thumbing
        LDMEQFD Rsp!,{Rfpsr,Rins,LR}    ; extended
        BXEQ    LR
  ELSE
        LDMEQFD Rsp!,{Rfpsr,Rins,PC}    ; extended
  ENDIF


; Now we need to get the last fractional bit.

        ADDS    OP2mlo,OP2mlo,OP2mlo    ;Get Q[i] << 1,
        ADCS    OP2mhi,OP2mhi,OP2mhi
        ADC     LR,LR,LR                ; putting overflow bit into LR[0]

        RSBS    Rtmp,Rtmp,#0            ;Do trial subtraction, which
        RSCS    Rins,OP1mlo,OP2mlo
        RSCS    Rfpsr,OP1mhi,OP2mhi
        MOVCCS  LR,LR,LSR #1            ; always works if (Q[i] << 1) >= 2.

        MOVCS   OP2mlo,Rins             ;Use subtraction result if
        MOVCS   OP2mhi,Rfpsr            ; successful
        MOVCC   Rtmp,#0                 ;And forget it if not
        ORRCS   OP1mlo,OP1mlo,#1        ;And put a 1 in the result

; And the round bit.

        MOV     Rarith,#TopBit+1        ;We know sticky bit is 1 - assume
                                        ; round bit is also 1

        ADDS    Rtmp,Rtmp,Rtmp          ;Get Q[i] << 1.
        ADCS    OP2mlo,OP2mlo,OP2mlo
        ADCS    OP2mhi,OP2mhi,OP2mhi
  IF Interworking :LOR: Thumbing
        LDMCSFD Rsp!,{Rfpsr,Rins,LR}    ;If >= 2, round bit must be 1
        BXCS    LR
  ELSE
        LDMCSFD Rsp!,{Rfpsr,Rins,PC}    ;If >= 2, round bit must be 1
  ENDIF

                                        ;Omit low word of trial subtraction
                                        ; - we know it will borrow and thus
                                        ; leave C=0. But C=0 here anyway!
        SBCS    Rins,OP2mlo,OP1mlo      ;Do rest of trial subtraction
        SBCS    Rins,OP2mhi,OP1mhi
        MOVCC   Rarith,#1               ;If it fails, round=0, sticky=1
  IF Interworking :LOR: Thumbing
        LDMFD   Rsp!,{Rfpsr,Rins,LR}
        BX      LR
  ELSE
        LDMFD   Rsp!,{Rfpsr,Rins,PC}
  ENDIF

        ]                               ; Conditional compilation of sqrt

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted

; Routine to do a move/move negated/absolute value of an internal format
; floating point number. It has the usual pair of entry points, one
; optimised for the FPASC, the other for the FPE.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;   This routine will not work correctly with an input which is an
; unnormalised URD result, or an invalid internal format number.
;
; Uses standard monadic operation entry and exit conventions - see top of
; this file.
;
; Note that these operations are usually very simple:
;   * Numeric values need their sign bits modified, then to be set up for
;     rounding; note that in the process, uncommon numeric values need to be
;     converted to zeros or normalised numbers to ensure that the rounding
;     works;
;   * Infinities and quiet NaNs need their sign bits modified;
;   * Signalling NaNs just need their sign bits modified if no change of
;     format is involved (what this means depends on the state of the FPSR
;     NE bit); if a change of format is required, they should generate the
;     usual invalid operation exception.

        [ FPEWanted

MoveFPE

        CDebug3 3,"MoveFPE: operand =",OP1sue,OP1mhi,OP1mlo

; If the value is common, it's a numeric value and there's no problem.

        TST     OP1sue,#Uncommon_bit
        BNE     Move_Uncommon

; Split out the exponent.

        AND     RNDexp,OP1sue,#ToExp_mask

        ]

Move_Numeric

; Isolate sign bit and clear uncommon bit. Also set Rarith to 0, since all
; rounding information is completely contained in OP1mhi and OP1mlo.

        AND     OP1sue,OP1sue,#Sign_bit
        MOV     Rarith,#0

Move_DoSigns

; Do the sign manipulations and return.

        TST     Rins,#MNF_bit
        EORNE   OP1sue,OP1sue,#Sign_bit
        TST     Rins,#ABS_bit
        BICNE   OP1sue,OP1sue,#Sign_bit
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]                               ; Conditional assembly of Move

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted

; Routine to do a NRM instruction on an internal format floating point
; number. It has the usual pair of entry points, one optimised for the
; FPASC, the other for the FPE.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;
; Uses standard monadic operation entry and exit conventions - see top of
; this file.
;
; This operation is very similar to MVF, except that we have to cater for
; unnormalised values with the uncommon bit equal to zero - i.e. an URD
; result.

        [ FPEWanted

NormFPE

        CDebug3 3,"NormFPE: operand =",OP1sue,OP1mhi,OP1mlo

; Split according to whether the value is common or uncommon.

        TST     OP1sue,#Uncommon_bit
        BNE     Norm_Uncommon

; Split out the exponent.

        AND     RNDexp,OP1sue,#ToExp_mask

; If the units bit is clear, it's either a URD result or a zero. URD results
; can be treated just like extended unnormalised numbers and zeros.

        TST     OP1mhi,#EIUnits_bit
        BNE     Norm_Numeric

        ]

Norm_ZeroUnnormOrDenorm

; The value is an uncommon numeric value - i.e. a denormalised number, an
; extended unnormalised number or an extended unnormalised zero - or a
; proper zero or a URD result, which may be treated like an extended
; unnormalised number or zero. If it's any sort of zero, change it to a real
; zero and treat it as a numeric.

        ORRS    Rtmp,OP1mhi,OP1mlo
        MOVEQ   RNDexp,#0
        BEQ     Norm_Numeric

; The operand is now a denormalised number or extended unnormalised non-zero
; number. We will change it into the corresponding normalised number
; (possibly with a negative biased exponent), then treat it as a numeric.
;   The types of numbers that require converting are extended unnormalised
; numbers and denormalised numbers of all precisions. In the case of the
; extended denormalised and unnormalised numbers, this just requires us to
; normalise them; in the case of the single and double denormalised numbers,
; we need to clear their units bits and add 1 to their exponents before we
; normalise them.
;   At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have uncommon = units =
; 1: all other numbers with this property are NaNs or infinities and have
; been dealt with already.

        STMFD   Rsp!,{LR}       ;We will have subroutine calls below

        ANDS    Rarith,OP1mhi,OP1sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP1mhi,OP1mhi,#EIUnits_bit
        ADDMI   RNDexp,RNDexp,#1

        BL      $NormaliseOp1_str       ;NB must be necessary, so no
                                        ; point in checking whether
                                        ; normalised

        LDMFD   Rsp!,{LR}

Norm_Numeric

; Isolate sign bit and clear uncommon bit. Also set Rarith to 0, since all
; rounding information is completely contained in OP1mhi and OP1mlo.

        AND     OP1sue,OP1sue,#Sign_bit
        MOV     Rarith,#0
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]                               ; Conditional assembly of Norm

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted

; Routine to do a URD instruction on an internal format floating point
; number. There are the usual two entry points.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard monadic operation entry and exit conventions - see top of
; this file.

        [ FPEWanted

UrdFPE

        CDebug3 3,"UrdFPE: operand =",OP1sue,OP1mhi,OP1mlo

; Start by splitting between common and uncommon operands.

        TST     OP1sue,#Uncommon_bit
        BNE     Urd_Uncommon

        ]

Urd_Common

; The operand is common. Split OP1sue into sign and biased exponent.

        AND     Rarith,OP1sue,#ToExp_mask
        AND     OP1sue,OP1sue,#Sign_bit

Urd_Numeric

; Calculate shift amount to denormalise the number to put the true binary
; point at the rounding boundary - i.e. to give it an effective unbiased
; exponent of 23, 52 or 63 depending on whether the precision of the
; instruction is single, double or extended.

        MOV     RNDexp,#((EIExp_bias+23):AND:&FF)
        TST     Rins,#Pr2_mask
        MOVNE   RNDexp,#((EIExp_bias+52):AND:&FF)
        TST     Rins,#Pr1_mask
        MOVNE   RNDexp,#((EIExp_bias+63):AND:&FF)
        ORR     RNDexp,RNDexp,#((EIExp_bias+63):AND:&FF00)
        ASSERT  ((EIExp_bias+63):AND:&FF00) = ((EIExp_bias+52):AND:&FF00)
        ASSERT  ((EIExp_bias+63):AND:&FF00) = ((EIExp_bias+23):AND:&FF00)

        SUBS    Rtmp,RNDexp,Rarith
        BLS     Urd_Big

; Denormalise the number to have this unbiased exponent and return.

        Denorm  OP1mhi,OP1mlo,Rarith,Rtmp,Rtmp2,Rtmp
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Urd_Big

; We just need to return the number itself, with rounding bits equal to
; zero.

        MOV     RNDexp,Rarith
        MOV     Rarith,#0
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]                               ; Conditional assembly of Urd

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted

; Routine to do a RND instruction on an internal format floating point
; number. There are the usual two entry points.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard monadic operation entry and exit conventions - see top of
; this file.

        [ FPEWanted
RndFPE
        ]

        [ FPASCWanted
RndFPASC
        ]

        CDebug3 3,"RndFPASC/FPE: operand =",OP1sue,OP1mhi,OP1mlo

; Start by splitting between common and uncommon operands.

        TST     OP1sue,#Uncommon_bit
        BNE     Rnd_Uncommon

Rnd_Common

; The operand is common. Split OP1sue into sign and biased exponent.

        AND     RNDexp,OP1sue,#ToExp_mask
        AND     OP1sue,OP1sue,#Sign_bit

; If the number is a zero, we're done.

        TST     OP1mhi,#EIUnits_bit
        BEQ     Rnd_Exact

Rnd_Numeric

; Find the position of the real binary point.

        MOVNE   Rarith,#((EIExp_bias+63):AND:&FF)
        ORR     Rarith,Rarith,#((EIExp_bias+63):AND:&FF00)
        ASSERT  (EIExp_bias + 63) < &10000

        SUBS    Rtmp,Rarith,RNDexp
        BLE     Rnd_Exact

; The rounding position for an integer - i.e. the real binary point - is now
; Rtmp bits above the bottom of the mantissa. Split according to whether
; this puts the round bit in the low word of the mantissa, the high word of
; the mantissa or above the high word of the mantissa.

        RSBS    Rtmp2,Rtmp,#32
        BLT     Rnd_AboveLowWord

Rnd_LowWord

; Branch out if rounding is exact.

        MOVS    Rtmp,OP1mlo,LSL Rtmp2
        BEQ     Rnd_Exact

; We now know we want to round down if we're rounding to zero, or if we're
; rounding to minus infinity and the number is positive, or if we're
; rounding to plus infinity and the number is negative.

        MOVS    Rtmp,OP1sue,LSL #32-Sign_pos
        TSTCS   Rins,#1:SHL:RM_pos
        TSTCC   Rins,#1:SHL:(RM_pos+1)
        ASSERT  RM_pos < 7              ;So that constants don't disturb C
        BNE     Rnd_LowWord_RoundDown

; If we're not rounding to nearest, we must now be rounding up.

        TST     Rins,#RM_mask
        BNE     Rnd_LowWord_RoundUp
        ASSERT  RM_Nearest = 0

; We're rounding to nearest. Produce the round and sticky bits, then work
; out which way we're rounding.

        ADD     Rtmp,Rtmp2,#1
        MOVS    Rtmp,OP1mlo,LSL Rtmp    ;C<-round, Z<-NOT(sticky)
        BNE     Rnd_LowWord_GotDir      ;Branch if not halfway case

        MOVS    Rtmp,OP1mhi,LSR #1      ;C<-least significant bit, from
        MOVS    Rtmp,OP1mlo,LSL Rtmp2   ; low word unless Rtmp2 is 0.

Rnd_LowWord_GotDir

        BCS     Rnd_LowWord_RoundUp

Rnd_LowWord_RoundDown

        RSB     Rtmp2,Rtmp2,#32         ;Clear all bits below rounding
        MOV     OP1mlo,OP1mlo,LSR Rtmp2 ; boundary
        MOV     OP1mlo,OP1mlo,LSL Rtmp2
        MOV     Rarith,#&40000000       ;And set round=0, sticky=1
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Rnd_LowWord_RoundUp

        RSB     Rtmp2,Rtmp2,#32         ;Set all bits below rounding
        MVN     OP1mlo,OP1mlo,LSR Rtmp2 ; boundary
        MVN     OP1mlo,OP1mlo,LSL Rtmp2
        MOV     Rarith,#&C0000000       ;And set round=1, sticky=1
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Rnd_AboveLowWord

        RSBS    Rtmp2,Rtmp,#64
        BLT     Rnd_AboveMantissa

Rnd_HighWord

; Branch out if rounding is exact.

        ORRS    Rtmp,OP1mlo,OP1mhi,LSL Rtmp2
        BEQ     Rnd_Exact

; We now know we want to round down if we're rounding to zero, or if we're
; rounding to minus infinity and the number is positive, or if we're
; rounding to plus infinity and the number is negative.

        MOVS    Rtmp,OP1sue,LSL #32-Sign_pos
        TSTCS   Rins,#1:SHL:RM_pos
        TSTCC   Rins,#1:SHL:(RM_pos+1)
        ASSERT  RM_pos < 7              ;So that constants don't disturb C
        BNE     Rnd_HighWord_RoundDown

; If we're not rounding to nearest, we must now be rounding up.

        TST     Rins,#RM_mask
        BNE     Rnd_HighWord_RoundUp
        ASSERT  RM_Nearest = 0

; We're rounding to nearest. Produce the round and sticky bits, then work
; out which way we're rounding.

        ADD     Rtmp,Rtmp2,#1
        ORRS    Rtmp,OP1mlo,OP1mhi,LSL Rtmp ;C<-round, Z<-NOT(sticky)
        BNE     Rnd_HighWord_GotDir     ;Branch if not halfway case

        CMP     Rtmp2,#1                ;C<-least significant bit, from
        MOVCSS  Rtmp,OP1mhi,LSL Rtmp2   ; high word unless Rtmp2 is 0.

Rnd_HighWord_GotDir

        BCS     Rnd_HighWord_RoundUp

Rnd_HighWord_RoundDown

        RSB     Rtmp2,Rtmp2,#32         ;Clear all bits below rounding
        MOV     OP1mhi,OP1mhi,LSR Rtmp2 ; boundary
        MOVS    OP1mhi,OP1mhi,LSL Rtmp2
        MOV     OP1mlo,#0
        MOVEQ   RNDexp,#0               ;Exponent must change for 0 result
        MOV     Rarith,#&40000000       ;And set round=0, sticky=1
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Rnd_HighWord_RoundUp

        RSB     Rtmp2,Rtmp2,#32         ;Set all bits below rounding
        MVN     OP1mhi,OP1mhi,LSR Rtmp2 ; boundary
        MVN     OP1mhi,OP1mhi,LSL Rtmp2
        MOV     OP1mlo,#&FFFFFFFF
        MOV     Rarith,#&C0000000       ;And set round=1, sticky=1
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Rnd_AboveMantissa

; The rounding cannot possibly be exact - we must either be rounding down to
; zero or up to one. Furthermore, we know that the round bit is 0 and the
; sticky bit is 1. So we can only be rounding up if we're rounding to plus
; or minus infinity, and the result must be of the correct sign as well.

        EOR     Rtmp,OP1sue,Rins,LSL #31-RM_pos   ;Somewhat tricky code to
        EOR     Rtmp2,OP1sue,Rins,LSL #30-RM_pos  ; establish the above
        BICS    Rtmp,Rtmp,Rtmp2
        BMI     Rnd_UpToOne

Rnd_DownToZero

        MOV     OP1mhi,#0
        MOV     OP1mlo,#0
        MOV     RNDexp,#0
        MOV     Rarith,#&40000000
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Rnd_UpToOne

        MOV     OP1mhi,#&FFFFFFFF
        MOV     OP1mlo,#&FFFFFFFF
        MOV     RNDexp,#(EIExp_bias-1):AND:&FF00
        ORR     RNDexp,RNDexp,#(EIExp_bias-1):AND:&FF
        ASSERT  (EIExp_bias-1) < &10000
        MOV     Rarith,#&C0000000
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Rnd_Exact

; We just need to return the number itself, with rounding bits equal to
; zero.

        MOV     Rarith,#0
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]                               ; Conditional assembly of Rnd

;===========================================================================

        [ :DEF: compare_s :LOR: FPEWanted :LOR: FPASCWanted

; Routine to compare two internal format floating point numbers. It has two
; entry points: "CompareFPE", which has an optimised fast track for common
; vs. common comparisons, and "CompareFPASC", which avoids the test for this
; optimised fast track - since it should never happen. The second entry
; point lies a long way down in the source to avoid addressing constraints.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
; Entry: OP1sue = First operand sign, uncommon, exponent;
;        OP1mhi = First operand mantissa, high word;
;        OP1mlo = First operand mantissa, low word;
;        OP2sue = Second operand sign, uncommon, exponent;
;        OP2mhi = Second operand mantissa, high word;
;        OP2mlo = Second operand mantissa, low word;
;        Rfpsr  = FPSR;
;        Rins   = instruction (needed to discriminate between
;                 CMF/CMFE/CNF/CNFE and for traps);
;        Rwp, Rfp, Rsp hold their usual values;
;        R14    = return link.
; Exit:  Rarith = result NZCV in bits 31:28; other bits zero;
;        OP1sue, OP1mhi, OP1mlo, OP2sue, OP2mhi, OP2mlo, Rtmp, Rtmp2 and R14
;          may be corrupt.
;        Rfpsr may be updated.
;        All other registers preserved.

        [ FPEWanted :LOR: FPLibWanted

CompareFPE

        [ FPLibWanted
__fp_compare
        ]

        CDebug3 3,"CompareFPE: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 3,"            op2 =",OP2sue,OP2mhi,OP2mlo

; Start by detecting the "fast track" case of both operands being common.

        TST     OP1sue,#Uncommon_bit
        TSTEQ   OP2sue,#Uncommon_bit
        BNE     Compare_Uncommon

        ]

Compare_Common

; Start by changing the sign of the second operand if the operation is
; CMF(E). (CNF(E) is easier than CMF(E), basically because addition is
; commutative and subtraction isn't.)

        [ FPEWanted :LOR: FPASCWanted
        TST     Rins,#CompNeg_bit
        EOREQ   OP2sue,OP2sue,#Sign_bit
        |
        EOR     OP2sue,OP2sue,#Sign_bit
        ]

; Both operands are common. We start with a magnitude comparison - life is
; fairly easy if (as is likely) it comes out not equal. In this case, the
; results are:
;
;   Magnitude    Operand 1   Operand 2  |  Result for
;   comparison     sign        sign     |    CNF(E)
;   ------------------------------------+------------
;       >           +           X       |      >
;       >           -           X       |      <
;       <           X           +       |      >
;       <           X           -       |      <

        ExpComp Rtmp,OP1sue,OP2sue,Rtmp2 ;Rtmp := left-aligned op1 exp.
        CMPEQ   OP1mhi,OP2mhi
        CMPEQ   OP1mlo,OP2mlo
        BEQ     Compare_EqualMag
        TEQCS   OP1sue,#0               ;NB does not affect C
        TEQCC   OP2sue,#0
        ASSERT  Sign_pos = 31
        MOVPL   Rarith,#Comp_GT
        MOVMI   Rarith,#Comp_LT
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Compare_EqualMag

; If the operands are equal magnitude, then if they're both zero, the
; results is equality. Otherwise, the result is given by the following
; table:
;
;   Operand 1   Operand 2  |  Result for
;     sign        sign     |    CNF(E)
;   -----------------------+------------
;      +           +       |      >
;      +           -       |      =
;      -           +       |      =
;      -           -       |      <
;
; Of course, since they're equal magnitude, they're both zero if the first
; one is. Note Rtmp still contains a left-aligned operand 1 exponent.

        EORS    Rtmp2,OP1sue,OP2sue     ;Are signs opposite or the same?
        ASSERT  Sign_pos = 31
        MOV     Rarith,#Comp_EQ         ;Result if signs opposite
  IF Interworking :LOR: Thumbing
        BXMI    LR
  ELSE
        MOVMI   PC,LR
  ENDIF
        ORR     Rtmp,Rtmp,OP1mhi        ;Otherwise, are they both zero?
        ORRS    Rtmp,Rtmp,OP1mlo
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR
  ENDIF
        TST     OP1sue,#Sign_bit
        MOVEQ   Rarith,#Comp_GT
        MOVNE   Rarith,#Comp_LT
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]                               ; Conditional assembly of Compare

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted :LOR: :DEF: fix_s :LOR: :DEF: fixu_s

; Routine to FIX an internal format floating point number. There are the
; usual two entry points.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
; Entry: OP1sue = Operand sign, uncommon, exponent;
;        OP1mhi = Operand mantissa, high word;
;        OP1mlo = Operand mantissa, low word;
;        Rfpsr  = FPSR;
;        Rins   = instruction (needed for rounding information and traps);
;        Rwp, Rfp, Rsp hold their usual values;
;        R14    = return link.
; Exit:  Rarith = result value;
;        OP1sue, OP1mhi, OP1mlo, OP2sue, OP2mhi, OP2mlo, Rtmp, Rtmp2 and R14
;          may be corrupt.
;        Rfpsr may be updated.
;        All other registers preserved.

        [ FPEWanted

FixFPE

        CDebug3 3,"FixFPE: operand =",OP1sue,OP1mhi,OP1mlo

; Start by splitting between common and uncommon operands.

        TST     OP1sue,#Uncommon_bit
        BNE     Fix_Uncommon

        ]

        [ :DEF: fix_s
__fp_fix_common
        ]
        [ :DEF: fixu_s
__fp_fixu_common
        ]

Fix_Common

; The operand is common. Split OP1sue into sign and biased exponent.

        AND     Rarith,OP1sue,#ToExp_mask
        [ :LNOT: :DEF: fixu_s
        AND     OP1sue,OP1sue,#Sign_bit
        ]

Fix_Numeric

; Calculate shift amount to denormalise the number to have effective
; unbiased exponent 63 - i.e. to put the true binary point at the rounding
; boundary.

        STMFD   Rsp!,{LR}       ;There may be a subroutine call below

        MOV     RNDexp,#((EIExp_bias+63):AND:&FF00)
        ORR     RNDexp,RNDexp,#((EIExp_bias+63):AND:&FF)
        ASSERT  (EIExp_bias+63) <= &FFFF
        SUBS    Rtmp,RNDexp,Rarith
        BLS     Fix_OutOfRange  ;Deal with massively out of range values

; Now denormalise the number to have this unbiased exponent.

        Denorm  OP1mhi,OP1mlo,Rarith,Rtmp,Rtmp2,Rtmp

; Next, we need to round the result to extended precision.

        [ FPEWanted :LOR: FPASCWanted

        AND     RNDprm,Rins,#RM_mask
        ORR     RNDprm,RNDprm,#2:SHL:(RM_pos+2)
        MOV     RNDdir,#0               ;Result has not been rounded so far
        BL      RoundNum_Extended

        |

; Expanded out rounding code

        MOVS    Rtmp,Rarith,LSL #1      ;C<-round, Z<-"tied case"
        BCC     Fix_NoRounding          ;Skip all rounding code...
        MOVEQS  Rtmp,OP1mlo,LSR #1      ; If "tied" C<-round
        ADDCSS  OP1mlo,OP1mlo,#1        ;Increment low word
        ADDCSS  OP1mlo,OP1mlo,#1        ;If carry out, increment high word
        MOVCS   OP1mhi,#EIUnits_bit     ;If mantissa overflow, adjust
        ADDCS   RNDexp,RNDexp,#1        ; mantissa and exponent

Fix_NoRounding

        ]

        [ :LNOT: :DEF: fixu_s

; Produce the potential result, checking for an out-of-range value.
;   We know at this point that (OP1mhi,OP1mlo) contains the unsigned integer
; result, which is in the range 0 to 2^63, *both ends included*, and that
; OP1sue contains the sign of the result. We first need to apply the sign to
; this value - this is done by some slightly tricky code to avoid branches.
;   Note we cannot tell the difference between a result of +2^63 and -2^63
; after this. This doesn't matter, though - they're both well out of range!

        MOVS    Rtmp,OP1sue,LSL #32-Sign_pos    ;CS if -ve, CC if +ve
        MVNCS   OP1mhi,OP1mhi                   ;If -ve, 1's compl't high
        RSBCSS  OP1mlo,OP1mlo,#0                ; word, 2's compl't low word
        ADDCS   OP1mhi,OP1mhi,#1                ; and do carry if needed

        ]

; The result is now in (OP1mhi,OP1mlo). Check for it being out of range -
; i.e. for its top 33 bits not being all identical.

        TEQ     OP1mhi,OP1mlo,ASR #31
        BNE     Fix_OutOfRange

        [ FPEWanted :LOR: FPASCWanted

        MOV     Rarith,OP1mlo

; The only remaining exception that could occur at this point is an inexact
; result.
;   If the result is exact, we don't want to do anything about the inexact
; exception. If it's inexact and the inexact trap is disabled, we want to
; set the inexact cumulative bit in the FPSR. If it's inexact and the
; inexact trap is enabled, we want to call the trap. We use some tricky
; code to distinguish the three cases in-line.
        
        CMP     RNDdir,#0       ;Leaves CS/EQ if exact, NE if inexact
        MOVNES  Rtmp,Rfpsr,LSR #IXE_pos+1
                                ;Now CS/EQ if exact, CS/NE if inexact &
                                ; trap enabled, CC/NE if inexact & trap
        ASSERT  SysID_FPA <> 0  ; disabled (since SysID non-zero & not
        ASSERT  SysID_FPE <> 0  ; shifted out)
        ASSERT  SysID_pos > IXE_pos
        ORRCC   Rfpsr,Rfpsr,#IXC_bit
        BLHI    InexactTrapForI ;Works because HI = CS/NE

        |

        MOV     OP1sue,#0       ;Signal no error

        ]

  IF Interworking :LOR: Thumbing
        LDMFD   Rsp!,{LR}
        BX      LR
  ELSE
        LDMFD   Rsp!,{PC}
  ENDIF

Fix_OutOfRange

; An out of range FIX produces an invalid operation, with a potential result
; of &7FFFFFFF or &80000000, depending on the sign of the operand.
        
        [ FPEWanted :LOR: FPASCWanted

        LDMFD   Rsp!,{LR}
        MOV     Rarith,#:NOT:TopBit             ;Make &7FFFFFFF
        EOR     Rarith,Rarith,OP1sue,ASR #31    ;Convert to &80000000 if -ve
        MOV     Rtmp,#InvReas_FixRange
        B       InvalidOperation1ForI

        |

        ORR     OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        LDMFD   Rsp!,{LR}
        BX      LR
  ELSE
        LDMFD   Rsp!,{PC}
  ENDIF

        ]

        ]                               ; Conditional assembly of Fix

;===========================================================================

        [ :DEF: addsub_s :LOR: FPEWanted :LOR: FPASCWanted

; The second entry point to the addition/subtraction routine, meant for use
; by the FPASC and without a fast track for common operands.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard dyadic operation entry and exit conventions - see top of
; this file.

        [ FPASCWanted

AddSubFPASC

        CDebug3 3,"AddSubFPASC: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 3,"             op2 =",OP2sue,OP2mhi,OP2mlo

        ]

        [ FPLibWanted
__fp_addsub_uncommon
        ]

AddSub_Uncommon

; We have to do a full addition/subtraction, since either or both of the
; operands may be uncommon. What we will do is:
;
;   (a) Check for NaNs. If found, produce an invalid operation exception and
;       suitable NaN result.
;
;   (b) Check for infinities. If found, the infinity effectively becomes the
;       result, unless both operands are infinities and (after taking
;       account of whether an addition or subtraction is involved) they are
;       effectively of opposite signs.
;
;   (c) If no NaNs or infinities, adjust the operands by replacing all
;       effectively unnormalised numbers by the corresponding normalised or
;       extended denormalised number. Then call AddSub_Common, which will
;       work correctly on zeros, normalised numbers and extended
;       denormalised numbers.
;
; So the first thing we do is check for NaNs and infinities - if we find
; one, we'll generate the result by special case code. Note that we check
; for them together, since they have similar bit patterns.

        TNaNInf Rtmp2,OP2sue,OP2mhi           ;Rtmp2[31] := (op2 is NaN/inf)
        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op1 is NaN/inf)
        BMI     AddSub_NaNInf1
        TST     Rtmp2,#TopBit                   ;Operand 2 NaN or infinity?
        BNE     AddSub_NaNInf2Only

; Now we know there are no NaNs or infinities and therefore no Invalid
; Operation or Divide-By-Zero exceptions - which means we no longer need to
; keep track of exactly what the operands are. Next, we will convert the
; remaining types of numbers to zeros, normalised numbers and extended
; denormalised numbers, which can be dealt with by a call to AddSub_Common
; and one to NormaliseOp1.
;   The types of numbers that require converting are extended unnormalised
; numbers and zeros, and single and double denormalised numbers. In the case
; of the extended unnormalised numbers and zeros, this just requires us to
; normalise them; in the case of the single and double denormalised numbers,
; we need to clear their units bits and add 1 to their exponents before we
; normalise them.
;   At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have uncommon = units =
; 1: all other numbers with this property are NaNs or infinities and have
; been dealt with already.

        STMFD   Rsp!,{LR}       ;We will have subroutine calls below

        ANDS    Rarith,OP1mhi,OP1sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP1mhi,OP1mhi,#EIUnits_bit
        ADDMI   OP1sue,OP1sue,#1:SHL:EIExp_pos
        ANDS    Rarith,OP2mhi,OP2sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP2mhi,OP2mhi,#EIUnits_bit
        ADDMI   OP2sue,OP2sue,#1:SHL:EIExp_pos

; Now we need to normalise all these types of numbers, which now means all
; uncommon numbers except those with exponent 0 (which are extended
; precision denormalised numbers and should be left alone).

        TST     OP1sue,#Uncommon_bit
        Exp2Top Rarith,OP1sue,NE,S      ;Complete test & set up for call
        BLNE    $NormDenormOp1_str
        TST     OP2sue,#Uncommon_bit
        Exp2Top Rarith,OP2sue,NE,S      ;Complete test & set up for call
        BLNE    $NormDenormOp2_str

; Call AddSub_Common to do the addition, then normalise the result if it
; isn't already normalised and isn't zero. (This is necessary because e.g. a
; magnitude sum of two denormalised numbers will only have been shifted 1
; bit by AddSub_Common.)

        BL      AddSub_Common
        TST     OP1mhi,#EIUnits_bit
  IF Interworking :LOR: Thumbing
        LDMNEFD Rsp!,{LR}
        BXNE    LR
  ELSE
        LDMNEFD Rsp!,{PC}
  ENDIF
        ORRS    LR,OP1mhi,OP1mlo
        BLNE    $NormaliseOp1_str
  IF Interworking :LOR: Thumbing
        LDMFD   Rsp!,{LR}
        BX      LR
  ELSE
        LDMFD   Rsp!,{PC}
  ENDIF

AddSub_NaNInf1

; The first operand is a NaN or infinity, the second may be (the top bit of
; Rtmp2 indicates whether it is).

        TST     Rtmp2,#TopBit
        BEQ     AddSub_NaNInf1Only

; Both operands are NaNs or infinities. If both operands are infinities, the
; result is an infinity with their shared sign if they have the same effective
; sign, or an invalid operation if they have opposite effective signs
; ("effective" means after taking ADF/SUF/RSF distinctions into account).
;   If either operand is a NaN, the standard exception/NaN propagation rules
; apply.

        ORR     Rtmp,OP1mlo,OP1mhi,LSL #1       ;Test if both are infinities
        ORR     Rtmp,Rtmp,OP2mlo
        ORRS    Rtmp,Rtmp,OP2mhi,LSL #1
        BNE     $ConvertNaNs_str                ;If not, use shared code
        BiShift EOR,Rtmp,OP2sue,Rins,LSR #SubNotAdd_pos,LSL #Sign_pos
        EORS    Rtmp,Rtmp,OP1sue                ;Check whether signs are
        ASSERT  Sign_pos = 31                   ; effectively same.
        ANDPL   Rtmp,OP1sue,#Sign_bit           ;If so, result is infinity
        BPL     AddSub_InfShared                ; (with op1 sign unless RSF)

        [ FPEWanted :LOR: FPASCWanted

        MOV     Rtmp,#InvReas_MagSubInf         ;If not, it's an invalid
        B       InvalidOperation2ForSDE         ; operation

        |

        ORR     OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

AddSub_NaNInf1Only

; The first operand is a NaN or infinity, the second isn't. The result is:
;   * an invalid operation exception if the first operand is a signalling
;     NaN;
;   * the first operand unchanged if it is a quiet NaN;
;   * the standard infinity if the first operand is an infinity, with its
;     sign determined by that of the first operand and whether the
;     instruction is RSF.

        ORRS    Rtmp,OP1mlo,OP1mhi,LSL #1 ;Is operand a NaN?
        BNE     $ConvertNaN1Of2_str     ;Use standard exception/quiet NaN
                                        ; propagation code if so
        AND     Rtmp,OP1sue,#Sign_bit   ;Make standard infinity with right
        B       AddSub_InfShared        ; sign

AddSub_NaNInf2Only

; The first operand is not a NaN or infinity, the second is. The result is:
;   * an invalid operation exception if the second operand is a signalling
;     NaN;
;   * the second operand unchanged if it is a quiet NaN;
;   * the standard infinity if the second operand is an infinity, with its
;     sign determined by that of the second operand and whether the
;     instruction is SUF.

        ORRS    Rtmp,OP2mlo,OP2mhi,LSL #1 ;Is operand a NaN?
        BNE     $ConvertNaN2Of2_str     ;Use standard exception/quiet NaN
                                        ; propagation code if so
        AND     Rtmp,OP2sue,#Sign_bit   ;Make standard infinity with right
        TST     Rins,#SubNotAdd_bit     ; sign
        EORNE   Rtmp,Rtmp,#Sign_bit
AddSub_InfShared
        TST     Rins,#RSF_bit
        EORNE   Rtmp,Rtmp,#Sign_bit
        [ CoreDebugging = 0
          ADR     OP1sue,Prototype_Infinity
        |
          ADRL    OP1sue,Prototype_Infinity
        ]
        LDMIA   OP1sue,OP1regs
        ORR     OP1sue,OP1sue,Rtmp
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]                               ; Conditional assembly of AddSub

;===========================================================================

        [ :DEF: mul_s :LOR: FPEWanted :LOR: FPASCWanted

; The second entry point to the normal/fast multiplication routine, meant
; for use by the FPASC and without a fast track for common operands.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard dyadic operation entry and exit conventions - see top of
; this file.

        [ FPASCWanted

MultFPASC

        CDebug3 3,"MultFPASC: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 3,"           op2 =",OP2sue,OP2mhi,OP2mlo

        ]

        [ FPLibWanted
__fp_mult_uncommon
        ]

Mult_Uncommon

; We have to do a full multiplication, since either or both of the operands
; may be uncommon. What we will do is:
;
;   (a) Check for NaNs. If found, produce an invalid operation exception and
;       suitable NaN result.
;
;   (b) Check for infinities. If found, the result is an infinity with sign
;       equal to the exclusive-OR of the two operand signs, unless the other
;       operand is a zero, in which case we have an invalid operation.
;
;   (c) Check for zeros. If found, the result is a zero with sign equal to
;       the exclusive-OR of the two operand signs.
;
;   (d) If no NaNs, infinities or zeros, we can transform the problem into
;       that of multiplying together two normalised numbers, though the
;       normalised numbers concerned may have unusual exponents.
;
; So the first thing we do is check for NaNs and infinities - if we find
; one, we'll generate the result by special case code. Note that we check
; for them together, since they have similar bit patterns.

        TNaNInf Rtmp2,OP2sue,OP2mhi           ;Rtmp2[31] := (op2 is NaN/inf)
        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op1 is NaN/inf)
        BMI     Mult_NaNInf1
        TST     Rtmp2,#TopBit                   ;Operand 2 NaN or infinity?
        BNE     Mult_NaNInf2Only

; Now if either operand is a zero, the result is zero. We can detect zeros
; by the mantissa being all zero, since only zeros, some unnormalised URD
; results, extended unnormalised zeros and extended infinities have this
; property, we're assuming the operands are not URD results and we've
; already dealt with extended infinities.

        ORRS    Rtmp,OP1mhi,OP1mlo
        ORRNES  Rtmp,OP2mhi,OP2mlo
        BEQ     Mult_Zero

; Both operands are now normalised numbers, denormalised numbers or extended
; unnormalised non-zero numbers. The first step is to convert all of these
; to normalised numbers, possibly with a negative biased exponent. After
; doing the exponent and sign calculations, we then call Mult_Mantissas to
; complete the calculation.
;   The types of numbers that require converting are extended unnormalised
; numbers and denormalised numbers of all precisions. In the case of the
; extended denormalised and unnormalised numbers, this just requires us to
; normalise them; in the case of the single and double denormalised numbers,
; we need to clear their units bits and add 1 to their exponents before we
; normalise them.
;   At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have uncommon = units =
; 1: all other numbers with this property are NaNs or infinities and have
; been dealt with already.

        ANDS    Rarith,OP1mhi,OP1sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP1mhi,OP1mhi,#EIUnits_bit
        ADDMI   OP1sue,OP1sue,#1:SHL:EIExp_pos
        ANDS    Rarith,OP2mhi,OP2sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP2mhi,OP2mhi,#EIUnits_bit
        ADDMI   OP2sue,OP2sue,#1:SHL:EIExp_pos

        AND     Rtmp,OP1sue,#ToExp_mask
        AND     Rtmp2,OP2sue,#ToExp_mask
        EOR     OP1sue,OP1sue,OP2sue    ;Produce result sign
        AND     OP1sue,OP1sue,#Sign_bit
        ADD     RNDexp,Rtmp,Rtmp2
        SUB     RNDexp,RNDexp,#(EIExp_bias-1):AND:&FF00
        SUB     RNDexp,RNDexp,#(EIExp_bias-1):AND:&FF
        ASSERT  (EIExp_bias-1) < &10000 ;Result exponent if mantissa
                                        ; overflow is exp1+exp2-bias+1

        STMFD   Rsp!,{LR}       ;We will have subroutine calls below

        TST     OP1mhi,#EIUnits_bit
        BLEQ    $NormaliseOp1_str
        TST     OP2mhi,#EIUnits_bit
        BLEQ    $NormaliseOp2_str

        LDMFD   Rsp!,{LR}
        B       Mult_Mantissas

Mult_Zero

; The result is zero.

        EOR     OP1sue,OP1sue,OP2sue    ;Get sign right
        AND     OP1sue,OP1sue,#Sign_bit
        MOV     OP1mhi,#0
        MOV     OP1mlo,#0
        MOV     RNDexp,#0               ;And exponent
        MOV     Rarith,#0               ;And round/sticky bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Mult_NaNInf1

; The first operand is a NaN or infinity, the second may be (the top bit of
; Rtmp2 indicates whether it is).

        TST     Rtmp2,#TopBit
        BEQ     Mult_NaNInf1Only

; Both operands are NaNs or infinities. If both operands are infinities, the
; result is an infinity with sign determined by those of the two operands.
;   If either operand is a NaN, the standard exception/NaN propagation rules
; apply.

        ORR     Rtmp,OP1mlo,OP1mhi,LSL #1       ;Test if both are infinities
        ORR     Rtmp,Rtmp,OP2mlo
        ORRS    Rtmp,Rtmp,OP2mhi,LSL #1
        BNE     $ConvertNaNs_str                ;If not, use shared code
Mult_InfShared
        EOR     Rtmp,OP1sue,OP2sue              ;If so, result is infinity
        AND     Rtmp,Rtmp,#Sign_bit             ; with correct sign
        ADR     OP1sue,Prototype_Infinity
        LDMIA   OP1sue,OP1regs
        ORR     OP1sue,OP1sue,Rtmp
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Mult_NaNInf1Only

; The first operand is a NaN or infinity, the second isn't. The result is:
;   * an invalid operation exception if the first operand is a signalling
;     NaN;
;   * the first operand unchanged if it is a quiet NaN;
;   * an invalid operation exception if the first operand is an infinity and
;     the second is a zero;
;   * the standard infinity if the first operand is an infinity and the
;     second operand is not a zero, with its sign determined by those of the
;     two operands.
; Note that we can detect the second operand being zero by its mantissa
; being all zero, since only zeros, some unnormalised URD results, extended
; unnormalised zeros and extended infinities have this property, we're
; assuming the operands are not URD results and we know the second operand
; isn't an extended infinity.

        ORRS    Rtmp,OP1mlo,OP1mhi,LSL #1 ;Is first operand a NaN?
        BNE     $ConvertNaN1Of2_str     ;Use standard exception/quiet NaN
                                        ; propagation code if so
        ORRS    Rtmp,OP2mhi,OP2mlo      ;Is second operand a zero?
        BNE     Mult_InfShared          ;If not, result is an infinity

        [ FPEWanted :LOR: FPASCWanted

        MOV     Rtmp,#InvReas_InfTimes0 ;Otherwise, an invalid operation
        B       InvalidOperation2ForSDE

        |

        ORR     OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

Mult_NaNInf2Only

; The first operand is not a NaN or infinity, the second is. The result is:
;   * an invalid operation exception if the second operand is a signalling
;     NaN;
;   * the second operand unchanged if it is a quiet NaN;
;   * an invalid operation exception if the first operand is a zero and the
;     second is an infinity;
;   * the standard infinity if the first operand is not a zero and the second
;     operand is an infinity, with its sign determined by those of the two
;     operands.
; Note that we can detect the first operand being zero by its mantissa being
; all zero, since only zeros, some unnormalised URD results, extended
; unnormalised zeros and extended infinities have this property, we're
; assuming the operands are not URD results and we know it isn't an extended
; infinity.

        ORRS    Rtmp,OP2mlo,OP2mhi,LSL #1 ;Is second operand a NaN?
        BNE     $ConvertNaN2Of2_str     ;Use standard exception/quiet NaN
                                        ; propagation code if so
        ORRS    Rtmp,OP1mhi,OP1mlo      ;Is first operand a zero?
        BNE     Mult_InfShared          ;If not, result is an infinity

        [ FPEWanted :LOR: FPASCWanted

        MOV     Rtmp,#InvReas_0TimesInf ;Otherwise, an invalid operation
        B       InvalidOperation2ForSDE

        |

        ORR     OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

        ]

;===========================================================================

        [ :DEF: div_s :LOR: FPEWanted :LOR: FPASCWanted

; The second entry point to the normal/fast division/reverse division
; routine, meant for use by the FPASC and without a fast track for common
; operands.
;   The value returned is either a numeric value plus associated rounding
; information, with the uncommon bit clear, or an infinity or NaN, with the
; uncommon bit set.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard dyadic operation entry and exit conventions - see top of
; this file.

        [ FPASCWanted

DivFPASC

        CDebug3 3,"DivFPASC: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 3,"          op2 =",OP2sue,OP2mhi,OP2mlo

        ]

        [ FPLibWanted
__fp_div_uncommon
__fp_rdv_uncommon
        ]

Div_Uncommon

; We have to do a full division, since either or both of the operands may be
; uncommon. What we will do is:
;
;   (a) Check for NaNs. If found, produce an invalid operation exception and
;       suitable NaN result.
;
;   (b) Check for infinities. If found, the result is:
;         * An invalid operation exception if both operands are infinities;
;         * An infinite result if the dividend is an infinity and the
;           divisor is numeric;
;         * A zero result if the dividend is numeric and the divisor is an
;           infinity;
;
;   (c) Check for zeros. If found, the result is:
;         * An invalid operation exception if both operands are zeros;
;         * A divide-by-zero exception if the dividend is non-zero and the
;           divisor is zero;
;         * A zero if the dividend is zero and the divisor is non-zero.
;
;   (d) If no NaNs, infinities or zeros, we can transform the problem into
;       that of dividing a normalised number by another, though the
;       normalised numbers concerned may have unusual exponents.
;
; So the first thing we do is check for NaNs and infinities - if we find
; one, we'll generate the result by special case code. Note that we check
; for them together, since they have similar bit patterns.

        TNaNInf Rtmp2,OP2sue,OP2mhi           ;Rtmp2[31] := (op2 is NaN/inf)
        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op1 is NaN/inf)
        BMI     Div_NaNInf1
        TST     Rtmp2,#TopBit                   ;Operand 2 NaN or infinity?
        BNE     Div_NaNInf2Only

; Now if either operand is a zero, we need to take special action. We can
; detect zeros by the mantissa being all zero, since only zeros, some
; unnormalised URD results, extended unnormalised zeros and extended
; infinities have this property, we're assuming the operands are not URD
; results and we've already dealt with extended infinities.

        [ FPEWanted :LOR: FPASCWanted

        ORRS    Rtmp,OP1mhi,OP1mlo
        ORRNES  Rtmp,OP2mhi,OP2mlo
        BEQ     Div_Zero

; Both operands are now going to be converted to normalised numbers. We now
; know that we are not going to need to know the operands for trap purposes,
; so we can swap them if this is a normal (rather than reverse) division.

        TST     Rins,#RevDiv_bit
        |
        TST     Rins,#Reverse
        ]
        BNE     Div_Uncommon_Swapped

        MOV     Rtmp,OP1sue
        MOV     OP1sue,OP2sue
        MOV     OP2sue,Rtmp
        MOV     Rtmp,OP1mhi
        MOV     OP1mhi,OP2mhi
        MOV     OP2mhi,Rtmp
        MOV     Rtmp,OP1mlo
        MOV     OP1mlo,OP2mlo
        MOV     OP2mlo,Rtmp

Div_Uncommon_Swapped

; Both operands are now normalised numbers, denormalised numbers or extended
; unnormalised non-zero numbers. The first step is to convert all of these
; to normalised numbers, possibly with a negative biased exponent. After
; doing the exponent and sign calculations, we then call Div_Mantissas to
; complete the calculation.
;   The types of numbers that require converting are extended unnormalised
; numbers and denormalised numbers of all precisions. In the case of the
; extended denormalised and unnormalised numbers, this just requires us to
; normalise them; in the case of the single and double denormalised numbers,
; we need to clear their units bits and add 1 to their exponents before we
; normalise them.
;   At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have uncommon = units =
; 1: all other numbers with this property are NaNs or infinities and have
; been dealt with already.

        ANDS    Rarith,OP1mhi,OP1sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP1mhi,OP1mhi,#EIUnits_bit
        ADDMI   OP1sue,OP1sue,#1:SHL:EIExp_pos
        ANDS    Rarith,OP2mhi,OP2sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP2mhi,OP2mhi,#EIUnits_bit
        ADDMI   OP2sue,OP2sue,#1:SHL:EIExp_pos

        AND     Rtmp,OP1sue,#ToExp_mask
        AND     Rtmp2,OP2sue,#ToExp_mask
        EOR     OP1sue,OP1sue,OP2sue    ;Produce result sign
        AND     OP1sue,OP1sue,#Sign_bit
        SUB     RNDexp,Rtmp2,Rtmp
        ADD     RNDexp,RNDexp,#EIExp_bias:AND:&FF00
        ADD     RNDexp,RNDexp,#EIExp_bias:AND:&FF
        ASSERT  EIExp_bias < &10000     ;Result exponent if no mantissa
                                        ; underflow is exp1-exp2+bias

        STMFD   Rsp!,{LR}       ;We will have subroutine calls below

        TST     OP1mhi,#EIUnits_bit
        BLEQ    $NormaliseOp1Neg_str
        TST     OP2mhi,#EIUnits_bit
        BLEQ    $NormaliseOp2_str

        LDMFD   Rsp!,{LR}
        B       Div_Mantissas

        [ FPEWanted :LOR: FPASCWanted

Div_Zero

; One or both operands are zeros, and both are numeric values (i.e. not NaNs
; or infinities). The result is:
;   * An invalid operation exception if both operands are zeros;
;   * A divide-by-zero exception if the dividend is non-zero and the divisor
;     is zero;
;   * A zero if the dividend is zero and the divisor is non-zero.
;
; Split according to whether this is a normal or reverse division.

        MOV     Rtmp,#InvReas_0Div0     ;The only type of invalid operation
                                        ; that occurs below
        TST     Rins,#RevDiv_bit
        BNE     Div_Zero_Reversed

; It's a normal division - check the three cases above.

        ORRS    Rtmp2,OP1mhi,OP1mlo     ;Check dividend
        BNE     DivideByZero2
        ORRS    Rtmp2,OP2mhi,OP2mlo     ;Check divisor
        BEQ     InvalidOperation2ForSDE

Div_ZeroByX

; The result is zero.

        EOR     OP1sue,OP1sue,OP2sue    ;Get sign right
        AND     OP1sue,OP1sue,#Sign_bit ;Uncommon bit is zero
        MOV     OP1mhi,#0               ;So is mantissa
        MOV     OP1mlo,#0
        MOV     RNDexp,#0               ;And exponent
        MOV     Rarith,#0               ;And round/sticky bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Div_Zero_Reversed

; It's a reverse division - check the three cases above.

        ORRS    Rtmp2,OP1mhi,OP1mlo     ;Check divisor
        BNE     Div_ZeroByX
        ORRS    Rtmp2,OP2mhi,OP2mlo     ;Check dividend
        BNE     DivideByZero2
        B       InvalidOperation2ForSDE

        ]

Div_NaNInf1

; The first operand is a NaN or infinity, the second may be (the top bit of
; Rtmp2 indicates whether it is).

        TST     Rtmp2,#TopBit
        BEQ     Div_NaNInf1Only

; Both operands are NaNs or infinities. If both operands are infinities, the
; result is an invalid operation.
;   If either operand is a NaN, the standard exception/NaN propagation rules
; apply.

        ORR     Rtmp,OP1mlo,OP1mhi,LSL #1       ;Test if both are infinities
        ORR     Rtmp,Rtmp,OP2mlo
        ORRS    Rtmp,Rtmp,OP2mhi,LSL #1
        BNE     $ConvertNaNs_str                ;If not, use shared code

        [ FPEWanted :LOR: FPASCWanted

        MOV     Rtmp,#InvReas_InfDivInf
        B       InvalidOperation2ForSDE

        |

        ORR     OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

Div_NaNInf1Only

; The first operand is a NaN or infinity, the second isn't. The result is:
;   * an invalid operation exception if the first operand is a signalling
;     NaN;
;   * the first operand unchanged if it is a quiet NaN;
;   * a standard infinity with sign equal to the exclusive-OR of the two
;     operand signs if the first operand is an infinity and the instruction
;     is a normal division;
;   * a zero with sign equal to the exclusive-OR of the two operand signs if
;     the first operand is an infinity and the instruction is a reverse
;     division.

        ORRS    Rtmp,OP1mlo,OP1mhi,LSL #1 ;Is first operand a NaN?
        BNE     $ConvertNaN1Of2_str     ;Use standard exception/quiet NaN
                                        ; propagation code if so
        EOR     Rtmp,OP1sue,OP2sue
        AND     Rtmp,Rtmp,#Sign_bit
        [ FPASCWanted :LOR: FPEWanted
        TST     Rins,#RevDiv_bit
        |
        TST     Rins,#Reverse
        ]
        ADREQ   OP1sue,Prototype_Infinity
        ADRNE   OP1sue,Prototype_Zero
        LDMIA   OP1sue,OP1regs
        ORR     OP1sue,OP1sue,Rtmp
        MOV     RNDexp,#0               ;These two are only needed when
        MOV     Rarith,#0               ; result is zero
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Div_NaNInf2Only

; The first operand is not a NaN or infinity, the second is. The result is:
;   * an invalid operation exception if the second operand is a signalling
;     NaN;
;   * the second operand unchanged if it is a quiet NaN;
;   * a standard infinity with sign equal to the exclusive-OR of the two
;     operand signs if the first operand is an infinity and the instruction
;     is a reverse division;
;   * a zero with sign equal to the exclusive-OR of the two operand signs if
;     the first operand is an infinity and the instruction is a normal
;     division.

        ORRS    Rtmp,OP2mlo,OP2mhi,LSL #1 ;Is second operand a NaN?
        BNE     $ConvertNaN2Of2_str     ;Use standard exception/quiet NaN
                                        ; propagation code if so

        EOR     Rtmp,OP1sue,OP2sue
        AND     Rtmp,Rtmp,#Sign_bit
        [ FPEWanted :LOR: FPASCWanted
        TST     Rins,#RevDiv_bit
        |
        TST     Rins,#Reverse
        ]
        ADRNE   OP1sue,Prototype_Infinity
        ADREQ   OP1sue,Prototype_Zero
        LDMIA   OP1sue,OP1regs
        ORR     OP1sue,OP1sue,Rtmp
        MOV     RNDexp,#0               ;These two are only needed when
        MOV     Rarith,#0               ; result is zero
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

;===========================================================================

        [ :DEF: fmod_s :LOR: FPEWanted :LOR: FPASCWanted

; The second part of the IEEE remainder function.

Rem_Uncommon

; One or both of the operands may be uncommon. What we will do is:
;
;   (a) Check for NaNs. If found, produce an invalid operation exception and
;       suitable NaN result.
;
;   (b) Check for infinities. If found, the result is:
;         * An invalid operation exception if the first operand is an
;           infinity.
;         * Equal to the first operand if the second operand is an infinity
;           and the first isn't.
;
;   (c) Check for zeros. If found, the result is:
;         * An invalid operation exception if the second operand is a zero;
;         * Equal to the first operand if the first operand is a zero and
;           the second isn't;
;
;   (d) If no NaNs, infinities or zeros, we can transform the problem into
;       that of doing the remainder of one normalised number by another,
;       though the normalised numbers concerned may have unusual exponents.
;
; So the first thing we do is check for NaNs and infinities - if we find
; one, we'll generate the result by special case code. Note that we check
; for them together, since they have similar bit patterns.

        TNaNInf Rtmp2,OP2sue,OP2mhi           ;Rtmp2[31] := (op2 is NaN/inf)
        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op1 is NaN/inf)
        BMI     Rem_NaNInf1
        TST     Rtmp2,#TopBit                   ;Operand 2 NaN or infinity?
        BNE     Rem_NaNInf2Only

; Now if the second operand is a zero, we've got an invalid operation, and
; if it isn't but the first operand is, we've got a result equal to the
; first operand. We can detect zeros by the mantissa being all zero, since
; only zeros, some unnormalised URD results, extended unnormalised zeros and
; extended infinities have this property, we're assuming the operands are
; not URD results and we've already dealt with extended infinities.

        ORRS    Rtmp,OP2mhi,OP2mlo

        [ FPEWanted :LOR: FPASCWanted

        MOVEQ   Rtmp,#InvReas_XRem0
        BEQ     InvalidOperation2ForSDE

        |

        ORREQ   OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR
  ENDIF

        ]

        ORRS    Rarith,OP1mhi,OP1mlo
        BEQ     Rem_FirstOperand_Zero

; Both operands may now be forced to be normalised numbers - after we've
; dealt with signs and exponents, we can rejoin the main code.
;   The types of numbers that require converting are extended unnormalised
; numbers and denormalised numbers of all precisions. In the case of the
; extended denormalised and unnormalised numbers, this just requires us to
; normalise them; in the case of the single and double denormalised numbers,
; we need to clear their units bits and add 1 to their exponents before we
; normalise them.
;   At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have uncommon = units =
; 1: all other numbers with this property are NaNs or infinities and have
; been dealt with already.

        ANDS    Rarith,OP1mhi,OP1sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP1mhi,OP1mhi,#EIUnits_bit
        ADDMI   OP1sue,OP1sue,#1:SHL:EIExp_pos
        ANDS    Rarith,OP2mhi,OP2sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP2mhi,OP2mhi,#EIUnits_bit
        ADDMI   OP2sue,OP2sue,#1:SHL:EIExp_pos

        STMFD   Rsp!,{LR}       ;We will have subroutine calls below

        AND     RNDexp,OP2sue,#ToExp_mask       ;Raw second operand exponent
        TST     OP2mhi,#EIUnits_bit             ;Normalise second operand,
        BLEQ    $NormaliseOp2_str               ; then adjust to get
        SUB     Rtmp2,RNDexp,#1                 ; prospective result exp.

        AND     RNDexp,OP1sue,#ToExp_mask       ;Raw first operand exponent
        TST     OP2mhi,#EIUnits_bit             ;Normalise first operand
        BLEQ    $NormaliseOp1_str               ; then determine the number
        SUBS    Rarith,RNDexp,Rtmp2             ; of iterations - 1
        MOV     RNDexp,Rtmp2                    ;Get prospective result exp.
                                                ; back where it's wanted

; All the special exponent handling is done, so we might as well rejoin the
; main code.

        B       Rem_ExponentsDone

Rem_NaNInf1

; The first operand is a NaN or infinity, the second may be (the top bit of
; Rtmp2 indicates whether it is).

        TST     Rtmp2,#TopBit
        BEQ     Rem_NaNInf1Only

; Both operands are NaNs or infinities. If both operands are infinities, the
; result is an invalid operation.
;   If either operand is a NaN, the standard exception/NaN propagation rules
; apply.

        ORR     Rtmp,OP1mlo,OP1mhi,LSL #1       ;Test if both are infinities
        ORR     Rtmp,Rtmp,OP2mlo
        ORRS    Rtmp,Rtmp,OP2mhi,LSL #1
        BNE     $ConvertNaNs_str                ;If not, use shared code
        
        [ FPEWanted :LOR: FPASCWanted

        MOV     Rtmp,#InvReas_InfRemX
        B       InvalidOperation2ForSDE

        |

        ORR     OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

Rem_NaNInf1Only

; The first operand is a NaN or infinity, the second isn't. The result is:
;   * an invalid operation exception if the first operand is a signalling
;     NaN;
;   * the first operand unchanged if it is a quiet NaN;
;   * an invalid operation if it is an infinity.

        ORRS    Rtmp,OP1mlo,OP1mhi,LSL #1 ;Is first operand a NaN?
        BNE     $ConvertNaN1Of2_str     ;Use standard exception/quiet NaN
                                        ; propagation code if so
        
        [ FPEWanted :LOR: FPASCWanted

        MOV     Rtmp,#InvReas_InfRemX
        B       InvalidOperation2ForSDE

        |

        ORR     OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

Rem_NaNInf2Only

; The first operand is not a NaN or infinity, the second is. The result is:
;   * an invalid operation exception if the second operand is a signalling
;     NaN;
;   * the second operand unchanged if it is a quiet NaN;
;   * equal to the first operand if the second operand is an infinity.

        ORRS    Rtmp,OP2mlo,OP2mhi,LSL #1 ;Is second operand a NaN?
        BNE     $ConvertNaN2Of2_str     ;Use standard exception/quiet NaN
                                        ; propagation code if so

Rem_FirstOperand

; If the first operand is common, life is easy.

        TST     OP1sue,#Uncommon_bit
        ANDEQ   RNDexp,OP1sue,#ToExp_mask
        ANDEQ   OP1sue,OP1sue,#Sign_bit
        MOVEQ   Rarith,#0
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR
  ENDIF

; If it's uncommon, life is trickier. First check for zeros.

        ORRS    Rarith,OP1mhi,OP1mlo
        BEQ     Rem_FirstOperand_Zero

; The operand is now a denormalised number or extended unnormalised non-zero
; number; it needs conversion to an internal precision number. In the case
; of the extended denormalised and unnormalised numbers, this just requires
; us to normalise them; in the case of the single and double denormalised
; numbers, we need to clear their units bits and add 1 to their exponents
; before we normalise them.
;
; At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have a units bit of 1:
; all other uncommon numbers with this property are NaNs or infinities and
; have been dealt with already.

        AND     RNDexp,OP1sue,#ToExp_mask ;Extract operand exponent
        AND     OP1sue,OP1sue,#Sign_bit   ; and its sign

        TST     OP1mhi,#EIUnits_bit
        BICNE   OP1mhi,OP1mhi,#EIUnits_bit
        ADDNE   RNDexp,RNDexp,#1

        MOV     Rarith,#0               ;Result is exact.
        B       $NormaliseOp1_str       ;NB must be necessary, so no
                                        ; point in checking whether
                                        ; normalised

Rem_FirstOperand_Zero

        AND     OP1sue,OP1sue,#Sign_bit
        MOV     RNDexp,#0               ;We already know OP1mhi, OP1mlo and
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR                   ; Rarith are zero
  ENDIF

        ]

;===========================================================================

Prototype_Zero
        DCD     &00000000,&00000000,&00000000

Prototype_Infinity
        DCD     &40007FFF,&00000000,&00000000

;===========================================================================

        [ :DEF: sqrt_s :LOR: FPEWanted :LOR: FPASCWanted

; The second part of the square root routine, which deals with uncommon
; operands.

        [ FPLibWanted
__fp_sqrt_uncommon
        ]

Sqrt_Uncommon

; We have to deal with the square root of an uncommon value. The cases are:
;
;   * The square root of a signalling NaN is an invalid operation;
;
;   * The square root of a quiet NaN is the NaN itself;
;
;   * The square root of plus infinity is plus infinity;
;
;   * The square root of minus infinity is an invalid operation;
;
;   * The square root of an extended unnormalised zero is a zero of the same
;     sign;
;
;   * The square roots of denormalised numbers and extended unnormalised
;     numbers can be determined by transforming them into normalised numbers
;     (possibly with an out-of-range exponent), then using the standard
;     square root code above.
;
; So the first thing we do is check for NaNs and infinities - if we find
; one, we'll generate the result by special case code. Note that we check
; for them together, since they have similar bit patterns.

        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op is NaN/inf)
        BMI     Sqrt_NaNInf

; Now if the operand is a zero, the result is a zero of the same sign. We
; can detect zeros by the mantissa being all zero, since only zeros, some
; unnormalised URD results, extended unnormalised zeros and extended
; infinities have this property, we're assuming the operand is not a URD
; result and we've already dealt with extended infinities.

        ORRS    Rtmp,OP1mhi,OP1mlo
        ANDEQ   OP1sue,OP1sue,#Sign_bit
        BEQ     Sqrt_Zero

; The operand is now a denormalised number or extended unnormalised non-zero
; number. If it is negative, we've got an invalid operation. Otherwise, we
; know that no invalid operation or divide-by-zero exception is going to
; occur, so we can convert it to a normalised number, possibly with a
; negative biased exponent. After doing the exponent and sign calculations,
; we then call Sqrt_Mantissa to complete the calculation.
;   The types of numbers that require converting are extended unnormalised
; numbers and denormalised numbers of all precisions. In the case of the
; extended denormalised and unnormalised numbers, this just requires us to
; normalise them; in the case of the single and double denormalised numbers,
; we need to clear their units bits and add 1 to their exponents before we
; normalise them.
;   At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have a units bit of 1:
; all other numbers with this property are NaNs or infinities and have
; been dealt with already.

        AND     RNDexp,OP1sue,#ToExp_mask ;Extract operand exponent

        ANDS    OP1sue,OP1sue,#Sign_bit
        
        [ FPEWanted :LOR: FPASCWanted

        MOVNE   Rtmp,#InvReas_SqrtNeg
        BNE     InvalidOperation1ForSDE

        |

        ORRNE   OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

        STMFD   Rsp!,{LR}       ;We will have subroutine calls below

        TST     OP1mhi,#EIUnits_bit
        BICNE   OP1mhi,OP1mhi,#EIUnits_bit
        ADDNE   RNDexp,RNDexp,#1

        BL      $NormaliseOp1_str       ;NB must be necessary, so no
                                        ; point in checking whether
                                        ; normalised

        ADD     RNDexp,RNDexp,#EIExp_bias:AND:&FF00
        ADD     RNDexp,RNDexp,#EIExp_bias:AND:&FF
        ASSERT  (EIExp_bias-1) < &10000 ;Result exponent if mantissa
                                        ; overflow is (exp+bias) DIV 2
        MOVS    RNDexp,RNDexp,LSR #1

        LDMFD   Rsp!,{LR}
        B       Sqrt_Mantissa

Sqrt_Zero

; The result is equal to the operand, which is a zero.

        MOV     RNDexp,#0               ;Clear exponent
        MOV     Rarith,#0               ;And round/sticky bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Sqrt_NaNInf

; The operand is a NaN or infinity. If it's a NaN, we use the standard
; rules for propagating NaNs. If an infinity, we've got an invalid operation
; if it is negative and a result equal to the standard plus infinity if it
; is positive.

        ORRS    Rtmp,OP1mlo,OP1mhi,LSL #1 ;Is operand a NaN?
        BNE     $ConvertNaN1_str             ;Use standard exception/quiet NaN
                                        ; propagation code if so
        TST     OP1sue,#Sign_bit

        [ FPEWanted :LOR: FPASCWanted

        MOVNE   Rtmp,#InvReas_SqrtNeg
        BNE     InvalidOperation1ForSDE

        ADR     OP1sue,Prototype_Infinity
        LDMIA   OP1sue,OP1regs

        |

        ORRNE   OP1sue,OP1sue,#IVO_bits
        ADREQ   OP1sue,Prototype_Infinity
        LDMEQIA OP1sue,OP1regs

        ]

  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted

; The second entry point to the move/move negated/absolute value routine,
; meant for use by the FPASC.
;   This routine will not work correctly with an input which is an
; unnormalised URD result, or an invalid internal format number.
;
; Uses standard monadic operation entry and exit conventions - see top of
; this file.

        [ FPASCWanted

MoveFPASC

        CDebug3 3,"MoveFPASC: operand =",OP1sue,OP1mhi,OP1mlo

; The FPA does not bounce common values in the Prepare stage for these
; instructions, so no need to check the uncommon bit.

        ]

Move_Uncommon

; Only uncommon values will get here. First split out NaNs and infinities.

        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op is NaN/inf)
        BMI     Move_NaNInf

; The value is an uncommon numeric value - i.e. a denormalised number, an
; extended unnormalised number or an extended unnormalised zero. If it's the
; last of these, change it to a real zero and treat it as a numeric.

        ORRS    Rtmp,OP1mhi,OP1mlo
        MOVEQ   RNDexp,#0
        BEQ     Move_Numeric

; The operand is now a denormalised number or extended unnormalised non-zero
; number. We will change it into the corresponding normalised number
; (possibly with a negative biased exponent), then treat it as a numeric.
;   The types of numbers that require converting are extended unnormalised
; numbers and denormalised numbers of all precisions. In the case of the
; extended denormalised and unnormalised numbers, this just requires us to
; normalise them; in the case of the single and double denormalised numbers,
; we need to clear their units bits and add 1 to their exponents before we
; normalise them.
;   At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have uncommon = units =
; 1: all other numbers with this property are NaNs or infinities and have
; been dealt with already.

        AND     RNDexp,OP1sue,#ToExp_mask
        ASSERT  EIExp_pos = 0

        STMFD   Rsp!,{LR}       ;We will have subroutine calls below

        ANDS    Rarith,OP1mhi,OP1sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP1mhi,OP1mhi,#EIUnits_bit
        ADDMI   RNDexp,RNDexp,#1

        BL      $NormaliseOp1_str       ;NB must be necessary, so no
                                        ; point in checking whether
                                        ; normalised

        LDMFD   Rsp!,{LR}
        B       Move_Numeric

Move_NaNInf

; The operand is a NaN or infinity. If it's an infinity, we just want to
; perform the standard sign manipulations on it and return a standard
; infinity. If it's a NaN, we need to pay attention to the implicit IEEE
; format conversion.

        ORRS    Rtmp,OP1mlo,OP1mhi,LSL #1 ;Is operand a NaN?
        BNE     Move_NaN
        AND     Rtmp,OP1sue,#Sign_bit   ;Isolate sign
        TST     Rins,#MNF_bit           ;Do sign manipulations
        EORNE   Rtmp,Rtmp,#Sign_bit
        TST     Rins,#ABS_bit
        BICNE   Rtmp,Rtmp,#Sign_bit
        ADR     OP1sue,Prototype_Infinity
        LDMIA   OP1sue,OP1regs
        ORR     OP1sue,OP1sue,Rtmp
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

Move_NaN

        STMFD   Rsp!,{LR}
        BL      NaNConversionNeeded
        TEQ     Rarith,#0               ;Conversion needed?
        BMI     Move_NaN_DoSigns        ;Just alter signs if not
        BL      ConvertNaN1_Special     ;Do correct NaN conversion
  IF Interworking :LOR: Thumbing
        LDMNEFD Rsp!,{LR}               ;We're done and must *not* alter
                                        ; signs if an invalid operation trap
                                        ; occurred
        BXNE    LR
  ELSE
        LDMNEFD Rsp!,{PC}               ;We're done and must *not* alter
                                        ; signs if an invalid operation trap
                                        ; occurred
  ENDIF

Move_NaN_DoSigns

; Do the sign manipulations and return.

        TST     Rins,#MNF_bit
        EORNE   OP1sue,OP1sue,#Sign_bit
        TST     Rins,#ABS_bit
        BICNE   OP1sue,OP1sue,#Sign_bit
  IF Interworking :LOR: Thumbing
        LDMFD   Rsp!,{LR}
        BX      LR
  ELSE
        LDMFD   Rsp!,{PC}
  ENDIF

        ]

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted

; The second entry point to the NRM routine, intended for use by the FPASC.
;
; Uses standard monadic operation entry and exit conventions - see top of
; this file.

        [ FPASCWanted

NormFPASC

        CDebug3 3,"NormFPASC: operand =",OP1sue,OP1mhi,OP1mlo

; The FPA does not bounce common values in the Prepare stage for these
; instructions, so no need to check the uncommon bit.

        ]

Norm_Uncommon

; Only uncommon values will get here. First split out all but NaNs and
; infinities.

        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op is NaN/inf)
        ANDPL   RNDexp,OP1sue,#ToExp_mask
        BPL     Norm_ZeroUnnormOrDenorm

NormUrd_NaNInf

; The operand is a NaN or infinity. If it's an infinity, we just want to
; return a standard infinity. If it's a NaN, we use the standard NaN
; propagation code.

        ORRS    Rtmp,OP1mlo,OP1mhi,LSL #1 ;Check for NaNs
        BNE     $ConvertNaN1_str
        AND     Rtmp,OP1sue,#Sign_bit   ;Isolate sign
        ADR     OP1sue,Prototype_Infinity
        LDMIA   OP1sue,OP1regs
        ORR     OP1sue,OP1sue,Rtmp
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted

; The second entry point to the URD routine, meant for use by the FPASC and
; optimised for uncommon operands.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Uses standard monadic operation entry and exit conventions - see top of
; this file.

        [ FPASCWanted

UrdFPASC

        CDebug3 3,"UrdFPASC: operand =",OP1sue,OP1mhi,OP1mlo

; The FPA does not bounce common values in the Prepare stage for these
; instructions, so no need to check the uncommon bit.

        ]

Urd_Uncommon

; Split out NaNs and infinities, which are dealt with in exactly the same
; way as by the NRM instruction.

        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op1 is NaN/inf)
        BMI     NormUrd_NaNInf

; The operand is now known to be a denormalised number or an extended
; precision unnormalised number or zero. We have to take a little care about
; single and double precision denormalised numbers, since their exponents
; and mantissas need correcting. Otherwise, we can just use the standard
; Urd_Numeric routine on them once we have separated the sign and the
; exponent from each other. We can recognise the single and double
; denormalised numbers by the fact that they are the only remaining cases
; with a units bit of 1.

        AND     Rarith,OP1sue,#ToExp_mask       ;Extract operand exponent
        AND     OP1sue,OP1sue,#Sign_bit         ; and sign

        TST     OP1mhi,#EIUnits_bit
        BICNE   OP1mhi,OP1mhi,#EIUnits_bit
        ADDNE   Rarith,Rarith,#1

        B       Urd_Numeric

        ]

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted

; The second part of the RND routine, which deals with uncommon operands.

Rnd_Uncommon

; Split out NaNs and infinities, which are dealt with in exactly the same
; way as by the NRM instruction.

        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op1 is NaN/inf)
        BMI     NormUrd_NaNInf

; The value is an uncommon numeric value - i.e. a denormalised number, an
; extended unnormalised number or an extended unnormalised zero. If it's the
; last of these, change it to a real zero and treat it as a numeric.

        ORRS    RNDexp,OP1mhi,OP1mlo
        ANDEQ   OP1sue,OP1sue,#Sign_bit
        BEQ     Rnd_Exact

; The operand is now a denormalised number or extended unnormalised non-zero
; number. We will change it into the corresponding normalised number
; (possibly with a negative biased exponent), then treat it as a numeric.
;   The types of numbers that require converting are extended unnormalised
; numbers and denormalised numbers of all precisions. In the case of the
; extended denormalised and unnormalised numbers, this just requires us to
; normalise them; in the case of the single and double denormalised numbers,
; we need to clear their units bits and add 1 to their exponents before we
; normalise them.
;   At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have uncommon = units =
; 1: all other numbers with this property are NaNs or infinities and have
; been dealt with already.

        AND     RNDexp,OP1sue,#ToExp_mask
        AND     OP1sue,OP1sue,#Sign_bit
        ASSERT  EIExp_pos = 0

        STMFD   Rsp!,{LR}       ;We will have subroutine calls below

        TST     OP1mhi,#EIUnits_bit
        BICNE   OP1mhi,OP1mhi,#EIUnits_bit
        ADDNE   RNDexp,RNDexp,#1

        BL      $NormaliseOp1_str       ;NB must be necessary, so no
                                        ; point in checking whether
                                        ; normalised

        LDMFD   Rsp!,{LR}
        B       Rnd_Numeric

        ]

;===========================================================================

        [ :DEF: compare_s :LOR: FPEWanted :LOR: FPASCWanted

; The second entry point to the comparison routine, meant for use by the
; FPASC and without a fast track for common operands.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Has the same entry and exit conventions as "CompareFPE" above.

        [ FPASCWanted

CompareFPASC

        CDebug3 3,"CompareFPASC: op1 =",OP1sue,OP1mhi,OP1mlo
        CDebug3 3,"              op2 =",OP2sue,OP2mhi,OP2mlo

        ]

Compare_Uncommon

; We have to do a full comparison, since either or both of the operands may
; be uncommon. What we will do is:
;
;   (a) Check for NaNs. If found, produce a trap if appropriate, or a result
;       of "unordered" otherwise.
;
;   (b) If no NaNs, adjust the operands by replacing all infinities by the
;       standard extended infinity, and all effectively unnormalised numbers
;       by the corresponding normalised or denormalised number. Then call
;       Compare_Common, which will work correctly on zeros, denormalised
;       numbers, normalised numbers and extended infinities.
;
; So the first thing we do is check for NaNs. This is done by first testing
; for a NaN or infinity (they have similar bit patterns) by a standard
; technique, then checking whether the fraction is non-zero.

        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op1 is NaN/inf)
        TNaNInf Rtmp2,OP2sue,OP2mhi           ;Rtmp2[31] := (op2 is NaN/inf)
        TST     Rtmp,#TopBit                    ;Operand 1 NaN or infinity?
        ORRNES  Rarith,OP1mlo,OP1mhi,LSL #1     ;If so, is it a NaN?
        BNE     Compare_Unordered
        TST     Rtmp2,#TopBit                   ;Operand 2 NaN or infinity?
        ORRNES  Rarith,OP2mlo,OP2mhi,LSL #1     ;If so, is it a NaN?
        BNE     Compare_Unordered

; Now we know there are no NaNs and therefore no exceptions - which means we
; no longer need to keep track of exactly what the operands are. We are
; going to massage the operands into a form where we can use the
; Compare_Common routine on them - note that it already works for zeros,
; normalised numbers, extended denormalised numbers and normal extended
; precision infinities. The remaining numbers are the other infinities, the
; extended unnormalised numbers and zeros, and the single and double
; precision denormalised numbers.
;   We will first convert all the infinities to a standard extended
; precision infinity, to ensure that they compare equal with each other. Or
; rather, an almost standard one - we will mark the result as common to
; avoid mistaking it for an unnormalised or denormalised number later on.

        STMFD   Rsp!,{LR}           ;We're likely to make subroutine calls

        TST     Rtmp,#TopBit
        ANDNE   OP1sue,OP1sue,#Sign_bit
        ORRNE   OP1sue,OP1sue,#&FF
        ORRNE   OP1sue,OP1sue,#&7F00
        BICNE   OP1mhi,OP1mhi,#EIUnits_bit
        TST     Rtmp2,#TopBit
        ANDNE   OP2sue,OP2sue,#Sign_bit
        ORRNE   OP2sue,OP2sue,#&FF
        ORRNE   OP2sue,OP2sue,#&7F00
        BICNE   OP2mhi,OP2mhi,#EIUnits_bit

; Now we need to deal with the extended unnormalised numbers and zeros, and
; the single and double denormalised numbers. These basically need
; converting to extended precision normalised or denormalised numbers. In
; the case of the extended unnormalised numbers and zeros, this just
; requires us to normalise them; in the case of the single and double
; denormalised numbers, we need to clear their units bits and add 1 to their
; exponents before we normalise them.
;   At this stage, we can recognise that the numbers are single or double
; denormalised numbers simply by the fact that they have uncommon = units =
; 1: all other numbers with this property are NaNs or infinities and have
; been dealt with already.

        ANDS    Rarith,OP1mhi,OP1sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP1mhi,OP1mhi,#EIUnits_bit
        ADDMI   OP1sue,OP1sue,#1:SHL:EIExp_pos
        ANDS    Rarith,OP2mhi,OP2sue,LSL #EIUnits_pos-Uncommon_pos
        ASSERT  EIUnits_pos = 31
        BICMI   OP2mhi,OP2mhi,#EIUnits_bit
        ADDMI   OP2sue,OP2sue,#1:SHL:EIExp_pos

; Now we need to normalise all these types of numbers, which now means all
; uncommon numbers except those with exponent 0 (which are extended
; precision denormalised numbers and should be left alone).

        TST     OP1sue,#Uncommon_bit
        Exp2Top Rarith,OP1sue,NE,S      ;Complete test & set up for call
        BLNE    $NormDenormOp1_str
        TST     OP2sue,#Uncommon_bit
        Exp2Top Rarith,OP2sue,NE,S      ;Complete test & set up for call
        BLNE    $NormDenormOp2_str

; And now we can compare the results as though they were common numbers.

        LDMFD   Rsp!,{LR}
        B       Compare_Common

Compare_Unordered

; The result is definitely unordered. We need to choose the correct result.

        TST     Rfpsr,#AC_bit
        MOVEQ   Rarith,#Comp_Un_Orig
        MOVNE   Rarith,#Comp_Un_Alt

; Now we need to know whether there's an IEEE exception - there is one if
; either operand is a signalling NaN, or if the instruction is CMFE or CNFE.
; Note that the top bits of Rtmp and Rtmp2 are still NaN/infinity flags for
; the two operands.

        TST     Rtmp,#TopBit                    ;Is operand 1 a NaN?
        ORRNES  Rtmp,OP1mlo,OP1mhi,LSL #1
        BEQ     Compare_Unordered_Op1NotNaN     ;If not, operand 2 must be
        ANDS    Rtmp,OP1mhi,#EIFracTop_bit      ;If so, is it signalling?
        [ FPLibWanted
        MOVEQ   Rarith,#IVO_bits
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR
  ENDIF
        |
        BEQ     InvalidOperation2ForI           ; (invalid operation if so)
        ASSERT  InvReas_SigNaN = 0
        ]

        TST     Rtmp2,#TopBit                   ;Is operand 2 a NaN?
        ORRNES  Rtmp,OP2mlo,OP2mhi,LSL #1
        [ FPEWanted :LOR: FPASCWanted
        BEQ     Compare_Unordered_Op2NotNaN     ;Branch if not
        |
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR
  ENDIF
        ]
Compare_Unordered_Op1NotNaN
        ANDS    Rtmp,OP2mhi,#EIFracTop_bit      ;If so, is it signalling?
        [ FPLibWanted
        MOVEQ   Rarith,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF
        |
        BEQ     InvalidOperation2ForI           ; (invalid operation if so)
        ASSERT  InvReas_SigNaN = 0
        ]

        [ FPEWanted :LOR: FPASCWanted
Compare_Unordered_Op2NotNaN
        TST     Rins,#CompExc_bit               ;Is instruction CMFE/CNFE?
  IF Interworking :LOR: Thumbing
        BXEQ    LR
  ELSE
        MOVEQ   PC,LR                           ;If not, no exception
  ENDIF
        MOV     Rtmp,#InvReas_CompQNaN          ;Otherwise, invalid op
        B       InvalidOperation2ForI
        ]

        ]

;===========================================================================

        [ FPEWanted :LOR: FPASCWanted :LOR: :DEF: fix_s :LOR: :DEF: fixu_s

; The second entry point to the FIX routine, meant for use by the FPASC and
; optimised for uncommon operands.
;   This routine will not work correctly with inputs which are unnormalised
; URD results, or with invalid internal format numbers.
;
; Has the same entry and exit conventions as "FixFPE" above.

        [ FPASCWanted

FixFPASC

        CDebug3 3,"FixFPASC: operand =",OP1sue,OP1mhi,OP1mlo

; Start by splitting between common and uncommon operands.

        TST     OP1sue,#Uncommon_bit
        BEQ     Fix_Common

        ]

        [ :DEF: fix_s
__fp_fix_uncommon
        ]
        [ :DEF: fixu_s
__fp_fixu_uncommon
        ]

Fix_Uncommon

; NaNs and infinities will produce invalid operation exceptions, with the
; precise nature of the exception depending on whether the operand is a
; signalling NaN, a quiet NaN or an infinity.

        TNaNInf Rtmp,OP1sue,OP1mhi            ;Rtmp[31] := (op1 is NaN/inf)
        BMI     Fix_NaNInf

; The operand is now known to be a denormalised number or an extended
; precision unnormalised number or zero. We have to take a little care about
; single and double precision denormalised numbers, since their exponents
; and mantissas need correcting. Otherwise, we can just use the standard
; Fix_Numeric routine on them once we have separated the sign and the
; exponent from each other. We can recognise the single and double
; denormalised numbers by the fact that they are the only remaining cases
; with a units bit of 1.

        AND     Rarith,OP1sue,#ToExp_mask       ;Extract operand exponent
        [ :LNOT: :DEF: fixu_s
        AND     OP1sue,OP1sue,#Sign_bit         ; and sign
        ]

        TST     OP1mhi,#EIUnits_bit
        BICNE   OP1mhi,OP1mhi,#EIUnits_bit
        ADDNE   Rarith,Rarith,#1

        B       Fix_Numeric

Fix_NaNInf

; All of these produce an invalid operation exception, with the reason being
; InvReas_SigNaN for signalling NaNs, InvReas_FixQNaN for quiet NaNs and
; InvReas_FixInf for infinities.

        [ FPEWanted :LOR: FPASCWanted

        TST     OP1mhi,#EIFracTop_bit
        MOVEQ   Rtmp,#InvReas_SigNaN
        MOVNE   Rtmp,#InvReas_FixQNaN
        ORRS    Rarith,OP1mlo,OP1mhi,LSL #1
        MOVEQ   Rtmp,#InvReas_FixInf
        MOV     Rarith,#TopBit                  ;Some sort of integer result
        B       InvalidOperation1ForI

        |

        MOV     OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

        ]

        ]

;===========================================================================

        END
