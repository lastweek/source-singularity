;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; nans.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

        GET     fpe.asm

        [ :DEF: thumb
        CODE32
        ]

	AREA   |.text|, CODE, READONLY

        EXPORT  __fp_convert_NaNs
        EXPORT  __fp_convert_NaN1
        EXPORT  __fp_convert_NaN_1Of2
        EXPORT  __fp_convert_NaN_2Of2

__fp_convert_NaNs

; First check for cases where the first operand determines which routine to
; use - i.e. if it is a signalling NaN or not a NaN at all.

        ORRS    Rtmp,OP1mlo,OP1mhi,LSL #1       ;First operand a NaN?
        BEQ     __fp_convert_NaN_2Of2           ;If not, use ConvertNaN2Of2
        TST     OP1mhi,#EIFracTop_bit           ;First operand a sign.NaN?
        BEQ     __fp_convert_NaN_1Of2           ;If so, use ConvertNaN1Of2

; First operand is a quiet NaN. If second is a signalling NaN, we use
; ConvertNaN2Of2; otherwise, we use ConvertNaN1Of2.

        ORRS    Rtmp,OP2mlo,OP2mhi,LSL #1       ;Second operand a NaN?
        BEQ     __fp_convert_NaN_1Of2           ;If not, use ConvertNaN1Of2
        TST     OP2mhi,#EIFracTop_bit           ;Second operand a sign.NaN?
        BNE     __fp_convert_NaN_1Of2           ;If not, use ConvertNaN1Of2

__fp_convert_NaN_2Of2

        CDebug3 4,"ConvertNaN2Of2: NaN =",OP2sue,OP2mhi,OP2mlo

; We must check for an invalid operation trap *before* we start using shared
; code, because the operands must be left unchanged for the trap handler.

;; There is always a trap handler, and it doesn't care about the operands

        TST     OP2mhi,#EIFracTop_bit           ;Signalling NaN?
        BEQ     ReturnIVO

; Now we can transfer the NaN to OP1sue/mhi/mlo and use shared code.

        MOV     OP1sue,OP2sue
        MOV     OP1mhi,OP2mhi
        MOV     OP1mlo,OP2mlo
        B       ConvertNaN1_NoTrap

__fp_convert_NaN1

; We must check for an invalid operation trap *before* we start using shared
; code, because the operands must be left unchanged for the trap handler.

        CDebug3 4,"ConvertNaN1: NaN =",OP1sue,OP1mhi,OP1mlo

        TST     OP1mhi,#EIFracTop_bit           ;Signalling NaN?
        BEQ     ReturnIVO
        B       ConvertNaN1_NoTrap              ; becomes 0 = InvReas_SigNaN

__fp_convert_NaN_1Of2

        CDebug3 4,"ConvertNaN1Of2: NaN =",OP1sue,OP1mhi,OP1mlo

; We must check for an invalid operation trap *before* we start using shared
; code, because the operands must be left unchanged for the trap handler.

        TST     OP1mhi,#EIFracTop_bit           ;Signalling NaN?
        BEQ     ReturnIVO

ConvertNaN1_NoTrap

; Now we need to perform the actual NaN conversion. The rules here are:
;
; * The exponent field must be converted to the appropriate value for the
;   destination precision;
;
; * Fraction bits that are not used by the destination precision must be
;   cleared;
;
; * If result precision is single or double, units bit is forced to 1;
;
; * If the NE bit is 0 and we're converting to extended precision, the
;   bottom bit of the fraction must be set or cleared to indicate whether
;   the NaN is "really" single or double precision respectively.

; Split according to result precision.

        TST     Rins,#Single_mask
        BNE     ConvertNaN1_ToSingle
        TST     Rins,#Double_mask
        BNE     ConvertNaN1_ToDouble

;------------------------------------------------------------------------------

ConvertNaN1_ToExtended

; If NE=0, we just need to modify the exponent. Otherwise, we need to
; establish the effective precision and set or clear the bottom bit of the
; fraction appropriately.

        TST     Rins,#NE_bit
        BNE     ConvertNaN1_ToExtended_MantissaDone
        AND     Rtmp,OP1sue,#ToExp_mask ;Isolate exponent field
        MOV     Rtmp2,#NaNInfExp_Double:AND:&FF
        ORR     Rtmp2,Rtmp2,#NaNInfExp_Double:AND:&FF00
        ASSERT  NaNInfExp_Double <= &FFFF
        CMP     Rtmp,Rtmp2              ;LO/EQ/HI if single/double/extended
        ASSERT  NaNInfExp_Single < NaNInfExp_Double
        ASSERT  NaNInfExp_Double < NaNInfExp_Extended
        BICLO   OP1mlo,OP1mlo,#1        ;Bottom bit cleared for single NaN
        ORREQ   OP1mlo,OP1mlo,#1        ;Bottom bit set for double NaN
                                        ;Bottom bit unchanged for extended NaN

ConvertNaN1_ToExtended_MantissaDone

; Change exponent and return.

        AND     OP1sue,OP1sue,#Sign_bit+Uncommon_bit
        ORR     OP1sue,OP1sue,#NaNInfExp_Extended:AND:&FF
        ORR     OP1sue,OP1sue,#NaNInfExp_Extended:AND:&FF00
        ASSERT  NaNInfExp_Extended <= &FFFF

        TEQ     OP1sue,OP1sue           ;Force EQ condition
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

;------------------------------------------------------------------------------

ConvertNaN1_ToDouble

; Change exponent.

        AND     OP1sue,OP1sue,#Sign_bit+Uncommon_bit
        ORR     OP1sue,OP1sue,#NaNInfExp_Double:AND:&FF
        ORR     OP1sue,OP1sue,#NaNInfExp_Double:AND:&FF00
        ASSERT  NaNInfExp_Double <= &FFFF

; Clear appropriate fraction bits and set the units bit. Note that we know
; this won't change a NaN into an infinity unless someone is misusing
; extended precision with NE=0.

        MOV     OP1mlo,OP1mlo,LSR #11
        MOV     OP1mlo,OP1mlo,LSL #11
        ORR     OP1mhi,OP1mhi,#EIUnits_bit

        TEQ     OP1sue,OP1sue           ;Force EQ condition
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR
  ENDIF

;------------------------------------------------------------------------------

ConvertNaN1_ToSingle

; Change exponent.

        AND     OP1sue,OP1sue,#Sign_bit+Uncommon_bit
        ORR     OP1sue,OP1sue,#NaNInfExp_Single:AND:&FF
        ORR     OP1sue,OP1sue,#NaNInfExp_Single:AND:&FF00
        ASSERT  NaNInfExp_Single <= &FFFF

; Clear appropriate fraction bits and set the units bit. Note that we know
; this won't change a NaN into an infinity unless someone is misusing
; extended precision with the NE bit equal to 0.

        MOV     OP1mlo,#0
        BIC     OP1mhi,OP1mhi,#&FF
        ORR     OP1mhi,OP1mhi,#EIUnits_bit
  IF Interworking :LOR: Thumbing
        BX      LR
  ELSE
        MOV     PC,LR                   ;Note we still have EQ from above
  ENDIF

;==============================================================================

ReturnIVO

; Return to the veneer with an IVO exception signalled.

        ORR     OP1sue,OP1sue,#IVO_bits
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

;==============================================================================

        END
