;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; format_d.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

        GET     fpe.asm

        CodeArea |FPL$$Format|

        IMPORT  __fp_nonveneer_error

; Functions for converting
;        double <-> internal,
;        double <-> int,
;        double <-> longlong
; and for fiddling with the double format (frexp)



DNaNInf EQU     NaNInfExp_Double - EIExp_bias + DExp_bias

exp     RN 2

;==============================================================================

        [ :DEF: dflt_s :LOR: :DEF: dfltu_s

;This code needed for the unsigned float too.

        MACRO
        DoubleNormalise

;Now we have the basis of the exponent, we round.

        MOVS    utmp1, a1, LSR #16
        MOVEQ   a1, a1, LSL #16
        SUBEQ   tmp, tmp, #16<<DExp_pos
        MOVS    utmp1, a1, LSR #24
        MOVEQ   a1, a1, LSL #8
        SUBEQ   tmp, tmp, #8<<DExp_pos
        MOVS    utmp1, a1, LSR #28
        MOVEQ   a1, a1, LSL #4
        SUBEQ   tmp, tmp, #4<<DExp_pos
        MOVS    utmp1, a1, LSR #30
        MOVEQ   a1, a1, LSL #2
        SUBEQ   tmp, tmp, #2<<DExp_pos
        MOVS    utmp1, a1, LSR #31
        MOVEQ   a1, a1, LSL #1
        SUBEQ   tmp, tmp, #1<<DExp_pos
        MOV     a1, a1, LSL #1

;Now shift the mantissa into both words

        MOV     dOPl, a1, LSL #DFhi_len
        ORR     dOPh, tmp, a1, LSR #32-DFhi_len

        ReturnToLR

        MEND

        ]

;...........................................................................

        [ :DEF: dflt_s

        Export __itod
        Export __utod

__utod  EnterWithLR_16
        MOV     exp, #(DExp_bias+1) << DExp_pos
        B       __dflt_normalise

__itod  EnterWithLR_16
        ANDS    exp, a1, #Sign_bit      ;Extract sign
        RSBNE   a1, a1, #0              ;If -ve, undo 2's complement
        ORR     exp, exp, #(DExp_bias+1) << DExp_pos
        ; fallthrough

; Normalise a 32 bit number in a1. The high 13 bit of exp contain 
; the preset sign+exponent. The decimal point is set at bit 1 (if a1 = 2,
; exponent will be increased by 0). 
; No under/overflow checking is done. Returns normalised double in dOPh/l,
; or +0 if the number was zero.

__dflt_normalise
        MOVS    a2, a1, LSR #16
        ADDNE   exp, exp, #16 << DExp_pos
        MOVEQS  a1, a1, LSL #16
        ReturnToLR EQ                           ; a1 was zero - return +0
        TST     a1, #255 << 24
        ADDNE   exp, exp, #8 << DExp_pos
        MOVEQ   a1, a1, LSL #8
        TST     a1, #15 << 28
        ADDNE   exp, exp, #4 << DExp_pos
        MOVEQ   a1, a1, LSL #4
        TST     a1, #3 << 30
        ADDNE   exp, exp, #2 << DExp_pos
        MOVEQS  a1, a1, LSL #2
        ; MI if high bit set, PL if not
        ADDMI   exp, exp, #1 << DExp_pos
        MOVPL   a1, a1, LSL #1
        MOV     tmp, a1
        MOV     dOPl, tmp, LSL #DFhi_len+1               ; put low 12 bits into low word
        ADD     dOPh, exp, tmp, ASR #32 - (DFhi_len+1)   ; combine high 20 bits and exponent                                                       ;   and subtract one from exponent
        ReturnToLR

        ]

;------------------------------------------------------------------------------

        [ :DEF: ll_sto_d_s :LOR: :DEF: ll_uto_d_s

;This code needed for the unsigned float too.

        MACRO
        LongDoubleNormalise

;Now we have the basis of the exponent, we round.

        MOV     utmp1, #0
        MOVS    utmp2, a2, LSR #16
        MOVEQ   a2, a2, LSL #16
        ADDEQ   utmp1, utmp1, #16
        MOVS    utmp2, a2, LSR #24
        MOVEQ   a2, a2, LSL #8
        ADDEQ   utmp1, utmp1, #8
        MOVS    utmp2, a2, LSR #28
        MOVEQ   a2, a2, LSL #4
        ADDEQ   utmp1, utmp1, #4
        MOVS    utmp2, a2, LSR #30
        MOVEQ   a2, a2, LSL #2
        ADDEQ   utmp1, utmp1, #2
        MOVS    utmp2, a2, LSR #31
        MOVEQ   a2, a2, LSL #1
        ADDEQ   utmp1, utmp1, #1
        MOV     a2, a2, LSL #1

        SUB     tmp, tmp, utmp1, LSL #DExp_pos

        ; save off low-word for now
        MOV     utmp2, a1

        ; take bits from high word into mhi
        ORR     dOPh, tmp, a2, LSR #DExp_len+1

        ; get 32 - (number of bits from other word needed in mhi)
        RSB     utmp1, utmp1, #64-DFhi_len-1
        SUBS    tmp, utmp1, #32 ; CMP, save result

        ORRLO   dOPh, dOPh, utmp2, LSR utmp1
        RSBLO   utmp1, utmp1, #32
        MOVLO   dOPl, utmp2, LSL utmp1

        ReturnToLR LO

; high word contributes to mlo, and there's a rounding to be
; considered.

        MOV     dOPl, a2, LSL #DFhi_len ; this many bits left from top-word
        ORR     dOPl, dOPl, utmp2, LSR tmp ; plus these bits

; now deal with the rounding
        RSB     tmp, tmp, #33
        MOVS    utmp2, utmp2, LSL tmp ; C<-round Z<-sticky

; Now we need to round - the rounding bits are in the flags

        ReturnToLR CC

        TSTEQ   dOPl, #1        ; combine "even" bit with sticky
        ReturnToLR EQ

        ADDS    dOPl, dOPl, #1  ; round up
        ADDCS   dOPh, dOPh, #1  ; and carry

        ReturnToLR

        MEND

        ]

;------------------------------------------------------------------------------

        [ :DEF: ll_sto_d_s

        Export  _ll_sto_d
        ImportCodeSize _ll_to_d_shared
        ROUT

_ll_sto_d EnterWithLR_16

        IMPORT  _dfltu

        TEQ     a2, #0
        BEQ     _dfltu          ; a 'normal' long

        ANDS    tmp, a2, #Sign_bit ; Extract sign
; sign is in tmp, and the denormalised mantissa is in a1/a2.
    [ CodeSize = 2
        BEQ     _ll_to_d_shared
    |
        ORR     tmp, tmp, #((DExp_bias + 63) :AND: 0xff00) << DExp_pos
      [ CodeSize = 1
        BEQ     _ll_to_d_shared
      |
        ORR     tmp, tmp, #((DExp_bias + 63) :AND: 0x00ff) << DExp_pos
        BEQ     %FT01
      ]
    ]
        RSBS    a1, a1, #0
        RSCS    a2, a2, #0      ; undo 2's complement
      [ CodeSize <> 0
        BNE     _ll_to_d_shared
      |
        BEQ     %FT02

01
        LongDoubleNormalise

02
      ]
        EnterWithStack
        BL      _dfltu
        ORR     dOPh, dOPh, #Sign_bit
        ReturnToStack
        ]

        
;------------------------------------------------------------------------------

        [ :DEF: ll_uto_d_s

        Export  _ll_uto_d
        ExportCodeSize  _ll_to_d_shared

_ll_uto_d EnterWithLR_16

        IMPORT  _dfltu

        TEQ     a2, #0
        BEQ     _dfltu

      [ CodeSize = 2
        MOV     tmp, #0

_ll_to_d_shared
        ORR     tmp, tmp, #((DExp_bias + 63) :AND: 0xff00) << DExp_pos
      |
        MOV     tmp, #((DExp_bias + 63) :AND: 0xff00) << DExp_pos
      ]
      [ CodeSize = 1
_ll_to_d_shared
      ]
        ORR     tmp, tmp, #((DExp_bias + 63) :AND: 0x00ff) << DExp_pos

        LongDoubleNormalise

        ]

;===========================================================================

        [ :DEF: dfix_s

        Export  _dfix

        ROUT
_dfix   EnterWithLR_16
        MOVS    a3, dOPh, LSL #1                ; C<--sign
        MOV     a3, a3, LSR #DFhi_len+1
        MOV     dOPh, dOPh, LSL #DExp_len
        ORR     a1, dOPh, dOPl, LSR #DFhi_len+1
        ORR     a1, a1, #1<<31
        SUB     a3, a3, #(DExp_bias:AND:0xff00)
        BCS     _dfix_neg
        SUBS    a3, a3, #(DExp_bias:AND:0x00ff)
        BMI     _dfix_zero
        RSBS    a3, a3, #31
        ; if resulting shift is -ve, or zero, then the result would
        ; overflow (zero because it would leave the units bit
        ; unchanged, and this path is for +ve arguments)
        MOVGT   a1, a1, LSR a3
        ; Don't return -ve results for +ve arguments - will only happen
        ; if the shift amount is zero
        ReturnToLR GT

        ; a1 contains the mantissa, with units bit at bit 31 (shift
        ; did not happen, or was zero)
        ; a2 contains the other bits of the mantissa
        BIC     a1, a1, #Sign_bit        ; ensure any untrapped result is +ve
        B       _dfix_ivo

_dfix_zero
        MOV     a1, #0
        ReturnToLR

_dfix_neg
        SUBS    a3, a3, #(DExp_bias:AND:0x00ff)
        BMI     _dfix_zero
        RSBS    a3, a3, #31
        MOVGT   a1, a1, LSR a3
        RSBGT   a1, a1, #0      ; don't return +ve for -ve arguments
        ReturnToLR GT

; Special case - INT_MIN will leave a shift of zero (Z set), and
; r0=0x80000000 r1=0x00000000
        ORREQS  ip, dOPl, dOPh, LSL #1 ; Z<-special case
        ReturnToLR EQ

;       ORR     a1, a1, #Sign_bit   ; ensure untrapped result is -ve
_dfix_ivo
        MOV     a4, #IVO_bit :OR: FixFn
      [ {TRUE}
        ; On some systems, casting NaN returns zero
        ; check for maximum exponent
        ADD     a3, a3, #:NOT:(31-((DExp_mask:SHR:DExp_pos)-DExp_bias))
        CMN     a3, #1
        BNE     __fp_nonveneer_error
        ORRS    ip, dOPl, a1, LSL #1 ; ignore prospective sign
        MOVNE   a4, #IVO_bit :OR: FixZeroFn
      ]
        B       __fp_nonveneer_error
        ]

;---------------------------------------------------------------------------

        [ :DEF: dfixu_s

        ROUT
        Export  _dfixu

_dfixu  EnterWithLR_16
        MOVS    a3, dOPh, LSL #1 ; C<-sign
        BCS     _dfixu_neg
      [ CodeSize <> 0
;; This doesn't work at the moment, because dfixu will return UINT_MAX on
;; overflow, whereas for dfix it should return INT_MAX. The same applies
;; to longlong and float versions
_dfix_shared
      ]
        MOV     a3, a3, LSR #DFhi_len+1 ; get exponent into a3
        MOV     dOPh, dOPh, LSL #DExp_len
        ORR     a1, dOPh, dOPl, LSR #DFhi_len+1 ; get mantissa into a1
        ORR     a1, a1, #1<<31  ; and add units bit
        SUB     a3, a3, #(DExp_bias:AND:0xff00)
        SUBS    a3, a3, #(DExp_bias:AND:0x00ff)
        BMI     _dfix_zero
        RSBS    a3, a3, #31
        ; in the unsigned case, a shift of zero is perfectly allowable
        MOVPL   a1, a1, LSR a3
        ReturnToLR PL

_dfixu_ivo
        MOV     a4, #IVO_bit :OR: FixuFn
      [ {TRUE}
        ; On some systems, casting NaN returns zero
        ; check for maximum exponent
        ADD     a3, a3, #:NOT:(31-((DExp_mask:SHR:DExp_pos)-DExp_bias))
        CMN     a3, #1
        BNE     __fp_nonveneer_error
        ORRS    ip, dOPl, a1, LSL #1 ; ignore units bit
        MOVNE   a4, #IVO_bit :OR: FixZeroFn
      ]
        B       __fp_nonveneer_error

_dfixu_neg
        ORRS    a4, dOPl, dOPh, LSL #1
        MOVNE   a4, #IVO_bit :OR: FixZeroFn
        BNE     __fp_nonveneer_error
_dfix_zero
        MOV     a1, #0
        ReturnToLR

        ]

;------------------------------------------------------------------------------

        [ :DEF: ll_sfrom_d_s

        Export  _ll_sfrom_d

        ROUT
_ll_sfrom_d EnterWithLR_16

        MOVS    a4, dOPh, LSL #1 ; C<-sign
        MOV     a4, a4, LSR #DFhi_len+1 ; exp
        MOV     tmp, dOPh, LSL #DExp_len ; mhi
        ORR     tmp, tmp, dOPl, LSR #DFhi_len+1 ; add mlo to mhi
        ORR     tmp, tmp, #1<<31  ; set units bit -- tmp now has top of mantissa
        MOV     a1, dOPl, LSL #DExp_len ; a1 <- low of mantissa

        ; a1 <- lsw of mantissa
        ; a2 <- original low word of mantissa
        ; tmp <- msw of mantissa, with units
        ; a4 <- exponent, still biased
        ; C <- sign

        SUB     a4, a4, #(DExp_bias :AND: 0xff00)

        BCS     ll_from_d_negative

        SUBS    a4, a4, #(DExp_bias :AND: 0x00ff)
        BMI     _ll_from_d_zero
        RSBS    a3, a4, #31     ; N <- large exponent

        MOVGT   a1, tmp, LSR a3  ; small exponent - 32+a3 shift
        MOVGT   a2, #0          ; msw is zero
        ReturnToLR GT

        ADDS    a3, a3, #32     ; large exponent,   N <- too large
        SUB     a4, a4, #31
        MOVGT   a1, a1, LSR a3
        ORRGT   a1, a1, tmp, LSL a4
        MOVGT   a2, tmp, LSR a3 ; ensure result is +ve
        ReturnToLR GT
        ;  fall through
        ; tmp/a2 <- mantissa
        ; a4 <- unbiased exponent

        BIC     a1, a1, #Sign_bit   ; prospective result is +ve
        B       _ll_from_d_ivo

_ll_from_d_zero
        MOV     a1, #0
        MOV     a2, #0
        ReturnToLR

ll_from_d_negative
        SUBS    a4, a4, #(DExp_bias :AND: 0x00ff)
        BMI     _ll_from_d_zero
        RSBS    a3, a4, #31

        MOVPL   a1, tmp, LSR a3
        MOVPL   a2, #0
        BPL     %ft01

        ADDS    a3, a3, #32
        SUB     a4, a4, #31
        BLE     %f02
        MOV     a1, a1, LSR a3
        ORR     a1, a1, tmp, LSL a4
        MOV     a2, tmp, LSR a3

01      RSBS    a1, a1, #0
        RSC     a2, a2, #0

        ReturnToLR

02
; special case for LLINT_MIN
        ORREQS  a1, dOPl, ip, LSL #1
        MOVEQ   a2, #Sign_bit
        ReturnToLR EQ

        ORR     a1, a1, #Sign_bit ; ensure result is -ve
        ; tmp/a2 <- mantissa
        ; a3 <- unbiased exponent
_ll_from_d_ivo
        MOV     a4, #IVO_bit :OR: FixFn :OR: LongLong_bit
      [ {TRUE}
        ; On some systems, casting NaN returns zero
        ; check for maximum exponent
        ADD     a3, a3, #:NOT:(63-((DExp_mask:SHR:DExp_pos)-DExp_bias))
        CMN     a3, #1
        BNE     __fp_nonveneer_error
        ORRS    ip, dOPl, tmp, LSL #1 ; ignore units bit
        MOVNE   a4, #IVO_bit :OR: FixZeroFn :OR: LongLong_bit     
      ]
        B       __fp_nonveneer_error
        ]

;------------------------------------------------------------------------------

        [ :DEF: ll_ufrom_d_s

        Export  _ll_ufrom_d

        ROUT
_ll_ufrom_d EnterWithLR_16

        MOVS    a3, dOPh, LSL #1 ; C<-sign
        BCS     _ll_ufrom_d_neg
        MOV     a3, a3, LSR #DFhi_len+1 ; exp
        MOV     a4, dOPh, LSL #DExp_len ; mhi
        ORR     a4, a4, dOPl, LSR #DFhi_len+1 ; add mlo to mhi
        ORR     a4, a4, #1<<31  ; set units bit -- a4 now has top of mantissa
        MOV     a1, dOPl, LSL #DExp_len ; a1 <- low of mantissa
        MOV     a2, a4          ; a2 <- high of mantissa
        ; a1 <- lsw of mantissa
        ; a2 <- msw of mantissa, with units

        SUB     a3, a3, #(DExp_bias :AND: 0xff00)
        SUBS    a3, a3, #(DExp_bias :AND: 0x00ff)
        BMI     _ll_ufrom_d_zero
        RSBS    a4, a3, #31     ; N <- large exponent

        MOVPL   a1, a2, LSR a4  ; small exponent - 32+a4 shift
        MOVPL   a2, #0          ; msw is zero
        ReturnToLR PL

        ADDS    a4, a4, #32     ; large exponent,   N <- too large
        SUB     a3, a3, #31
        MOVPL   a1, a1, LSR a4
        ORRPL   a1, a1, a2, LSL a3
        MOVPL   a2, a2, LSR a4
        ReturnToLR PL
        ;  fall through

_ll_ufrom_d_ivo
        ; On some systems, casting NaN returns zero
        ; check for maximum exponent
        ADD     a3, a4, #:NOT:(63-((DExp_mask:SHR:DExp_pos)-DExp_bias))
        CMN     a3, #1
        MOV     a4, #IVO_bit :OR: FixuFn :OR: LongLong_bit
        BNE     __fp_nonveneer_error
        ORRS    ip, a1, dOPl, LSL #1 ; ignore units bit
        MOVNE   a4, #IVO_bit :OR: FixZeroFn :OR: LongLong_bit     
        B       __fp_nonveneer_error

_ll_ufrom_d_neg
        ORRS    a4, dOPl, dOPh, LSL #1
        MOVNE   a4, #IVO_bit :OR: FixZeroFn :OR: LongLong_bit
        BNE     __fp_nonveneer_error
_ll_ufrom_d_zero
        MOV     a1, #0
        MOV     a2, #0
        ReturnToLR

        ]

;==============================================================================

        [ :DEF: d2e_s

        EXPORT  _d2e

_d2e    EnterWithLR
        MOVS    tmp,dOPh,LSL #1                 ;C=sign; Z=exp & frac.top zero
        TEQEQ   dOPl,#0                         ;C unchanged; Z=value is a zero
        MOV     a4,tmp,LSL #DExp_len-1          ;Frac.top in bits 30:11 of mhi
        MOV     dOPh,tmp,LSR #DExp_pos          ;Exponent in bits 11:1
        MOV     OP1mlo,dOPl,LSL #DExp_len       ; OP2mhi and 31:11 of OP2mlo
        ORR     OP1mhi,a4,dOPl,LSR #DFhi_len+1
                                                ;Fraction in bits 30:0 of
        ADDNE   dOPh,dOPh,#(EIExp_bias-DExp_bias):SHL:1
        MOV     OP1sue,dOPh,RRX                 ;Recombine sign and exponent
        ORRNE   OP1mhi,OP1mhi,#EIUnits_bit

        ; Gets here with the *double precision* exponent in the top 11 bits
        ; of tmp. (Exponent<<1+DExp_pos.) We use a sign extended shift to
        ; spot the "maximum exponent case" - leaves us with -1 in tmp.
        MOVS    tmp,tmp,ASR #1+DExp_pos
        BEQ     _d2e_norm_op1                   ;Returns to caller
        CMP     tmp,#&ffffffff
        ORREQ   OP1sue,OP1sue,#Uncommon_bit

        ReturnToLR

_d2e_norm_op1

; Got to here implies a denormalised number. This needs normalising. The
; units bit is (incorrectly) set. If it *is* unset then this is a zero,
; and we have got here "by accident".

        TST     OP1mhi, #EIUnits_bit
        ReturnToLR EQ

        BICS    OP1mhi,OP1mhi,#Sign_bit
        BEQ     _d2e_denorm_low

; The top set bit in the high word, so find out how much to denormalise
; by

        MOVS    RNDexp,OP1mhi,LSR #16
        MOVEQ   OP1mhi,OP1mhi,LSL #16
        MOVEQ   tmp,#16
        MOVNE   tmp,#0
        MOVS    RNDexp,OP1mhi,LSR #24   
        MOVEQ   OP1mhi,OP1mhi,LSL #8
        ADDEQ   tmp,tmp,#8
        MOVS    RNDexp,OP1mhi,LSR #28
        MOVEQ   OP1mhi,OP1mhi,LSL #4
        ADDEQ   tmp,tmp,#4
        MOVS    RNDexp,OP1mhi,LSR #30
        MOVEQ   OP1mhi,OP1mhi,LSL #2
        ADDEQ   tmp,tmp,#2
        MOVS    RNDexp,OP1mhi,LSR #31
        MOVEQ   OP1mhi,OP1mhi,LSL #1
        ADDEQ   tmp,tmp,#1

; tmp now contains the amount to shift by.

        RSB     RNDexp,tmp,#32
        ORR     OP1mhi,OP1mhi,OP1mlo,LSR RNDexp
        MOV     OP1mlo,OP1mlo,LSL tmp

        SUB     OP1sue,OP1sue,tmp
        ADD     OP1sue,OP1sue,#1
        ReturnToLR

_d2e_denorm_low

; The top bit to be set is in OP1mlo

        MOVS    RNDexp,OP1mlo,LSR #16
        MOVEQ   OP1mlo,OP1mlo,LSL #16
        MOVEQ   tmp,#16
        MOVNE   tmp,#0
        MOVS    RNDexp,OP1mlo,LSR #24   
        MOVEQ   OP1mlo,OP1mlo,LSL #8
        ADDEQ   tmp,tmp,#8
        MOVS    RNDexp,OP1mlo,LSR #28
        MOVEQ   OP1mlo,OP1mlo,LSL #4
        ADDEQ   tmp,tmp,#4
        MOVS    RNDexp,OP1mlo,LSR #30
        MOVEQ   OP1mlo,OP1mlo,LSL #2
        ADDEQ   tmp,tmp,#2
        MOVS    RNDexp,OP1mlo,LSR #31
        MOVEQ   OP1mlo,OP1mlo,LSL #1
        ADDEQ   tmp,tmp,#1

; tmp now contains the amount to shift by.

        MOV     OP1mhi,OP1mlo
        MOV     OP1mlo,#0

        SUB     OP1sue,OP1sue,#31
        SUB     OP1sue,OP1sue,tmp
        ReturnToLR

        ]

;==============================================================================

        [ :DEF: e2d_s

        EXPORT  _e2d
        EXPORT  __fp_e2d

  MACRO
  E2D_Return $cc=AL
    MOV$cc     a4, r10
    LDM$cc.FD  sp!, {r10}
  IF Interworking :LOR: Thumbing
    BX$cc      lr
  ELSE
    MOV$cc     pc, lr
  ENDIF
  MEND

_e2d    EnterWithLR
        MOV     RNDexp, OP1sue, LSL #32-EIExp_len
        MOV     RNDexp, RNDexp, LSR #32-EIExp_len
        BIC     OP1sue, OP1sue, RNDexp

__fp_e2d
        STMFD   sp!, {r10}        ; r10 is used to store exception information
        MOV     r10, #0           ; Assume no exceptions
;Passed in the result of an operation. That is:  
;  - the uncommon/sign are in OP1sue
;    an error can be flagged as Uncommon, with the Error bit set, and
;    a further bit specifying which. fpe.s defines appropriate values
;    (e.g. IVO_bits). These are transferred to a4 on exit.
;  - the exponent in RNDexp,
;  - the fraction in OP1mlo/OP1mhi.
;Return with
;  - a result in dOPh/dOPl and possibly some error flags in a4

        ASSERT  Uncommon_bit = 1:SHL:(31-1)
        ASSERT  EIUnits_bit = 1:SHL:31
        BICS    tmp, OP1mhi, OP1sue, LSL #1
        BPL     _e2d_SpecialCase

        SUBS    RNDexp, RNDexp, #(EIExp_bias-DExp_bias)
        BMI     _e2d_ExpUnderflow

        ASSERT  tmp <> RNDexp
        ADDNE   tmp, RNDexp, #1
        CMPNE   tmp, #DNaNInf+1
        BGE     _e2d_ExpOverflow

        MOVS    tmp, OP1mlo, LSR #32-DFhi_len-1 ; 1 is for the J bit
;If rounding is needed then a one will have dropped out
        BCS     _e2d_NeedsRounding

;Simple enough now then.

        ; Test for inexact
        ORRS    Rarith, Rarith, OP1mlo, LSL #DFhi_len+1
        ORRNE   r10, r10, #INX_bit

        ORR     dOPh, OP1sue, RNDexp, LSL #DExp_pos
        BIC     OP1mhi, OP1mhi, #EIUnits_bit
        ORR     dOPh, dOPh, OP1mhi, LSR #32-DFhi_len-1
        ORR     dOPl, tmp, OP1mhi, LSL #DFhi_len+1
        E2D_Return                             ; 22S+1N

;..............................................................................

_e2d_SpecialCase

        TST     OP1sue, #Uncommon_bit
        BNE     _e2d_Uncommon

_e2d_UnitsBit

;Sign is in OP1sue's top bit. The units bit of OP1mhi is clear indicating a
;zero value (since the denorm case is handled by the uncommon bit).

        AND     dOPh, OP1sue, #Sign_bit
        MOV     dOPl, #0
        E2D_Return                              ; 9S+2N

;..............................................................................

_e2d_ExpOverflow

;Sign is in OP1sue's sign bit. May still need rounding. The exponent (RNDexp)
;is out of range for a double precision number, and wasn't signalled as a NaN.

;The exponent has been re-biased.

;Might just be the "just underflowing case" (because of a quirk above). In
;that case RNDexp = 0

        TEQ     RNDexp, #0
        BEQ     _e2d_ExpUnderflow
        MOV     r10, #OVF_bit :OR: INX_bit
        MOV      r0, #0                   ; Have an overflow so clear mantissa and
        MVN      r2, #0                   ;   force exponent to max, preserving the sign
        ANDS     r1, r1, r2, LSL #20      ;   ..
        ORR      r1, r1, r2, LSL #20      ;   ..
        BICPL    r1, r1, #0x80000000      ;   ..
        E2D_Return

;..............................................................................
 Export _e2d_ExpUnderflow
_e2d_ExpUnderflow

;Underflow. If the value can be represented as a denorm in the target
;precision, then it should be. For this to be the case the exponent needs
;to lie in the range [&380-23..&380]. Otherwise the result is a suitably
;signed zero. (A zero is, however, a denorm with zero mantissa.)

;The exponent (RNDexp) has been rebiased (by (EIExp_bias-SExp_bias))

        ADDS    RNDexp, RNDexp, #DFhi_len+32

;If the result is zero then we round according to the top bit of the
;fraction. Branch out of line to do this.

        BEQ     _e2d_ExpJustUnderflow

;If this result is negative, nothing can be done, so return a signed zero.

        ANDMI   dOPh, OP1sue, #Sign_bit
        MOVMI   dOPl, #0
        ORRMI   r10, r10, #UNF_bits
        E2D_Return MI

;We now have in OP1mhi 1MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
;and in OP1mlo         MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
;These need to be converted into a denormalised number. We want the N
;left most bits (N<=52) from this 64-bit value. This splits into three
;cases - [1..20], [21..32] and [33..52]. We actually split it into the
;[1..32] and [33..52] cases.

        SUBS    RNDexp, RNDexp, #32
        BEQ     _e2d_Underflow32
        BLT     _e2d_ShortUnderflow

;Okay - all the bits we are going to throw away are in the low word.
;Check for rounding.

        SUB     tmp, RNDexp, #1
        ORRS    tmp, Rarith, OP1mlo, LSL RNDexp
        ORRNE   r10, r10, #UNF_bits      ; Determine inexact

        MOVS    tmp, OP1mlo, LSL RNDexp
        BMI     _e2d_LongUnderflowNeedsRounding

        RSB     tmp, RNDexp, #32
        ASSERT  dOPh <> OP1mhi
        ORR     dOPh, OP1sue, OP1mhi, LSR tmp
        MOV     OP1mlo, OP1mlo, LSR tmp
        ORR     dOPl, OP1mlo, OP1mhi, LSL RNDexp

        E2D_Return

_e2d_LongUnderflowNeedsRounding

;We need to determine whether to just round upwards, or to round to even.

        ORRS    tmp, Rarith, tmp, LSL #1        ;C=1, Z=definite round to even.

;Now we calculate the shift amount and do the shift, probably throwing away
;lots of mantissa bits

        RSB     tmp, RNDexp, #32

;Merge in the sign bit and add one (C flag). Then undo the rounding if we
;need to round to even and the result isn't even.

        ORR     dOPh, OP1sue, OP1mhi, LSR tmp
        MOV     OP1mlo, OP1mlo, LSR tmp
        ORR     dOPl, OP1mlo, OP1mhi, LSL RNDexp
        TSTEQ   dOPl, #1
        E2D_Return EQ
        ADDS    dOPl, dOPl, #1
        ADDCS   dOPh, dOPh, #1
        TST     dOPh, #0x00100000  ; Check if rounded up to MinNormal
        BICNE   r10, r10, #UNF_bit ; If did, no longer underflow
        E2D_Return

;..............................................................................

_e2d_Underflow32

        ; Check for inexact
        ORRS     tmp, Rarith, OP1mlo
        ORRNE    r10, r10, #UNF_bits



;We are going to throw away the entire of the bottom word. This makes
;rounding simple, so it is special cased.

        TEQ     OP1mlo, #1<<31

;Z flag is set if only the top bit is set. The N flag is set to the
;*inverse* of the top bit.

        ASSERT  OP1sue = dOPh
        ASSERT  OP1mhi = dOPl

        E2D_Return MI          ;No rounding to be done

        TSTEQ   dOPl, #1        ;Z flag now clear if rounding needed
        E2D_Return EQ

        ADDS    dOPl, dOPl, #1
        ADDCS   dOPh, dOPh, #1
        E2D_Return

;..............................................................................

_e2d_ShortUnderflow

;We are going to throw away all of the bottom word. The amount to shift
;by is in RNDexp, but has had 32 taken away.

        ADD     RNDexp, RNDexp, #32             ; Undo the subtraction

        ; Check for inexact
        SUB     tmp, RNDexp, #0
        ORR     tmp, Rarith, OP1mhi, LSL tmp
        ORRS    tmp, tmp, OP1mlo
        ORRNE   r10, r10, #UNF_bits

        MOVS    tmp, OP1mhi, LSL RNDexp         ; test top bit to be thrown
        BMI     _e2d_ShortUnderflowNeedsRounding

        RSB     tmp, RNDexp, #32
        ASSERT  dOPh <> OP1mhi
        MOV     dOPl, OP1mhi, LSR tmp
        AND     dOPh, OP1sue, #Sign_bit
        E2D_Return

_e2d_ShortUnderflowNeedsRounding

        TEQ     tmp, #1<<31                     ; any bits other than rounding
        ORREQS  tmp, OP1mlo, Rarith             ; bit? i.e. in lo or in sticky?

        RSB     tmp, RNDexp, #32
        ASSERT  dOPh = OP1sue
        MOV     dOPl, OP1mhi, LSR tmp
        TSTEQ   dOPl, #1
        ADDNE   dOPl, dOPl, #1  ; Can't overflow in this case
        E2D_Return

_e2d_ExpJustUnderflow

;The exponent is just at the limits of underflow - i.e. we may be able
;to represent the number as the float epsilon.

;       MOVS    dOPh, dOPh, LSR #20
;       ADC     fOP, tmp, #0

;But that's not how the FP emulator behaves. It does this:

        TEQ     OP1mhi, #1<<31
        TEQEQ   OP1mlo, #0
        ASSERT  OP1sue = dOPh
        MOVEQ   dOPl, #0
        MOVNE   dOPl, #1
        ORR     r10, r10, #UNF_bits
        E2D_Return

_e2d_Uncommon

;The uncommon bit may signal an error (in which case the error bit will
;be set too)

; RDCFix: Get rid of this?  Take care of NaNs, etc. in special code for each routine?
;        TST     OP1sue,#Error_bit
;        BNE     _e2d_Error


;The uncommon bit (infinity or a NaN) bit was set. The exponent in RNDexp
;is invalid. An infinity is signalled by mhi=mlo=0.

        TEQ     OP1mhi, #0
        MOVNES  OP1mhi, OP1mhi, LSL #1
        MOVMI   dOPh, #-1
        E2D_Return MI
        TEQEQ   OP1mlo, #0
        E2D_Return NE

;An infinity. The sign of the resulting infinity is in tmp.

        AND     dOPh, OP1sue, #Sign_bit
        ORR     dOPh, dOPh,#(DNaNInf:AND:&ff00)<<DExp_pos
        ORR     dOPh, dOPh,#(DNaNInf:AND:&00ff)<<DExp_pos
        ASSERT  dOPl = OP1mhi   ; =0
        E2D_Return

;RDCFix: Get rid of this?  See above
;_e2d_Error

;The error bit was set.

;        MOV     a4, OP1sue
;     ORR r10, r10, #IVO_bit
;        E2D_Return

;..............................................................................

_e2d_NeedsRounding

;Sign in OP1sue, exponent (in range) in RNDexp. OP1mlo is unaffected, but
;a correctly shifted value is in tmp. OP1mhi has the top bit set.

        BIC     OP1mhi, OP1mhi, #EIUnits_bit

;Get the bits that are going to be thrown away, except for the topmost one

        ; Test for inexact
        ORRS    tmp, Rarith, OP1mlo, LSL #DFhi_len+1
        ORRNE   r10, r10, #INX_bit
 
        MOV     tmp, OP1mlo, LSL #DFhi_len+2
        ORRS    tmp, tmp, Rarith        ; Z<-round to even

        AND     tmp, OP1sue, #Sign_bit  ; save the real sign
        MOV     dOPh, RNDexp, LSL #DExp_pos
        ORR     dOPh, dOPh, OP1mhi, LSR #32-DFhi_len-1

        MOV     dOPl, OP1mhi, LSL #DFhi_len+1
        ORR     dOPl, dOPl, OP1mlo, LSR #32-DFhi_len-1

   ;     MOV     a4, #0

        BEQ     _e2d_RoundToEven

        ADDS    dOPl, dOPl, #1
        ADDCS   dOPh, dOPh, #1
        ADDS    a3, dOPh, #1<<DExp_pos
        ORR     dOPh, dOPh, tmp
        E2D_Return PL
        MOV     r10, #OVF_bits
        E2D_Return

;If we need to round to zero, we do something else
_e2d_RoundToEven
        TSTEQ   dOPl, #1
        ORREQ   dOPh, dOPh, tmp
        E2D_Return EQ

; Same as before
        ADDS    dOPl, dOPl, #1
        ADDCS   dOPh, dOPh, #1
        ADDS    a3, dOPh, #1<<DExp_pos
        ORR     dOPh, dOPh, tmp
        E2D_Return PL
        MOV     r10, #OVF_bits
        E2D_Return
        
        ]

;==============================================================================
; frexp

        [ :DEF: frexp_s

; Take a double and a pointer to an integer, and return the fractional part,
; writing the integer to the pointer.


        EXPORT  frexp
        EXPORT  __fp_frexp
        [ :DEF: thumb
        EXPORT  __16__fp_frexp
        ]

        Import_32 __fp_edom
        Import_32 __fp_erange

frexp
; extern double frexp(double value, int *exp);

        [ :DEF: thumb
        PUSH    {a3,lr}
        BL      __16__fp_frexp
        POP     {a4}
        STR     a3,[a4]
    [ Interworking
        POP     {a4}
        BX      a4
    |
        POP     {pc}
    ]
        |
        STMFD   sp!,{a3,lr}     ; leaves sp pointing at a3
        BL      __fp_frexp      ; returns double,int
        LDMFD   sp!,{a4,lr}
        STR     a3,[a4]         ; store value away
        ReturnToLR
        ]

;...........................................................................

; __value_in_regs struct { double frac; int exp } __fp_exp(double);

__fp_frexp EnterWithLR_16
        MOVS    dOPh,dOPh,LSL #1        ; C<-sign Z<-zero?
        TEQEQ   dOPl,#0                 ;  Z<-zero
        MOVEQ   dOPh,dOPh,RRX           ; if (zero) restore sign;
        MOVEQ   a3,#0                   ;           return exp=0
        ReturnToLR EQ

        MOV     a3,dOPh,LSR #DFhi_len+1 ; extract exponent
        BIC     dOPh,dOPh,a3,LSL #DFhi_len+1 ; clear out exponent
        MOV     dOPh,dOPh,RRX           ; recombine sign bit

        TEQ     a3,#0
        SUB     a3,a3,#(DExp_bias-1):AND:&ff00
        SUB     a3,a3,#(DExp_bias-1):AND:&00ff ; adjust exponent
        BEQ     __fp_frexp_denorm       ; un-normalized mantissa

        ORR     dOPh,dOPh,#(0x3fe<<(DFhi_len)) :AND: 0xff000000 ; add new exponent
        ORR     dOPh,dOPh,#(0x3fe<<(DFhi_len)) :AND: 0x00ff0000

;Test for an uncommon exponent - &401
        EOR     a4,a3,#(DNaNInf-DExp_bias+1):AND:&ff00
        TEQ     a4,#(DNaNInf-DExp_bias+1):AND:&00ff

        ReturnToLR NE                   ; and return

; We have an uncommon value. We need to set errno to EDOM and return a huge_val.

        MOV     a2, #1                  ; return HUGE_VAL
        B_32     __fp_edom

__fp_frexp_denorm

; Handle an unnormalized mantissa

; Shove the sign bit into a temporary register, and then shove the mantissa up into
; the top of the word. Then loop around until a bit pops out, and recombine everything.

        AND     tmp,dOPh,#Sign_bit

        MOV     dOPh,dOPh,LSL #DExp_len+1

frexp_denorm_loop

        SUB     a3,a3,#1
        MOVS    dOPh,dOPh,LSL #1                ; N<-last bit C<-0
        BMI     frexp_denorm_loop_exit
        MOVS    dOPl,dOPl,LSL #1
        ORRCS   dOPh,dOPh,#1:SHL:(DExp_len+1)
        B       frexp_denorm_loop

frexp_denorm_loop_exit

; When we get here we have:
;               1MMMMMMMMMMMMMMMMMMMM00000000000
;               MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
;
; We sign extend the 1 to get the 3fe exponent and then add in the sign

        MOV     dOPh,dOPh,ASR #DExp_len-2       ; 1111111111MMMMMMMMMMMMMMMMMMMM00 MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
        BIC     dOPh,dOPh,#1:SHL:(DExp_pos+2)   ; 1111111110MMMMMMMMMMMMMMMMMMMM00 MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
        ORR     dOPh,tmp,dOPh,LSR#2             ; S01111111110MMMMMMMMMMMMMMMMMMMM MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
        ReturnToLR

        ]

;===========================================================================
;ldexp

        [ :DEF: ldexp_s

        EXPORT  ldexp

        Import_32  __fp_edom
        Import_32  __fp_erange

; Take a double format number and an integer, and return x * 2^n without
; calculating 2^n - i.e. add n to the exponent of x.

;       extern double   ldexp(double value, int exp);

; SEEEEEEEEEEEMMMMMMMMMMMMMMMMMMMM MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM

ldexp   EnterWithStack
        AND     tmp, dOPh, #Sign_bit
        MOVS    a4, dOPh, LSL #1
        MOVS    a4, a4, LSR #DExp_pos+1 ; Grab exponent in a4
        BEQ     ldexp_zero_exp
; Test for max exponent
        ADD     lr, a4, #1
        CMP     lr, #1:SHL:DExp_len
        BGE     ldexp_max_exp
ldexp_entry
        ADDS    a4, a4, a3
        BLE     ldexp_exp_underflow     ;not sure about CC here
; Test for max exponent
        ADD     lr, a4, #1
        CMP     lr, #1:SHL:DExp_len
        BGE     ldexp_exp_overflow

;Add the mantissa onto the exponent, and then rotate into position adding
;the sign giving:  MMMMMMMMMMMMMMMMMMMM_EEEEEEEEEEE
        ORR     dOPh, a4, dOPh, LSL #DExp_len+1
        ORR     dOPh, tmp, dOPh, ROR #DExp_len+1
        ReturnToStack

ldexp_zero_exp

; Could either be a zero (return zero) or an un-normalized number (yuck).

        ORRS    a4, dOPl, dOPh, LSL #1  ; check for zero
        MOVEQ   dOPh, tmp
        ReturnToStack EQ

; An un-normalized number...
; We do this the slow way - normalize the number, and then branch back into
; the main code. For each normalization step, decrement a3

ldexp_norm_loop
        MOVS    dOPl, dOPl, LSL #1              ; C <- top bit of low
        ADC     dOPh, dOPh, dOPh                ; dOPh << 1 + C flag
        SUB     a3, a3, #1
        TST     dOPh, #1:SHL:DExp_pos
        BEQ     ldexp_norm_loop

;The value has been normalized, so the exponent is "1". The bit at
;DExp_pos in dOPh is unimportant - it will be cleared later.

        MOV     a4, #1
        B       ldexp_entry

ldexp_exp_underflow

; clear exponent and add leading one.

        MOV     dOPh, dOPh, LSL #DExp_len
        ORR     dOPh, dOPh, #1<<31

; A zero or negative exponent. We should attempt denormalization.
; An exponent in the range [0..-19] leaves some bits in the high word

        CMP     a4, #-DFhi_len
        BGT     ldexp_ufl_small

; An exponent in the range [-53..) cannot be denormalised - the result
; is just zero. -52 might just get a result through rounding.

        CMP     a4, #-(DFhi_len+32)
        BGE     ldexp_ufl_large

; Return a zero with the same sign as the argument

        MOV     dOPh, tmp
        MOV     dOPl, #0
        ReturnToStack

ldexp_ufl_small

        MOV     dOPh, dOPh, LSR #DExp_len

        RSB     a4, a4, #1              ; get the shift amount
        RSB     a3, a4, #32             ; get inverse shift amount

; get rounding information

        MOV     lr, dOPl, LSL a3
        MOVS    lr, lr, LSL #1          ; C <- round Z <- if round, round to even

        MOV     lr, dOPh, LSL a3        ; do the shift
        ORR     dOPl, lr, dOPl, LSR a4
        MOV     dOPh, dOPh, LSR a4

        ORR     dOPh, dOPh, tmp         ; add in sign

        B       ldexp_ufl_exit

ldexp_ufl_large

; we know that the result is going to be all in the lower word, but are any
; bits from the lower word going to be used? [-20..-31]

        ADDS    a4, a4, #32             ; shift amount
        BLE     ldexp_ufl_massive

; dOPh is in place - merge in dOPl bits.

        ORR     dOPh, dOPh, dOPl, LSR #32-DExp_len

; get rounding information
        MOVS    lr, dOPl, LSL a4        ; C <- round, Z <- if round, round to even

        RSB     a4, a4, #32-DFhi_len
        B       ldexp_ufl_massive_exit

ldexp_ufl_massive
        ADD     a4, a4, #DFhi_len+1

; get rounding information
        ORRS    lr, dOPl, dOPh, LSL a4  ; C <- round, Z <- if round, round to even

        RSB     a4, a4, #33

ldexp_ufl_massive_exit

        MOV     dOPl, dOPh, LSR a4      ; do shift
        MOV     dOPh, tmp               ; get sign/hi-word

ldexp_ufl_exit

        TSTEQ   dOPl, #1                ; test for rounding

        ReturnToStack LS                ; C clear (don't round) or Z set (even)

        ADDS    dOPl, dOPl, #1          ; round upwards
        ADDCS   dOPh, dOPh, #1

        ReturnToStack

ldexp_max_exp

; The number has the maximum exponent, so the result is a domain error.

        PullFromStack
        MOV     a2, #1                  ; return HUGE_VAL
        B_32    __fp_edom

ldexp_exp_overflow

; Exponent overflow - set ERANGE and return HUGE_VAL.

        PullFromStack
        MOV     a2, #1                  ; return HUGE_VAL
        B_32    __fp_erange

        ]

;===========================================================================

        [ :DEF: modf_s

        EXPORT  modf
        IMPORT  _dadd

modf    EnterWithLR

        ; Take a double argument in a1,a2, and a pointer in a3 and write
        ; the integral part to *a3, returning the fractional part.

;Test for zero (return zero and write zero)
        ORRS    tmp,dOPl,dOPh,LSL #1    ; Z<-zero argument

;A zero argument. Integer part is appropiate zero, fractional part is zero.
;We know that tmp=0 and dOPl must also be zero.

        STMEQIA a3,{dOPl,tmp}
        ReturnToLR EQ


        MOV     tmp,dOPh,LSL #1
        MOV     tmp,tmp,LSR #DFhi_len+1
        SUB     tmp,tmp,#DExp_bias+1
        ADDS    tmp,tmp,#1
        BMI     modf_small

        RSBS    tmp,tmp,#DFhi_len
        BPL     modf_truncate_top

        ADDS    tmp,tmp,#32
        BMI     modf_big

        MOV     a4,dOPl,LSR tmp
        MOV     a4,a4,LSL tmp
        ASSERT  a4>dOPh
        STMIA   a3,{dOPh,a4}
        ASSERT  dOP2l=a4
        EOR     dOP2h,dOP1h,#Sign_bit
        B       _dadd

modf_truncate_top
        MOV     a4,dOPh,LSR tmp
        MOV     a4,a4,LSL tmp
        MOV     tmp,#0  
        ASSERT  tmp>a4
        STMIA   a3,{a4,tmp}
        EOR     dOP2h,a4,#Sign_bit
        MOV     dOP2l,#0
        B       _dadd

modf_big

; The number is so big that it has no fractional part.

        STMIA   a3,{dOPh,dOPl}
        MOV     dOPh,#0
        MOV     dOPl,#0
        ReturnToLR

modf_small

; The number is so small that it has a zero integer part.

        MOV     a4,#0
        MOV     tmp,#0
        STMIA   a3,{a4,tmp}
        ReturnToLR

        ]       

;===========================================================================

        [ :DEF: floor_s

        EXPORT  floor
        EXPORT  ceil

mask    RN 12

        ; Floor - Round to an integer towards -Inf

floor   EnterWithLR
        MOVS    exp, dOPh, LSL #1
        BCS     ceil_1
floor_1        
        MOV     exp, exp, LSR #21
        RSB     exp, exp, #1088                 ; 1088 is first 8-bit constant > 1023+53
        RSBS    exp, exp, #65
        BLO     floor_exp_overflow              ; exp > 1088 or exp < 1023 -> overflow
        ; exp is number of fraction bits to preserve (0 .. 65) 
        RSBS    exp, exp, #20                   ; number of bits to clear in high word
        MOV     mask, #-1
        ANDGE   dOPh, dOPh, mask, LSL exp       ; clear exp bits in high word
        MOVGE   dOPl, #0
        ReturnToLR GE
        RSB     exp, exp, #0                    ; number of bits to preserve in low word
        BIC     dOPl, dOPl, mask, LSR exp       ; preserve exp bits in low word
        ReturnToLR
        
floor_exp_overflow                              ; PL if exp too large, MI too small
        ANDMI   dOPh, dOPh, #Sign_bit           ; create signed zero
        MOVMI   dOPl, #0
        ReturnToLR
        
        
        ; Ceil - Round to an integer towards +Inf

ceil    EnterWithLR
        MOVS    exp, dOPh, LSL #1
        BCS     floor_1
ceil_1        
        MOV     exp, exp, LSR #21
        RSB     exp, exp, #1088
        RSBS    exp, exp, #65
        BLO     ceil_exp_overflow               ; exp > 1088 or exp < 1023 -> overflow
        ; exp is number of fraction bits to preserve (0 .. 65) 
        MOV     mask, #-1
        SUBS    exp, exp, #20                   ; number of bits to preserve in low word
        BGT     ceil_low
        ADD     exp, exp, #32                   ; number of bits to preserve in high word
        ADDS    dOPl, dOPl, #-1                 ; round up low word
        ADC     dOPh, dOPh, mask, LSR exp       ; round up high word
        BIC     dOPh, dOPh, mask, LSR exp       ; clear exp bits in high word
        MOV     dOPl, #0
        ReturnToLR
        
ceil_low        
        ADDS    dOPl, dOPl, mask, LSR exp       ; round up low word
        BIC     dOPl, dOPl, mask, LSR exp       ; clear exp bits in low word
        ReturnToLR CC
        ADD     dOPh, dOPh, #1                  ; round up high word
        ReturnToLR

ceil_exp_overflow                               ; PL if exp too large, MI too small
        ReturnToLR PL
        ORRS    tmp, dOPl, dOPh, LSL #1         ; zero?
        ANDNE   dOPh, dOPh, #Sign_bit
        ORRNE   dOPh, dOPh, #0x30000000         ; no, create +-1.0
        ORRNE   dOPh, dOPh, #0x0FF00000
        MOVNE   dOPl, #0
        ReturnToLR

        ]

;===========================================================================

        END
