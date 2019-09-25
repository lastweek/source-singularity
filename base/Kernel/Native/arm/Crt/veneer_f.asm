;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; veneer_f.s - float add/sub/mul/div
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author
;

; Local storage size and offsets
LOC_SIZE   EQU  0x18
OrgOp2l    EQU  0x14
OrgOp1l    EQU  0x10
ExDResl    EQU  0x08
ExOp2l     EQU  0x00
NewResl    EQU  0x10


        GET     fpe.asm
        GET     kxarm.inc


a       RN 0
b       RN 1
tmp     RN 12
mask    RN 12
expa    RN 2
expb    RN 3
exp     RN expa
sign    RN expb
shift   RN expb
res     RN expb
guess   RN 14
num     RN b
den     RN a
div     RN 3



;===============================================================================
;
; RDCFix:
; BUGBUG: These comments aren't necessarily right anymore.
;
;


; __adds/__subs:
;
;   Upon entry the signs are checked, and if they are not equal, control is given
;   to the inverse routine while negating the second operand. Ie. __adds(+A,-B) ->
;   __subs(+A,+B) and __subs(-A,+B) -> __adds(-A,-B). After this check the signs are 
;   known to be equal.
; 
;   The operands are sorted to ensure that A >= B. This enables many checks to
;   be simplified: (A == 0) || (B == 0) reduces to (B == 0). The calculations
;   are also simpler: only operand B needs to be shifted. Unsigned arithmetic
;   is used to compare the packed numbers, since we want to have the operand with 
;   the largest magnitude as operand A.
;
;   Special cases, namely zeroes, infinities, denormals and Not-a-Numbers (NaNs) 
;   are checked for on entry. If one of the operands is special, a jump is made
;   to handle these cases out of line to keep overhead for the general case as 
;   low as possible. Because the operands are sorted, only 2 checks need to be
;   made: operand A is checked for NaN, while operand B is checked for zero.   
;
;   As the signs of the operands are known to be equal and the operands
;   are ordered, the sign of the result is the sign of one of the operands.
;   Since the exponent can only change a little (one in __adds, and often little
;   in __subs), the sign and exponent are not separated.
;   
;   In __adds, the operands are added with the smallest one shifted right with the
;   exponent difference. The fraction might be larger then 1.0, and is renormalised 
;   if neccesary (max 1 right shift needed). The exponent is adjusted with -1 
;   (+ 1 if the fraction was >= 2.0) to counter for the leading bit when the
;   fraction and exponent are combined (using an ADD instruction).
;
;   In __subs, operand B is subtracted from a, after being shifted right with the
;   exponent difference. The result cannot be negative since A >= B, but it can
;   result in a unnormalized number (as the high bits of A and B might cancel out).
;   The common case results in the exponent being adjusted with +0 or -1, this is
;   when the MSB is still set, or when the next bit is set. In the last case 
;   underflow to a denormalized number is possible. Rounding proceeds as normal.
;   When 2 or more leading bits of the result are clear, the result must be 
;   normalized. If the resulting exponent is smaller than zero, denormalization
;   follows. No rounding is necessary (the round bit is zero since we shifted 
;   left by at least 2 bits). 
;
;   In the rounding stage, the exponent is recombined with the fraction 
;   which leading bit is still set (if it is normalized). This causes the
;   exponent to increment by one. Therefore, the exponent has been decremented
;   in an earlier stage.
;   The round-bit is calculated in the result by using more precision than 
;   necessary. After the result is shifted right to remove thse, the carry 
;   contains the roundbit.
;   The guard bits are in the second operand, which are calculated by 
;   left shifting. This is only necessary if the roundbit was set.
;   Round to even is implemented by always rounding upwards, and
;   clearing the LSB in case the guard bits were all zero. Thus an odd value will
;   be rounded up, while an even value will not. While rounding, the fraction may
;   become too large (>= 2.0), at which time the exponent must be incremented and 
;   the fraction shifted right. However, this doesn't need extra code, since 
;   exponent and fraction are already combined: the overflow from the fraction 
;   increments the exponent. Note that this means a denormalized number might 
;   become normalized while rounding!
;   
;   For __adds, overflow is being checked after rounding by adding 1 to the exponent. 
;   If the result was overflowed, the sign bit inverts (overflowed exponent is 255, 
;   and 255+1 negates the sign bit). Note that overflow can only occur after 
;   renormalization, or during rounding, but not in both.
;   Overflow cannot occur in __subs.
;
;   If one of the operands is an uncommon number, the following happens:
;   If the largest operand is a NaN, an Invalid Operation is raised (which 
;   returns the NaN if it is a quiet NaN).
;   For __adds, infinities are returned unaltered (inf + inf = inf), but in __subs a 
;   Invalid Operation exception is raised for inf - inf.
;   If the smallest operand is a zero, the other operand is returned (thus A + 0
;   -> A, A - 0 -> A, but a special case is -0 - -0 -> +0).
;   Denormalized numbers are handled by decoding an unnormalized fraction with 
;   exponent 1. This is to make up for the hidden bit which is clear in 
;   denormalized numbers. Normal addition or subtraction can now proceed without any 
;   modification (the algorithms don't rely on the operands being normalized). 
;   The result can be a denormalized number or a normalized number.
;
;   Frsb (B - A) is implemented by negating both signs on input of __subs. Its use
;   is mainly intended for code size optimization.
;
;===========================================================================

        [ :DEF: add_s

	AREA   |.text|, CODE, READONLY

        Export  __adds
        Export  __subs
        Export  __fArithReturn         ;; RDCFix: Should move to common area
        Export  __fArithNaNCheck       ;; RDCFix: Should move to common area
        Export  __flt_underflow        ;; RDCFix: Should move to common area
        IMPORT  FPE_Raise
        [ :DEF: thumb
        CODE32
        ]          

; Prologues for __adds, __subs, __muls, and __divs must be the same.
    NESTED_ENTRY __subs
        EnterWithLR_16
        STMFD   sp!, {lr}               ; Save return address
        SUB     sp, sp, #LOC_SIZE       ; Allocate stack space
    PROLOG_END
        STR     r1, [sp, #OrgOp2l]      ; Save original args in case of exception
        MOV     r14, #_FpSubS           ; Initialize no exceptions, float sub
        STR     r0, [sp, #OrgOp1l]      ; Save original args in case of exception
        B       fsubtract

    ENTRY_END __subs



; Prologues for __adds, __subs, __muls, and __divs must be the same.
    NESTED_ENTRY __adds
        EnterWithLR_16
        STMFD   sp!, {lr}               ; Save return address
        SUB     sp, sp, #LOC_SIZE       ; Allocate stack space
    PROLOG_END
        STR     r1, [sp, #OrgOp2l]      ; Save original args in case of exception
        MOV     r14, #_FpAddS           ; Initialize no exceptions, float add
        STR     r0, [sp, #OrgOp1l]      ; Save original args in case of exception
        B       faddition





_faddn                                  ; Branch to here from subtract
        EOR     b, b, #1 << 31
        B       _fadd1


faddition
        ; if the signs are unequal, it is a subtract
        TEQ     a, b                    
        BMI     _fsubn
_fadd1        
        ; swap a and b so that a >= b
        SUBS    tmp, a, b
        SUBLO   a, a, tmp
        ADDLO   b, b, tmp
        ; decode exponents, and filter out special cases        
        MOV     exp, a, LSR #23         ; exp = sign<<8 + exponent
        SUB     shift, exp, b, LSR #23  ; shift = 0..254 (sign bits cancel out)
        MOV     tmp, #255 << 24 
        TST     tmp, b, LSL #1          ; check for denorm/zero
        TEQNE   tmp, exp, LSL #24       ; check for inf/NaN
        BEQ     fadd_uncommon           ; handle zeroes/denorms/infs/NaNs
        ; decode fractions and add the leading one      
        MOV     tmp, #1 << 31
        ORR     a, tmp, a, LSL #8       ; a = 1.frac_a
        ORR     b, tmp, b, LSL #8       ; b = 1.frac_b

fadd_add                                
                                        ; Check for inexact where all bits lost
        CMP     shift, #24              ; Shift amount >= 24?
        ORRGE   r14, r14, #INX_bit      ; Set inexact (note b != +/-0)
        BGE     fadd_add_core
        RSB     tmp, shift, #24         ; Number of bits lost
        MOVS    tmp, b, LSL tmp         ; Check lower bits of lesser operand
        ORRNE   r14, r14, #INX_bit      ; If bits set, then inexact
        

fadd_add_core                           ; do the addition and renormalise 
        ADDS    a, a, b, LSR shift      ; CS if a >= 2.0     
        
        BCS     fadd_carry
        ADD     exp, exp, #-1           ; adjust exp for leading bit
        MOVS    a, a, LSR #8            ; CS -> round up (never EQ)
        ADC     a, a, exp, LSL #23      ; combine sign, exp & fraction and round
        BCC     __fArithReturn
        RSB     shift, shift, #25       
        MOVS    b, b, LSL shift         ; calc guard bits: CS,EQ -> round to even
        MOV     tmp, a, LSL #1
        CMNNE   tmp, #1 << 24           ; check for overflow (if not round to even)
        BCC     __fArithReturn          ; return if NOT(overflow OR round to even)
        BICEQ   a, a, #1                ; round to even
        CMN     tmp, #1 << 24           ; check for overflow
        BCC     __fArithReturn

fadd_overflow                           ; sign in a is correct
        ORR     r14, r14, #OVF_bit :OR: INX_bit
                                        ; Set overflow and inexact
        MOVS    r0, r0                  ; Check sign of result
        MOV     r1, #0xFF               ; Load up a correctly signed INF
        MOV     r0, r1, LSL #23         ; Move unsigned INF into result
        ORRMI   r0, r0, #0x80000000     ; Set sign bit if result negative
        B       __fArithReturn
                
fadd_carry
        MOV     a, a, RRX               ; restore leading bit
        MOVS    tmp, a, ROR #8          ; Check for inexact
        ORRMI   r14, r14, #INX_bit      ; Set inexact if bit set
        MOVS    a, a, LSR #8            ; CS -> round up (never EQ)
        ADC     a, a, exp, LSL #23      ; combine sign, exp & fraction and round
        MOV     tmp, a, LSL #1
        CMNCC   tmp, #1 << 24           ; check for overflow (if not round to even)
        BCC     __fArithReturn
        CMN     tmp, #1 << 24
        BCS     fadd_overflow
        RSB     shift, shift, #24
        MOVS    b, b, LSL shift         ; doesn't set carry if shift = 24!
        BICEQ   a, a, #1
        B       __fArithReturn


fadd_uncommon                   
        ; handle denorms, infinities and NaNs
        TEQ     tmp, exp, LSL #24       ; filter out NaN and infinites (EQ)
        BEQ     fadd_inf_NaN
        ; fast check for zeroes
        MOVS    tmp, b, LSL #1          ; EQ if b is zero
        BEQ     __fArithReturn          ; return A + 0 = A
        ; b is denornalized, a might be                 
        MOV     a, a, LSL #8            ; a = 0.frac_a
        MOV     b, b, LSL #8            ; b = 0.frac_b
        TST     exp, #255               ; a denormalized? (exp == 0 -> EQ)
        ORRNE   a, a, #1 << 31          ; no denorm, add leading one
        SUBNE   shift, shift, #1        ; correct shift
        ADDEQ   exp, exp, #1            ; both denorms - correct exp
        B       fadd_add

fadd_inf_NaN
        ; handle infinities and NaNs - a is infinite or NaN, b might be
        MOVS    tmp, a, LSL #9          ; EQ if a inf, NE if a NaN              
        BEQ     __fArithReturn
        B       __fArithNaNCheck
         

_fsubn                                  ; Branch here from add
        EOR     b, b, #1 << 31
        B       _fsub1
                

fsubtract
        ; if the signs are unequal, it is an addition
        TEQ     a, b
        BMI     _faddn
_fsub1        
        ; swap a and b so that a >= b
        SUBS    tmp, a, b
        EORLO   tmp, tmp, #1 << 31      ; negate both opnds (A - B = -B - -A)   
        SUBLO   a, a, tmp
        ADDLO   b, b, tmp       
        ; decode exponents, and filter out special cases
        MOV     exp, a, LSR #23         ; exp = sign<<8 + exponent
        SUB     shift, exp, b, LSR #23  ; shift = 0..254 (sign bits cancel out)
        MOV     tmp, #255 << 24 
        TST     tmp, b, LSL #1          ; check for denorm/zero
        TEQNE   tmp, exp, LSL #24       ; check for inf/NaN
        BEQ     fsub_uncommon           ; handle zeroes/denorms/infs/NaNs
        ; decode fractions and add the leading one
        ORR     a, tmp, a, LSL #1
        BIC     a, a, #0xFE000000
        ORR     b, tmp, b, LSL #1

        ; Check for inexact
        CMP     shift, #32              ; Shift amount >= 31?
        ORRGE   r14, r14, #INX_bit      ; Set inexact (note b != +/-0)
        BGE     fsub_sub_core
        RSB     tmp, shift, #32         ; Number of bits lost
        MOVS    tmp, b, LSL tmp         ; Check lower bits of lesser operand
        ORRNE   r14, r14, #INX_bit      ; If bits set, then inexact

fsub_dosub
        RSB     b, b, #0xFE000000       ; Negate B

fsub_sub_core
        ; do the subtraction and calc number of bits to renormalise (0, 1, >=2)
        ADD     a, a, b, ASR shift
        MOVS    tmp, a, LSL #8          ; CS = 10/11, CC,MI = 01, CC,PL = 00
        BCS     fsub_renorm_0           ; high bit still set - no renormalisation
        BPL     fsub_renormalise        ; high 2 bits clear - renormalise >= 2 bits
        TST     expa, #254              ; exp == 1? (cannot be zero)
        BEQ     fsub_renormalise        ; yes -> underflow to denormalized number
fsub_renorm_1                           
        ; 1 left shift needed, exp -= 1 
        MOV     a, tmp, ASR #8          ; doesn't set carry - no early exit!
; TST tmp, #0xFF           ; RDCFix: Need this?
; ORRNE r14, r14, #INX_bit ; RDCFix: Need this?
        RSBS    shift, shift, #32+1     ; shift can be <= 0...
        MOVLS   shift, #1               ; shift 1 -> CS and NE - always roundup
        MOVS    b, b, LSL shift         ; calc rounding (CS) and guard bits (EQ)
        ADC     a, a, exp, LSL #23      ; recombine sign, exponent and fraction
        BCC     __fArithReturn
        BNE     __fArithReturn
; ORR  r14, r14, #INX_bit  ; RDCFix: Need this?
        BICEQ   a, a, #1                ; round to even
        B       __fArithReturn

fsub_renorm_0   
        ; no renormalisation needed     
                                  ; RDCFix: Is this right?
        MOVS    a, tmp, LSL #32-9       ; Check if we're throwing away any bits
        ORRNE   r14, r14, #INX_bit      ; If we are, set inexact
        MOVS    a, tmp, LSR #9          ; CS -> round up
        ADC     a, a, exp, LSL #23      ; recombine sign, exponent and fraction
        BCC     __fArithReturn
        RSBS    shift, shift, #32-0     ; shift can be <= 0... -> don't round to even
        MOVHSS  b, b, LSL shift         ; EQ -> round to even
        BNE     __fArithReturn
        BICEQ   a, a, #1                ; round to even
        B       __fArithReturn
                        
fsub_renormalise
        ; >= 2 bits renormalisation needed
        MOV     sign, exp, LSR #8
        TST     a, #0x00FF0000          ; bit 16..23 set?
        BNE     fsub_renorm_small
fsub_renorm_large
        ; bit 16..23 clear, >= 8 bits renormalisation
        MOVS    a, a, LSL #8
        BEQ     __fArithReturn          ; return +0 if result is zero
        SUB     exp, exp, #8
        TST     a, #0x00FF0000          ; bit 16..23 set?
        MOVEQ   a, a, LSL #8
        SUBEQ   expa, expa, #8
fsub_renorm_small       
        ; renormalise A until bit 23 is set
        TST     a, #0x00F00000
        MOVEQ   a, a, LSL #4
        SUBEQ   exp, exp, #4
        TST     a, #0x00C00000
        MOVEQ   a, a, LSL #2
        SUBEQ   exp, exp, #2
        CMP     a, #1 << 23
        MOVCC   a, a, LSL #1
        ADC     exp, exp, #-3
        TEQ     sign, exp, LSR #8       ; exponent underflow? (signs differ if so)
        ADDEQ   a, a, exp, LSL #23     ; no rounding necessary
        BEQ     __fArithReturn
        ; underflow to denormalized number
        RSB     exp, exp, #0

;;
;; RDCFix: Move this to a common area (out of the adds/subs routine).
;;
;; Code adapted from except.s __flt_underflow
;;
;; Note that an underflow cannot occur for an add nor a subtract.  This is
;; because the Pegasus FP Specification states that underflow happens if the
;; result is denormal (or zero) after rounding and inexact.  Since the only
;; way we can get a denormal result from an add or subtract is to add/subtract
;; two denormals, and adding/subtracting two denormals is always exact (no
;; shift occurs as the exponents are equal), it is impossible to generate
;; an underflow condition.  Thus, for add and subtract, this code will just
;; generate the correct result.  The result will always be exact.
;;
;; For multiply and divide, inexacts must be detected here.  An inexact here
;; may or may not also raise underflow in __fArithReturn.  It is possible
;; for a normal result to enter here.
;;
;; Register usage:
;;   r0 - underflowed number with leading bit set, round and guard bits
;;   r2 - shift count for a (0 - exp)
;;   r3 - sign in bit 0 (negative if set)
;;
__flt_underflow
          ; RDCFix: What part of r2 is valid?  Only low byte?
          ;         I don't completely understand this.
                                       ; Check for inexact
        TST     r2, #0x000000E0        ; Check for shift >= 32
        ORRNE   r14, r14, #INX_bit     ; If shift >= 32, lost all bits: inexact

fp_underflow_calc_result
        MOV     r3, r3, LSL #31        ; Position sign into sign bit position
        ORRS    r3, r3, r0, LSR r2     ; Combine sign, exponent, and mantissa
        BCS     fp_underflow_carry
        RSB     r2, r2, #32            ; Check for inexact to see if we shifted
        MOVS    r0, r0, LSL r2         ;   any set bits out to the right
        ORRNE   r14, r14, #INX_bit     ; If we did, set inexact
        MOV     r0, r3
        B       __fArithReturn

fp_underflow_carry
        ORR     r14, r14, #INX_bit     ; RDCFix: Why is inexact guaranteed here?
        RSB     r2, r2, #33
        MOVS    r2, r0, LSL r2
        ADC     r0, r3, #0
        BICEQ   r0, r0, #1
        B       __fArithReturn



fsub_uncommon
        TEQ     tmp, exp, LSL #24       ; EQ if NaN
        BEQ     fsub_inf_NaN
fsub_denorm     ; here b is denormalized or zero, a might be a normal number
        ; check whether a or b is zero - fast case
        MOVS    tmp, a, LSL #1
        MOVEQ   a, #0                   ; -0 - -0 = +0
        MOVS    b, b, LSL #1            ; EQ if b == 0 or a == 0
        BEQ     __fArithReturn          ; return a - 0 = a
        ; b is denormalized, a might be                 
        TST     exp, #255
        BIC     a, tmp, #0xFF000000
        ORRNE   a, a, #1 << 24
        SUBNE   shift, shift, #1
        ADDEQ   exp, exp, #1

        ; Check for inexact
        CMP     shift, #31              ; Shift amount >= 31?
        ORRGE   r14, r14, #INX_bit      ; Set inexact (note b != +/-0)
        BGE     fsub_sub_core
        RSB     tmp, shift, #31         ; Number of bits lost
        MOVS    tmp, b, LSL tmp         ; Check lower bits of lesser operand
        ORRNE   r14, r14, #INX_bit      ; If bits set, then inexact

        RSB     b, b, #0
        B       fsub_sub_core


fsub_inf_NaN
        ; handle infinities and NaNs - a is infinite or a NaN, b might be
        MOVS    tmp, a, LSL #9          ; a NaN? (NE)
        BNE     __fArithNaNCheck
        CMP     a, b                    ; a is infinite, b too? (EQ)
        ORREQ   r14, r14, #IVO_bit      ; Set invalid operation if is
        ORREQ   r0, r0, #fSignalBit     ; Make INF into a QNaN
        B       __fArithReturn          ; yes, a & b infinite -> generate IVO
                       

;;
;; _fArithReturn
;;
;; Register Usage:
;;   r0 - Default return value
;;   r14 - Exception information
;;
;; Stack:
;;   | Caller's Frame |
;;   |                |
;;   +----------------+
;;   | Return Address |
;;   +----------------+
;;   | Original Arg2  |
;;   +----------------+
;;   | Original Arg1  |  <-- SP
;;   +----------------+
;;      Stack Top
;;
;;
;; Standard return path for single precision arithmetic routines.  It checks
;; if any exceptions occurred.  If any exceptional conditions occurred, then
;; an FPIEEE exception record is allocated and filled with the approptiate
;; values and the exception handler called.  Upon returning, the possibly
;; changed result is loaded from the returned union, the stack space is
;; restored, and control is returned to the caller.  If no exceptions occurred,
;; then the default result is returned.
;;
__fArithReturn
       TST     r14, #FPECause_mask      ; Any exceptions?
       ADDEQ   sp, sp, #LOC_SIZE        ; None so pop original args
  IF Interworking :LOR: Thumbing
       LDMEQFD sp!, {lr}                ;   and return
       BXEQ    lr
  ELSE
       LDMEQFD sp!, {pc}                ;   and return
  ENDIF
                                        ; Else we have an exception
                                        ; Check for underflow (denormal & inexact)
       MOV     tmp, #0xFF000000         ; Load up exponent mask << 1
       TST     r0, tmp, LSR #1          ; See if exponent is zero
       BNE     no_underflow             ; Non-zero exponent so no underflow possible
       TST     r14, #INX_bit            ; See if inexact bit is set
       ORRNE   r14, r14, #UNF_bit       ; If inexact, then underflow
no_underflow
       STR     r0, [sp, #ExDResl]       ; Push default result
       LDR     r0, [sp, #OrgOp2l]       ; Get orig Arg2 off stack
       STR     r0, [sp, #ExOp2l]        ; Push Arg2
       LDR     r2, [sp, #OrgOp1l]       ; Get orig Arg1 off stack
       MOV     r1, r14                  ; ExInfo
       ADD     r0, sp, #NewResl         ; Pointer to result from ex. handler
                                        ;   Note that this clobbers original
       CALL    FPE_Raise

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF                                   ;   Arg1 and Arg2 on the stack

       LDR     r0, [sp, #NewResl]       ; Get returned result
       ADD     sp, sp, #LOC_SIZE        ; Pop orig. args and arg passing space
  IF Interworking :LOR: Thumbing
       LDMFD   sp!, {lr}                ; Return
       BX      lr
  ELSE
       LDMFD   sp!, {pc}                ; Return
  ENDIF



;; __fArithNaNCheck
;;
;; Checks both operands for SNaNs and raises and exception if one is present.
;; If no SNaNs are present, then a QNaN is returned.  At least one of Arg1
;; and Arg2 must be a NaN.
;;
;; Register usage:
;;   r0 - Arg1 (must be a NaN if Arg2 is not)
;;   r1 - Arg2 (must be a NaN if Arg1 is not)
;;   r14 - FP exception information
;;
;; Code adapted from except.s.
__fArithNaNCheck
        MOV     a4, #0x01000000
        CMN     a4, fOP1, LSL #1
        BLS     fcheck_opnd2_NaN
fcheck_opnd1_NaN
        TST     fOP1, #fSignalBit
        ORREQ   fOP1, fOP1, #fSignalBit
        ORREQ   r14, r14, #IVO_bit
        BEQ     __fArithReturn
        CMN     a4, fOP2, LSL #1
        BLS     __fArithReturn
fcheck_opnd2_NaN
        MOV     fOP1, fOP2
        TST     fOP1, #fSignalBit
        ORREQ   fOP1, fOP1, #fSignalBit
        ORREQ   r14, r14, #IVO_bit
        B       __fArithReturn

    ENTRY_END __adds
        ]


;------------------------------------------------------------------------------

        [ :DEF: mul_s

	AREA   |.text|, CODE, READONLY

        Export  __muls
        Export  fmul_fdiv_overflow
        IMPORT  __fArithReturn
        IMPORT  __fArithNaNCheck
        IMPORT  __flt_normalise2
        IMPORT  __flt_underflow


        MACRO
        MULL48  $a, $b, $res, $tmp
        ; a = AAAAAA00
        ; b = BBBBBB00
        
        UMULL   $tmp, $res, $a, $b
        SUB     exp, exp, #128 << 16    ; subtract bias+1 - 0..253 normal       
        CMP     $tmp, #0
        ORRNE   $res, $res, #1
        
        MEND            
        
        
        
    ; Prologues for __adds, __subs, __muls, and __divs must be the same
    NESTED_ENTRY __muls
        EnterWithLR_16
        STMFD   sp!, {lr}               ; Save return address
        SUB     sp, sp, #LOC_SIZE       ; Allocate local storage
    PROLOG_END
        STR     r0, [sp, #OrgOp1l]      ; Save off args in case of exception
        MOV     r14, #_FpMulS           ; Initialize no exceptions, float multiply
        STR     r1, [sp, #OrgOp2l]

        MOV     mask, #255 << 16
        ANDS    expa, mask, a, LSR #7
        ANDNES  expb, mask, b, LSR #7
        TEQNE   expa, mask
        TEQNE   expb, mask
        BEQ     fmul_uncommon
        TEQ     a, b
        ORRMI   expa, expa, #1 << 8
        MOV     mask, #1 << 31
        ORR     a, mask, a, LSL #8
        ORR     b, mask, b, LSL #8
fmul_mul        
        ADD     exp, expa, expb
        MULL48  a, b, res, tmp 

   ;; r1 now available for scratch

        CMP     res, #&80000000
    ORRCS r1, tmp, res, LSL #24        ; Check res low 8 bits, low bits
        MOVLO   res, res, LSL #1
        ADC     exp, exp, exp, ASR #16  ; recombine sign & exp, and adjust exp
    ORRS r1, tmp, res, LSL #25         ; check low 7 bits, low bits
    ORRNE r14, r14, #INX_bit
    
fmul_round
        MOVS    a, res, LSR #8          ; never EQ (leading bit)
        ADC     a, a, exp, LSL #23      ; add fraction, and round
        TSTCS   res, #0x7f              ; EQ -> round to even
        CMPNE   exp, #252 << 16         ; possible overflow? (never EQ)
        BLO     __fArithReturn          ; return if no overflow and no round to even
        BICEQ   a, a, #1                ; delayed round to even
        CMP     exp, #252 << 16
        BLO     __fArithReturn
        BPL     fmul_fdiv_overflow

fmul_underflow                          ; result may be normalised after rounding
        MOV     r1, a, LSL #1
        SUB     r1, r1, #1 << 24
        CMP     r1, #3 << 24           ; result exp in 1..3 -> return
        BLO     __fArithReturn
        MOV     a, res
        MVN     sign, exp, LSR #8       ; correct sign from underflowed exponent
        RSB     exp, exp, #8            ; calc denormalising shift
        B       __flt_underflow

;;
;; fmul_fdiv_overflow is shared between __muls and __divs.
;;
fmul_fdiv_overflow                      ; result might not be overflowed after all
	MOV	tmp, a, LSL #1
	ADD	tmp, tmp, #1 << 24
	CMP	tmp, #254 << 24		; Check for exp = 253 or 254
	BHS	__fArithReturn		; no overflow - 9 cycles overhead
	SUBS	a, a, exp, LSL #7       ; get correct sign
	ORR	r14, r14, #OVF_bit :OR: INX_bit	; Set overflow and inexact
        MOV     a, #0x7F000000          ; Create a properly signed INF
        ORR     a, a, #0x00800000       ;   ...
        ORRMI   a, a, #0x80000000       ;   ...
	B	__fArithReturn

        
        
fmul_uncommon                           ; a or b denorm/NaN/inf
        AND     expb, mask, b, LSR #7
        TEQ     a, b
        ORRMI   expa, expa, #1 << 8
        CMP     expa, mask
        CMPLO   expb, mask
        BHS     fmul_inf_NaN
        ; a or b denorm, first check for zero case
        MOVS    tmp, a, LSL #1
        MOVNES  tmp, b, LSL #1
        MOVEQ   a, expa, LSL #23        ; return signed zero
        BEQ     __fArithReturn
        ; normalise operands
        ADR     tmp, fmul_mul
        B       __flt_normalise2
        
        
fmul_inf_NaN                            ; a or b is a NaN or infinite
        MOV     tmp, #0x01000000
        CMN     tmp, a, LSL #1
        CMNLS   tmp, b, LSL #1  
        BHI     __fArithNaNCheck
        ; now a or b is infinite - check that a and b are non-zero
        MOVS    tmp, a, LSL #1          ; a zero?
        MOVNES  tmp, b, LSL #1          ; b zero?
        ORRNE   expa, expa, #255        ; create infinite
        MOV     a, expa, LSL #23        ;   with correct sign
                                        ; If NE: a & b nonzero, return infinite
        ORREQ   r14, r14, #IVO_bit      ; If EQ: inf * 0 signals an exception
        ORREQ   a, a, #0x7F000000       ; Create a QNaN
        ORREQ   a, a, #0x00C00000       ;   ...
        B       __fArithReturn

    ENTRY_END __muls
        ]

;---------------------------------------------------------------------------

        [ :DEF: div_s

	AREA   |.text|, CODE, READONLY

        Export  __divs
        IMPORT  __flt_normalise2
        IMPORT  __fArithReturn
        IMPORT  __flt_underflow
        IMPORT  fmul_fdiv_overflow
        IMPORT  __fArithNaNCheck

        ; TODO: * halve lookup table size 
        

        DCB   0, 0, 0, 0
        DCB   1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15, 17
        DCB  18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 35, 36
        DCB  37, 39, 40, 41, 43, 44, 46, 47, 48, 50, 51, 53, 54, 56, 57, 59
        DCB  60, 62, 63, 65, 66, 68, 70, 71, 73, 74, 76, 78, 80, 81, 83, 85
        DCB  87, 88, 90, 92, 94, 96, 98,100,102,104,106,108,110,112,114,116
        DCB 118,120,122,125,127,129,131,134,136,138,141,143,146,148,151,153
        DCB 156,158,161,164,166,169,172,175,178,180,183,186,189,192,195,199
        DCB 202,205,208,212,215,218,222,225,229,233,236,240,244,248,252,255     
fdiv_tab
        
    ; Prologues for __adds, __subs, __muls, and __divs must be the same
    NESTED_ENTRY __divs
        EnterWithLR_16
        STMFD   sp!, {lr}               ; Save return address
        SUB     sp, sp, #LOC_SIZE       ; Allocate local storage
    PROLOG_END
        STR     r0, [sp, #OrgOp1l]      ; Save off args in case of exception
        MOV     r14, #_FpDivS           ; Initialize no exceptions, float divide 
                                        ;   Note that r14 is also used by "guess"
        STR     r1, [sp, #OrgOp2l]
        MOV     mask, #255 << 16
        ANDS    expa, mask, a, LSR #7
        ANDNES  expb, mask, b, LSR #7
        CMPNE   expa, #255 << 16
        CMPNE   expb, #255 << 16
        BEQ     fdiv_uncommon
        TEQ     a, b
        ADDMI   expa, expa, #1 << 8
        ORR     tmp, a, #1 << 23
        ORR     den, b, #1 << 23
        BIC     num, tmp, #0xFF000000
        BIC     den, den, #0xFF000000
fdiv_div        
        ; calculate exponent and find leading bit of result
        SUB     exp, expa, expb
        CMP     num, den
        ; this code fills result delay slots 
        ;MOVLO   num, num, LSL #1         ; shift so that div >= 1 << 23
        ;ADD     exp, exp, #(127-2) << 16 ; subtract bias (one too small)
        ;ADC     exp, exp, exp, ASR #16   ; calc exp, combine with sign
        
        ; lookup guess of 1/den - use rounded inverted tablelookup
        ADD     tmp, den, #32768 + ((. + 12 - (fdiv_tab + 127)) << 16)
        LDRB    guess, [pc, -tmp, LSR #16]
        RSB     den, den, #0            ; result delay - negate den for MLA
        ADD     guess, guess, #256
        
        ; do one Newton-Rhapson iteration to increase precision to 15 bits
        MUL     tmp, den, guess
        MOVLO   num, num, LSL #1        ; result delay - shift so that div >= 1 << 23
        MOV     tmp, tmp, ASR #4
        MUL     div, tmp, guess
        MOV     guess, guess, LSL #7
        ADD     guess, guess, div, ASR #21
        
        ; long division - 13 bits
        MOV     tmp, num, LSR #10
        MUL     tmp, guess, tmp
        MOV     num, num, LSL #12
        MOV     div, tmp, LSR #17
        MLA     num, den, div, num
        ADD     exp, exp, #(127-2) << 16 ; result delay - subtract bias (one too small)
        
        ; long division - 11 bits (can do 12)
        MOV     tmp, num, LSR #10
        MUL     tmp, guess, tmp
        MOV     num, num, LSL #11
        MOV     tmp, tmp, LSR #18
        MLA     num, den, tmp, num
        ADC     exp, exp, exp, ASR #16  ; result delay - calc exp, combine with sign
        
        ; correct div (may be one too small)
        CMN     num, den
        ADDHS   num, num, den           ; now num < den
        ADC     div, tmp, div, LSL #11

        MOV     r14, #_FpDivS           ; Reinitialize no exceptions, float divide
                                        ;   Note that r14 was used for "guess"
        CMP     num, #0                 ; Check for inexact
        ORRNE   r14, r14, #INX_bit      ; Set inexact if bits lost
        CMN     den, num, LSL #1        ; CS -> round, EQ -> round to even
        ADC     a, div, exp, LSL #23    ; recombine exp and fraction - increment exp   
        CMPNE   exp, #252 << 16         ; exp < 252 cannot overflow
        BLO     __fArithReturn
        BICEQ   a, a, #1
        CMP     exp, #252 << 16         ; exp < 252 cannot overflow
        BLO     __fArithReturn
        BPL     fmul_fdiv_overflow
        
fdiv_underflow                          ; result may be normalised after rounding
        MOV     tmp, a, LSL #1
        SUB     tmp, tmp, #1 << 24
        CMP     tmp, #3 << 24           ; result exp in 1..3 -> return
        BLO     __fArithReturn
        CMP     num, #1                 ; num contains implicit guard bits
        ADC     a, div, div             ; add explicit guard bit (1 if num > 0)
        MVN     sign, exp, LSR #8       ; get correct sign
        RSB     exp, exp, #1            ; calc 1 - exp
        B       __flt_underflow

        
fdiv_uncommon
        AND     expb, mask, b, LSR #7
        TEQ     a, b
        ORRMI   expa, expa, #1 << 8
        CMP     expa, mask
        CMPLO   expb, mask
        BHS     fdiv_inf_NaN
        ; a or b denorm, first check for zero case
        MOVS    tmp, b, LSL #1
        BEQ     fdiv_divbyzero          ; a / 0 -> division by zero
        MOVS    tmp, a, LSL #1          ; 0 / b -> 0
        MOVEQ   a, expa, LSL #23        ; return signed zero
        BEQ     __fArithReturn
        ; normalise operands
        ADR     tmp, fdiv_div1
        B       __flt_normalise2 
        
fdiv_div1                               ; remove... quick hack
        MOV     tmp, a, LSR #8
        MOV     den, b, LSR #8
        MOV     num, tmp
        B       fdiv_div        
        
        
fdiv_inf_NaN                            ; a or b is a NaN or infinite
        MOV     tmp, #0x01000000
        CMN     tmp, a, LSL #1
        CMNLS   tmp, b, LSL #1
        BHI     __fArithNaNCheck
        ; now a or b is infinite - check that a and b are not both infinite
        CMN     tmp, a, LSL #1
        CMNEQ   tmp, b, LSL #1
        MOVEQ   a, expa, LSL #23
        ORREQ   r14, r14, #IVO_bit      ; Set invalid
        ORREQ   a, a, #0x7F000000       ; Create QNaN
        ORREQ   a, a, #0x00C00000       ;   ...
        BEQ     __fArithReturn          ; inf / inf -> IVO
        CMN     tmp, b, LSL #1          ; b inf? (EQ)
        MOVEQ   a, #0                   ; a / inf -> signed zero
        BICNE   a, a, #1 << 31          ; inf / b = inf (even inf / 0 = inf)     
        ORR     a, a, expa, LSL #23     ; set sign
        B       __fArithReturn
                
fdiv_divbyzero                          ; b zero
        MOVS    tmp, a, LSL #1
        ORREQ   r14, r14, #IVO_bit      ; 0 / 0 -> IVO
        ORREQ   a, a, #0x7F000000       ; Create QNaN
        ORREQ   a, a, #0x00C00000       ;   ...
        ORRNE   r14, r14, #DVZ_bit      ; A / 0 -> DVZ
        MOVNE   a, expa, LSL #23        ; set sign of result (returns signed inf) 
        ORRNE   a, a, #0x7F000000       ; Create properly signed INF
        ORRNE   a, a, #0x00800000       ;   ...
        B       __fArithReturn

    ENTRY_END __divs
        ]

;---------------------------------------------------------------------------

        [ :DEF: fnorm2_s

	AREA   |.text|, CODE, READONLY

        EXPORT  __flt_normalise2

        ; normalise a or b (or both). One operand is denormalised
        ; a = x0AAAAAA, bits 0-22 nonzero, bits 23-30 zero
        ; normalise such that bit 23 = 1
        ; return to address in tmp
        
        [ :DEF: thumb
        CODE32
        ]
__flt_normalise2
        MOV     a, a, LSL #8
        MOV     b, b, LSL #8
        TST     expa, #255 << 16
        BNE     fnorm_b
fnorm_a         
        CMP     a, #1 << 16
        SUBLO   expa, expa, #16 << 16
        MOVLO   a, a, LSL #16
        TST     a, #255 << 24
        SUBEQ   expa, expa, #8 << 16
        MOVEQ   a, a, LSL #8
        TST     a, #15 << 28
        SUBEQ   expa, expa, #4 << 16
        MOVEQ   a, a, LSL #4
        TST     a, #3 << 30
        SUBEQ   expa, expa, #2 << 16
        MOVEQS  a, a, LSL #2
        MOVPL   a, a, LSL #1
        ADDMI   expa, expa, #1 << 16
        
        TST     expb, #255 << 16
        ORRNE   b, b, #1 << 31
        MOVNE   pc, tmp
fnorm_b         
        ORR     a, a, #1 << 31
        CMP     b, #1 << 16
        SUBLO   expb, expb, #16 << 16
        MOVLO   b, b, LSL #16
        TST     b, #255 << 24
        SUBEQ   expb, expb, #8 << 16
        MOVEQ   b, b, LSL #8
        TST     b, #15 << 28
        SUBEQ   expb, expb, #4 << 16
        MOVEQ   b, b, LSL #4
        TST     b, #3 << 30
        SUBEQ   expb, expb, #2 << 16
        MOVEQS  b, b, LSL #2
        MOVPL   b, b, LSL #1
        ADDMI   expb, expb, #1 << 16
        MOV     pc, tmp


        ]

;===========================================================================

        END
