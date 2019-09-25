;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; format_e.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

        GET     fpe.asm

	AREA   |.text|, CODE, READONLY

SNaNInf EQU     NaNInfExp_Single - EIExp_bias + SExp_bias
DNaNInf EQU     NaNInfExp_Double - EIExp_bias + DExp_bias

;==============================================================================

        [ :DEF: e2e_s

        EXPORT  _e2e

; Convert a five-word internal value to a three word value
;
; Enters with the partly-constructed internal precision value in OP1sue,
; OP1mhi and OP1mlo, the exponent in RNDexp and the guard/sticky bits in
; Rarith. No truncation is needed, only rounding.

        [ :DEF: thumb
        CODE32
        ]

_e2e
        TST     OP1sue,#Error_bit+Uncommon_bit
        BNE     _e2e_error_or_uncommon

        MOVS    Rtmp,Rarith,LSL #1      ;C<-round, Z<-"tied (or exact) case"
        BEQ     _e2e_exact_or_tied
_e2e_round_by_C
        ADDCSS  OP1mlo,OP1mlo,#1        ;Increment low word
        ADDCSS  OP1mhi,OP1mhi,#1        ;If carry out, increment high word
        MOVCS   OP1mhi,#EIUnits_bit     ;If mantissa overflow, adjust
        ADCS    RNDexp,RNDexp,#0        ; mantissa and exponent

        BMI     _e2e_underflow

;Check for overflow in the usual way

        ADD     tmp,RNDexp,#1
        BIC     tmp,tmp,#Uncommon_bit
        CMP     tmp,#1<<EIExp_len
        MOVGT   a4,#OVF_bits

_e2e_return_value

        AND     OP1sue,OP1sue,#Sign_bit
        ORR     OP1sue,RNDexp,OP1sue
        MOV     pc, lr                  ;Only *ever* called from ARM
                                        ;So no INTERWORK hacks needed!

;In the event of an error just return

_e2e_error_or_uncommon
        MOV     a4,OP1sue
        MOV     pc,lr

_e2e_exact_or_tied
        MOVCSS  Rtmp,OP1mlo,LSR #1      ;If "tied" C<-low mantissa bit
        B       _e2e_round_by_C         ;(If exact, C remains 0)

_e2e_underflow

;We have come out with a negative exponent. If the units bit is unset this
;may be recoverable.

        TST     OP1mhi,#EIUnits_bit
        BNE     _e2e_underflow_recover

_e2e_massive_underflow

;It is not - i.e. this is a normalised number. We return a signed zero.

        MOV     OP1mhi,#0
        MOV     OP1mlo,#0
        AND     OP1sue,OP1sue,#Sign_bit
        MOV     a4, #0
        MOV     pc,lr

_e2e_underflow_recover

;We may be able to shift the mantissa enough to bring the exponent back
;into range.

        MACRO
        I2ECheckBits $n
        MOVS    tmp,OP1mhi,LSR #32-$n
        MOVEQ   tmp,OP1mlo,LSR #32-$n
        ORREQ   OP1mhi,tmp,OP1mhi,LSL #$n
        ADDEQ   RNDexp,RNDexp,#$n
        MEND

        I2ECheckBits 16
        I2ECheckBits 8
        I2ECheckBits 4
        I2ECheckBits 2
        I2ECheckBits 1

        MOVS    RNDexp,RNDexp
        BMI     _e2e_massive_underflow
        BPL     _e2e_return_value

        ]

;===========================================================================

        [ :DEF: eflt_s :LOR: :DEF: efltu_s

;Macro for normalisation

        MACRO
        ExtendNormalise

;The sign bit is stored in OP1sue.

        ORR     OP1sue,OP1sue,#((EIExp_bias+31):AND:&ff00)<<EIExp_pos
        ORR     OP1sue,OP1sue,#((EIExp_bias+31):AND:&00ff)<<EIExp_pos

;Now that we have the basis for the exponent, we do the rounding

        MOVS    tmp,OP1mhi,LSR #16
        MOVEQ   OP1mhi,OP1mhi,LSL #16
        SUBEQ   OP1sue,OP1sue,#16<<EIExp_pos
        MOVS    tmp,OP1mhi,LSR #24
        MOVEQ   OP1mhi,OP1mhi,LSL #8
        SUBEQ   OP1sue,OP1sue,#8<<EIExp_pos
        MOVS    tmp,OP1mhi,LSR #28
        MOVEQ   OP1mhi,OP1mhi,LSL #4
        SUBEQ   OP1sue,OP1sue,#4<<EIExp_pos
        MOVS    tmp,OP1mhi,LSR #30
        MOVEQ   OP1mhi,OP1mhi,LSL #2
        SUBEQ   OP1sue,OP1sue,#2<<EIExp_pos
        MOVS    tmp,OP1mhi,LSR #31
        MOVEQ   OP1mhi,OP1mhi,LSL #1
        SUBEQ   OP1sue,OP1sue,#1<<EIExp_pos

;We want to keep the units bit, which now must be in the top bit of a1.

        MEND

        ]

;..............................................................................

        [ :DEF: eflt_s

        EXPORT  _eflt

_eflt   EnterWithLR
        MOVS    OP1mhi,a1               ;Check for zero and -ve; put in place
        AND     OP1sue,a1,#Sign_bit     ;Extract sign
        RSBMI   OP1mhi,OP1mhi,#0        ;Undo two's complement
        ASSERT  OP1sue = a1
        MOV     OP1mlo,#0               ;This will be done regardless
        ;MOVEQ  OP1sue,#0               ;Return a zero as appropiate
        ;MOVEQ  OP1mhi,#0               ;Already done this move
        ReturnToLR EQ

        ExtendNormalise

        ReturnToLR

        ]

;------------------------------------------------------------------------------

        [ :DEF: efltu_s

        EXPORT  _efltu

_efltu  EnterWithLR
        MOVS    OP1mhi,a1               ;Check for zero and -ve; put in place
        MOV     OP1mlo,#0               ;This will be done regardless
        MOV     OP1sue,#0               ;Return a zero as appropiate
        ;MOVEQ  OP1mhi,#0               ;Already done this move
        ReturnToLR EQ

        ExtendNormalise

        ReturnToLR

        ]

;---------------------------------------------------------------------------

        [ :DEF: norm_op1_s

        EXPORT  __fp_norm_op1

; This routine is called to normalised the first operand on entry to one
; of the veneered functions.

; Takes OP1 is r0,r1,r2 and corrupts tmp (r11).

;Called from ARM code

        [ :DEF: thumb
        CODE32
        ]

__fp_norm_op1

        TST     OP1mhi, #EIUnits_bit
        MOVEQ   pc, lr                  ;Only ever called from ARM - so
                                        ;no INTERWORK hacks needed

        STMFD   r13!,{RNDexp,lr}

        BICS    OP1mhi,OP1mhi,#Sign_bit
        BEQ     __fp_denorm_low

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

        LDMFD   r13!,{RNDexp,pc}

__fp_denorm_low

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

        LDMFD   r13!,{RNDexp,pc}

        ]

;---------------------------------------------------------------------------

        [ :DEF: norm_op2_s

        EXPORT  __fp_norm_op2

; This routine is called to normalised the second operand on entry to one
; of the veneered functions.

; takes OP2 in r4,r5,r6 and corrupts tmp (r11)

; Called from ARM code
        [ :DEF: thumb
        CODE32
        ]

__fp_norm_op2

        TST     OP2mhi, #EIUnits_bit
        MOVEQ   pc, lr

        STMFD   r13!,{OP1sue,lr}

        BICS    OP2mhi,OP2mhi,#Sign_bit
        BEQ     __fp_denorm_low

; The top set bit in the high word, so find out how much to denormalise
; by

        MOVS    OP1sue,OP2mhi,LSR #16
        MOVEQ   OP2mhi,OP2mhi,LSL #16
        MOVEQ   tmp,#16
        MOVNE   tmp,#0
        MOVS    OP1sue,OP2mhi,LSR #24   
        MOVEQ   OP2mhi,OP2mhi,LSL #8
        ADDEQ   tmp,tmp,#8
        MOVS    OP1sue,OP2mhi,LSR #28
        MOVEQ   OP2mhi,OP2mhi,LSL #4
        ADDEQ   tmp,tmp,#4
        MOVS    OP1sue,OP2mhi,LSR #30
        MOVEQ   OP2mhi,OP2mhi,LSL #2
        ADDEQ   tmp,tmp,#2
        MOVS    OP1sue,OP2mhi,LSR #31
        MOVEQ   OP2mhi,OP2mhi,LSL #1
        ADDEQ   tmp,tmp,#1

; tmp now contains the amount to shift by.

        RSB     OP1sue,tmp,#32
        ORR     OP2mhi,OP2mhi,OP2mlo,LSR OP1sue
        MOV     OP2mlo,OP2mlo,LSL tmp

        SUB     OP2sue,OP2sue,tmp
        ADD     OP2sue,OP2sue,#1

        LDMFD   r13!,{OP1sue,pc}

__fp_denorm_low

; The top bit to be set is in OP2mlo

        MOVS    OP1sue,OP2mlo,LSR #16
        MOVEQ   OP2mlo,OP2mlo,LSL #16
        MOVEQ   tmp,#16
        MOVNE   tmp,#0
        MOVS    OP1sue,OP2mlo,LSR #24   
        MOVEQ   OP2mlo,OP2mlo,LSL #8
        ADDEQ   tmp,tmp,#8
        MOVS    OP1sue,OP2mlo,LSR #28
        MOVEQ   OP2mlo,OP2mlo,LSL #4
        ADDEQ   tmp,tmp,#4
        MOVS    OP1sue,OP2mlo,LSR #30
        MOVEQ   OP2mlo,OP2mlo,LSL #2
        ADDEQ   tmp,tmp,#2
        MOVS    OP1sue,OP2mlo,LSR #31
        MOVEQ   OP2mlo,OP2mlo,LSL #1
        ADDEQ   tmp,tmp,#1

; tmp now contains the amount to shift by.

        MOV     OP2mhi,OP2mlo
        MOV     OP2mlo,#0

        SUB     OP2sue,OP2sue,#31
        SUB     OP2sue,OP2sue,tmp

        LDMFD   r13!,{OP1sue,pc}

        ]

;---------------------------------------------------------------------------

        END
