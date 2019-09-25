;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; veneer_d.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

;===========================================================================
;Veneers onto the arith.asm functions.
;
;This block should be assembled multiple times, once for each function.
;The possible functions are:
;
;       addsub_s        double precision add and subtract
;       mul_s           double precision multiply
;       div_s           double precision divide
;       fmod_s          implementation of math.h's fmod() [REM]
;       sqrt_s          implementation of math.h's sqrt() [SQRT]

        GET     fpe.asm
        GET     kxarm.inc
	
;===========================================================================

; When veneering these functions we need to be able to convert from double
; to extended on entry and back again on exit. This macro provides the
; conversion function.

; *WARNING* If no ulabel is set then the next instruction is skipped in
; the case of a number that needs normalizing. This is INTENTIONAL, since
; this macro leaves the Z flag set in the case of an uncommon case, but
; might also leave it set in the case of a denorm, so the following,
; conditional, instruction is skipped. It might be better if ulabel weren't
; there at all, just to make it explicit.
; The __fp_norm_opx functions should also do the skipping, rather than
; hacking lr in the fast path. This should be fixed, but for the moment
; I'd rather not be so disgustingly vile.

        MACRO
$label  DoubleToInternal $op,$zlabel,$ulabel
        ASSERT  ($op = 1) :LOR: ($op = 2)
$label  MOVS    tmp,dOP$op.h,LSL #1        ;C:=sign; Z:=exp & frac.top zero
        TEQEQ   dOP$op.l,#0                     ;C unchanged; Z:=value is a zero
        [ "$zlabel" <> ""
          BEQ   $zlabel                         ;Possible early abort
        ]
        MOV     Rtmp,tmp,LSL #DExp_len-1   ;Frac.top in bits 30:11 of mhi
        MOV     dOP$op.h,tmp,LSR #DExp_pos ;Exponent in bits 11:1
        MOV     OP$op.mlo,dOP$op.l,LSL #DExp_len; OP2mhi and 31:11 of OP2mlo
        ORR     OP$op.mhi,Rtmp,dOP$op.l,LSR #DFhi_len+1
                                                ;Fraction in bits 30:0 of
        ADDNE   dOP$op.h,dOP$op.h,#(EIExp_bias - DExp_bias):SHL:1
        MOV     OP$op.sue,dOP$op.h,RRX          ;Recombine sign and exponent
        ORRNE   OP$op.mhi,OP$op.mhi,#EIUnits_bit

        ; Gets here with the *double precision* exponent in the top 11 bits
        ; of tmp. (Exponent<<1+DExp_pos.) We use a sign extended shift to
        ; spot the "maximum exponent case" - leaves us with -1 in tmp.
        MOVS    tmp,tmp,ASR #1+DExp_pos
        ADDEQ   lr,pc,#8        ;Skip two instructions past normalise call
        BEQ     __fp_norm_op$op
        CMP     tmp,#&ffffffff
        [ "$ulabel" <> ""
        BEQ     $ulabel
        ]
        MEND

        MACRO
        InternalToDouble
        BL      __fp_e2d
        TST     a4,#Error_bit
        VReturn EQ
        ORR     a4,a4,#Double_bit
        B       __fp_veneer_error
        MEND

        MACRO
        Double $name
        IMPORT  __fp_e2d
        IMPORT  __fp_norm_op1
        IMPORT  __fp_norm_op2
        MEND

;===========================================================================
; Veneer functions

        [ :DEF: add_s

; Local stack size and offset defines
LOC_SIZE    EQU 0x24            ; Size of local storage on stack
ORG_OP2h    EQU 0x20            ; Original Operand 2 high half
ORG_OP2l    EQU 0x1C            ; Original Operand 2 high low
ORG_OP1h    EQU 0x18            ; Original Operand 1 high half
ORG_OP1l    EQU 0x14            ; Original Operand 1 high low
OPCODE      EQU 0x10            ; Opcode (_FpAddD or _FpSubD)
ExDRESh     EQU 0x0C            ; Exception record default result high
ExDRESl     EQU 0x08            ; Exception record default result low
ExOp2h      EQU 0x04            ; Exception record operand 2 high half
ExOp2l      EQU 0x00            ; Exception record operand 2 low half
ExNewResh   EQU 0x14            ; Exception new result high
ExNewResl   EQU 0x10            ; Exception new result low
        

	AREA   |.text|, CODE, READONLY
        Double add

; This is the veneer onto __addd, _drsb and __subd.

        Export  __addd
        IMPORT  __fp_addsub_common
        IMPORT  __fp_addsub_uncommon
        IMPORT  FPE_Raise

        [ :LNOT: :DEF: thumb

        Export  __subd


; __subd and __addd prologues must be the same.
    NESTED_ENTRY __subd
        ;VEnter_16                         ; Includes extra ARM entry point
        STMFD   sp!, veneer_s              ; Save off non-volatiles
        SUB     sp, sp, #LOC_SIZE          ; Local storage
    PROLOG_END
        MOV     r5, #_FpSubD               ; Double precision subtract
        STR     r3, [sp, #ORG_OP2h]        ; Save off original args in case of exception
        STR     r2, [sp, #ORG_OP2l]
        STR     r1, [sp, #ORG_OP1h]
        STR     r0, [sp, #ORG_OP1l]

;For sub we just invert the sign of operand 2 and branch to add.

        EOR     dOP2h, dOP2h, #Sign_bit
        B       coreadd
    ENTRY_END __subd
        ]

; __addd and __subd prologues must be the same.
    NESTED_ENTRY __addd
        ;VEnter_16                         ; Includes extra ARM entry point
        STMFD   sp!, veneer_s              ; Save off non-volatiles
        SUB     sp, sp, #LOC_SIZE          ; Local storage
    PROLOG_END

        MOV     r5, #_FpAddD               ; Double precision addition
        STR     r3, [sp, #ORG_OP2h]        ; Save off original args in case of exception
        STR     r2, [sp, #ORG_OP2l]
        STR     r1, [sp, #ORG_OP1h]
        STR     r0, [sp, #ORG_OP1l]

coreadd
        STR     r5, [sp, #OPCODE]          ; Save off operation code in case of exception

        ; Catch the NaNs and INFs here.
        MOV      r4, r1, LSL #1
        MOV      r4, r4, LSR #21
        ADD      r4, r4, #1
        CMP      r4, #2048
        BEQ      dadd_arg1_nan_inf   ; Arg1 is a NaN/INF

                                     ; Arg1 is finite
        MOV      r4, r3, LSL #1
        MOV      r4, r4, LSR #21
        ADD      r4, r4, #1
        CMP      r4, #2048
        BEQ      dadd_arg2_nan_inf   ; Arg2 is a NaN/INF

        DoubleToInternal 2,,dadd_uncommon1
        DoubleToInternal 1,,dadd_uncommon

        BL      __fp_addsub_common

dadd_return
        BL      __fp_e2d

dadd_check_cause
        TST     r3, #FPECause_mask
        ADDEQ   sp, sp, #LOC_SIZE

        ; VReturn EQ
          LDMEQFD sp!,veneer_s
  IF Interworking :LOR: Thumbing
          BXEQ    lr
  ELSE
          MOVEQ   pc, lr
  ENDIF
        
        LDR     r12, [sp, #OPCODE]    ; Get saved operation code
        STR     r0, [sp, #ExDRESl]
        STR     r1, [sp, #ExDRESh]
        LDR     r0, [sp, #ORG_OP2l]
        LDR     r1, [sp, #ORG_OP2h]
        STR     r0, [sp, #ExOp2l]
        STR     r1, [sp, #ExOp2h]
        LDR     r2, [sp, #ORG_OP1l]
        ORR     r1, r3, r12
        LDR     r3, [sp, #ORG_OP1h]
        ADD     r0, sp, #ExNewResl

	CALL    FPE_Raise
	
    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
		
        LDR     r0, [sp, #ExNewResl]
        LDR     r1, [sp, #ExNewResh]
        ADD     sp, sp, #LOC_SIZE
        LDMFD   sp!, veneer_s
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF



dadd_uncommon1
        ORR     OP2sue,OP2sue,#Uncommon_bit
        DoubleToInternal 1      ; Skips next instruction if denorm
dadd_uncommon
        ORREQ   OP1sue,OP1sue,#Uncommon_bit
        ADR     lr,dadd_return
        MOV     Rins,#Double_mask
        B       __fp_addsub_uncommon




; Arg1 is an INF or a NaN.
; If Arg1 is an SNaN, signal invalid and return a QNaN.
; Else if Arg1 is a QNaN, check Arg2 for an SNaN.
;   If Arg2 is an SNaN, signal invalid.
;   Return the Arg1 QNaN.
; Else it is an INF
;   If Arg2 is an SNaN, signal invalid and return a QNaN version of Arg2.
;   Else if Arg2 is a QNaN, return it.
;   Else if Arg2 is an INF of the same sign, return it.
;   Else if Arg2 is an INF of the opposite sign, set invalid and return a QNaN.
;   Else return the INF.
dadd_arg1_nan_inf
        ORRS    r4, r0, r1, LSL #12 ; Mantissa1 == 0?
        BEQ     dadd_arg1_inf       ; Mantissa1 == 0 so is an INF
        TST     r1, #dSignalBit     ; Arg1 == SNaN?
        ORREQ   r5, r5, #IVO_bit    ; If Arg1 == SNaN, signal invalid
        BEQ     dadd_return_qnan    ;   and return a QNaN version of it
        MOV     r4, r3, LSL #1      ; Extract exponent2
        MOV     r4, r4, LSR #21     ;  ..
        ADD     r4, r4, #1          ; Exponent2 == 2047?
        CMP     r4, #2048           ;  ..
        BNE     dadd_return_qnan    ; If !=, cannot be an SNaN
        ORRS    r4, r2, r3, LSL #12 ; Mantissa2 == 0?
        BEQ     dadd_return_qnan    ; If == 0, cannot be an SNaN
        TST     r3, #dSignalBit     ; Arg2 is a NaN.  Is it an SNaN?
        ORREQ   r5, r5, #IVO_bit    ; If SNaN, set invalid
        B       dadd_return_qnan    ; Return Arg1 QNaN


dadd_arg1_inf
        MOVS    r4, r3, LSL #1      ; Extract exponent2
        MOV     r4, r4, LSR #21     ;  ..
        ADD     r4, r4, #1          ; Exponent2 == 2047?
        CMP     r4, #2048           ;  ..
        MOVNE   r3, r5              ; Copy exception information
        BNE     dadd_check_cause    ;   and return the INF
        ORRS    r4, r2, r3, LSL #12 ; Mantissa2 == 0?
        BEQ     dadd_check_inf      ; If == 0, have an INF
        MOV     r1, r3              ; Arg2 is a NaN, so we need to copy the
        MOV     r0, r2              ;   mantissa bits to return in the QNaN.
        TST     r3, #dSignalBit     ; Is Arg2 an SNaN?
        ORREQ   r5, r5, #IVO_bit    ; If SNaN, set invalid
        B       dadd_return_qnan    ; Return Arg2 QNaN
        
dadd_check_inf
        EORS    r4, r1, r3          ; Check signs
        MOVPL   r3, r5              ; Copy exception information
        BPL     dadd_check_cause    ; Return the INF
        ORR     r5, r5, #IVO_bit
        B       dadd_return_qnan    ; Return a QNaN
        

        
; Arg2 is a NaN or an INF.  Arg1 is a finite non-zero number.
; If Arg2 is an INF, return it.
; Else if Arg2 is a QNaN, return it.
; Else if Arg2 is an SNaN, signal invalid and return a QNaN version of it.
dadd_arg2_nan_inf
        MOV     r1, r3              ; Arg2 is a NaN or INF.  We need to copy
        MOV     r0, r2              ;   the bits to the Arg1 registers.
        ORRS    r4, r2, r3, LSL #12 ; Mantissa2 == 0?
        BEQ     dadd_check_cause    ;   ..
        TST     r3, #dSignalBit     ; Is Arg2 an SNaN?
        ORREQ   r5, r5, #IVO_bit    ; If SNaN, set invalid
                                    ; Fall through to return QNaN


; Returns a QNaN.  R1 and R0 must contain the mantissa portion
; of the QNaN.  SNaNs are converted to QNaNs here.
dadd_return_qnan
        ORR     r1, r1, #0x7F000000 ; Set exponent = 0x7FF
        ORR     r1, r1, #0x00F80000 ;  ... and set mantissa[MSb] = 1
        MOV     r3, r5              ; Move exception information
        B       dadd_check_cause

    ENTRY_END __addd

        ]

;---------------------------------------------------------------------------

        [ {FALSE} :LAND: :DEF: sub_s :LAND: :DEF: thumb

	AREA   |.text|, CODE, READONLY
        Double  sub

        Export  __subd

        IMPORT  __addd

__subd   VEnter_16

        EOR     dOP2h, dOP2h, #Sign_bit
        ; Just do a tail call to addd. In the THUMB world, code density is
        ; king. (The addition skips the LDM on the __addd entry point, and
        ; is dangerous.)
        B       __addd+4

        [ {FALSE}
        DoubleToInternal 2,,dsub_uncommon1
        DoubleToInternal 1,,dsub_uncommon

        BL      __fp_addsub_common

dsub_return
        InternalToDouble

dsub_uncommon1
        ORR     OP2sue,OP2sue,#Uncommon_bit
        DoubleToInternal 1      ; Skips next instruction if denorm
dsub_uncommon
        ORREQ   OP1sue,OP1sue,#Uncommon_bit
        ADR     lr,dsub_return
        MOV     Rins,#Double_mask
        B       __fp_addsub_uncommon

        ]

        ]

;---------------------------------------------------------------------------

        [ :DEF: rsb_s :LAND: :DEF: thumb

        CodeArea |FPL$$drsb|
        Double  rsb

        Export  _drsb
        IMPORT  __addd

_drsb   VEnter_16

        EOR     dOP1h, dOP1h, #Sign_bit
        ; Same as above - branch to add code.
        B       __addd+4

        [ {FALSE}

        DoubleToInternal 2,,drsb_uncommon1
        DoubleToInternal 1,,drsb_uncommon

        BL      __fp_addsub_common

drsb_return
        InternalToDouble

drsb_uncommon1
        ORR     OP2sue,OP2sue,#Uncommon_bit
        DoubleToInternal 1      ; Skips next instruction if denorm
drsb_uncommon
        ORREQ   OP1sue,OP1sue,#Uncommon_bit
        ADR     lr,drsb_return
        MOV     Rins,#Double_mask
        B       __fp_addsub_uncommon

        ]

        ]

;---------------------------------------------------------------------------

        [ :DEF: mul_s

; Local stack size and offset defines
LOC_SIZE    EQU 0x20            ; Size of local storage on stack
OrgOP2h     EQU 0x1C            ; Original Operand 2 high half
OrgOP2l     EQU 0x18            ; Original Operand 2 high low
OrgOP1h     EQU 0x14            ; Original Operand 1 high half
OrgOP1l     EQU 0x10            ; Original Operand 1 high low
ExDRESh     EQU 0x0C            ; Exception record default result high
ExDRESl     EQU 0x08            ; Exception record default result low
ExOp2h      EQU 0x04            ; Exception record operand 2 high half
ExOp2l      EQU 0x00            ; Exception record operand 2 low half
ExNewResh   EQU 0x14            ; Exception new result high
ExNewResl   EQU 0x10            ; Exception new result low

	AREA   |.text|, CODE, READONLY
        Double  mul

        Export  __muld
        IMPORT  __fp_mult_common
        IMPORT  __fp_mult_uncommon
        IMPORT  FPE_Raise

    NESTED_ENTRY __muld
        ; VEnter_16
        STMFD   sp!, veneer_s              ; Save off non-volatiles
        SUB     sp, sp, #LOC_SIZE          ; Local storage
    PROLOG_END

        STR      r3, [sp, #OrgOP2h]        ; Save off original args in case of exception
        STR      r2, [sp, #OrgOP2l]
        STR      r1, [sp, #OrgOP1h]
        STR      r0, [sp, #OrgOP1l]

        ; Catch the NaNs, INFs, and Zeros here.
        MOV      r5, #0              ; Exception information initialized to none.
        ORRS     r4, r0, r1, LSL #1
        BEQ      dmul_arg1_zero      ; Arg1 is zero
        MOV      r4, r1, LSL #1
        MOV      r4, r4, LSR #21
        ADD      r4, r4, #1
        CMP      r4, #2048
        BEQ      dmul_arg1_nan_inf   ; Arg1 is a NaN/INF

                                     ; Arg1 is non-zero and finite
        ORRS     r4, r2, r3, LSL #1
        BEQ      dmul_return_zero    ; Arg2 is zero so just return a zero
        MOV      r4, r3, LSL #1
        MOV      r4, r4, LSR #21
        ADD      r4, r4, #1
        CMP      r4, #2048
        BEQ      dmul_arg2_nan_inf   ; Arg2 is a NaN/INF


        DoubleToInternal 2,,dmul_uncommon1
        DoubleToInternal 1,,dmul_uncommon
        
        BL      __fp_mult_common

dmul_return
        BL      __fp_e2d

dmul_check_cause
        TST     r3, #FPECause_mask
        ADDEQ   sp, sp, #LOC_SIZE

        ; VReturn EQ
          LDMEQFD r13!,veneer_s
  IF Interworking :LOR: Thumbing
          BXEQ    lr
  ELSE
          MOVEQ   pc, lr
  ENDIF
        
        STR     r0, [sp, #ExDRESl]
        STR     r1, [sp, #ExDRESh]
        LDR     r0, [sp, #OrgOP2l]
        LDR     r1, [sp, #OrgOP2h]
        STR     r0, [sp, #ExOp2l]
        STR     r1, [sp, #ExOp2h]
        LDR     r2, [sp, #OrgOP1l]
        ORR     r1, r3, #_FpMulD
        LDR     r3, [sp, #OrgOP1h]
        ADD     r0, sp, #ExNewResl

	CALL    FPE_Raise
	
    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF

        LDR     r0, [sp, #ExNewResl]
        LDR     r1, [sp, #ExNewResh]
        ADD     sp, sp, #LOC_SIZE
        LDMFD   sp!, veneer_s
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

dmul_uncommon1
        ORR     OP2sue,OP2sue,#Uncommon_bit
        DoubleToInternal 1      ; Skips next instruction if denorm
dmul_uncommon
        ORREQ   OP1sue,OP1sue,#Uncommon_bit
        ADR     lr,dmul_return
        MOV     Rins,#Double_mask
        B       __fp_mult_uncommon


; Arg1 is a zero.  If Arg2 isn't a NaN or an INF, we return a zero.
; If Arg2 is an INF, we have an invalid operation and return a QNaN.
; If Arg2 is a QNaN, we return the QNaN.
; If Arg2 is an SNaN, we return a QNaN and signal invalid operation.
dmul_arg1_zero
        MOV     r4, r3, LSL #1       ; Extract exponent2
        MOV     r4, r4, LSR #21      ;  ..
        ADD     r4, r4, #1           ; Exponent2 == 2047?
        CMP     r4, #2048            ;  ..
        BNE     dmul_return_zero     ; If != 2047, return 0
        ORRS    r4, r2, r3, LSL #12  ; Else if mantissa2==0
        ORREQ   r5, r5, #IVO_bit     ; If ==, invalid op
        BEQ     dmul_return_qnan     ;   return QNaN
        MOV     r1, r3               ; Else have a NaN so copy mantissas to
        MOV     r0, r2               ;   return QNaN and ...
        TST     r1, #dSignalBit      ;   check for an SNaN
        ORREQ   r5, r5, #IVO_bit     ; If clear, have SNaN so invalid operation
        B       dmul_return_qnan


; Arg1 is an INF or a NaN.
; If it is an SNaN, signal invalid and return a QNaN.
; else if it is a QNaN, check Arg2 for an SNaN.
;   If Arg2 is an SNaN, signal invalid.
;   Return the Arg1 QNaN.
; Else it is an INF
;   If Arg2 is an SNaN, signal invalid and return a QNaN version of Arg2.
;   Else if Arg2 is a QNaN, return it.
;   Else if Arg2 is an INF, return an INF.
;   Else if Arg2 is a zero, signal invalid and return a QNaN.
dmul_arg1_nan_inf
        ORRS    r4, r0, r1, LSL #12 ; Mantissa1 == 0?
        BEQ     dmul_arg1_inf       ; Mantissa1 == 0 so is an INF
        TST     r1, #dSignalBit     ; Arg1 == SNaN?
        ORREQ   r5, r5, #IVO_bit    ; If Arg1 == SNaN, signal invalid
        BEQ     dmul_return_qnan    ;   and return a QNaN version of it
        MOV     r4, r3, LSL #1      ; Extract exponent2
        MOV     r4, r4, LSR #21     ;  ..
        ADD     r4, r4, #1          ; Exponent2 == 2047?
        CMP     r4, #2048           ;  ..
        BNE     dmul_return_qnan    ; If !=, cannot be an SNaN
        ORRS    r4, r2, r3, LSL #12 ; Mantissa2 == 0?
        BEQ     dmul_return_qnan    ; If == 0, cannot be an SNaN
        TST     r3, #dSignalBit     ; Arg2 is a NaN.  Is it an SNaN?
        ORREQ   r5, r5, #IVO_bit    ; If SNaN, set invalid
        B       dmul_return_qnan    ; Return Arg1 QNaN


dmul_arg1_inf
        ORRS    r4, r2, r3, LSL #1  ; Arg2 == 0?
        ORREQ   r5, r5, #IVO_bit    ; If == 0, signal invalid, return
        BEQ     dmul_return_qnan    ;   return a QNaN
        MOVS    r4, r3, LSL #1      ; Extract exponent2
        MOV     r4, r4, LSR #21     ;  ..
        ADD     r4, r4, #1          ; Exponent2 == 2047?
        CMP     r4, #2048           ;  ..
        BNE     dmul_return_inf     ; If !=, cannot be a NaN or INF
        ORRS    r4, r2, r3, LSL #12 ; Mantissa2 == 0?
        BEQ     dmul_return_inf     ; If == 0, cannot be a NaN
        MOV     r1, r3              ; Arg2 is a NaN, so we need to copy the
        MOV     r0, r2              ;   mantissa bits to return in the QNaN.
        TST     r3, #dSignalBit     ; Is Arg2 an SNaN?
        ORREQ   r5, r5, #IVO_bit    ; If SNaN, set invalid
        B       dmul_return_qnan    ; Return Arg2 QNaN
        
        
; Arg2 is a NaN or an INF.  Arg1 is a finite non-zero number.
; If Arg2 is an INF, return it.
; Else if Arg2 is a QNaN, return it.
; Else if Arg2 is an SNaN, signal invalid and return a QNaN version of it.
dmul_arg2_nan_inf
        ORRS    r4, r2, r3, LSL #12 ; Mantissa2 == 0?
        BEQ     dmul_return_inf     ; If == 0, Arg2 is an INF, so return it.
        MOV     r1, r3              ; Arg2 is a NaN, so we need to copy the
        MOV     r0, r2              ;   mantissa bits to return in the QNaN.
        TST     r3, #dSignalBit     ; Is Arg2 an SNaN?
        ORREQ   r5, r5, #IVO_bit    ; If SNaN, set invalid
        B       dmul_return_qnan    ; Return Arg2 QNaN
        


; Returns a QNaN.  R1 and R0 must contain the mantissa portion
; of the QNaN.  SNaNs are converted to QNaNs here.
dmul_return_qnan
        ORR     r1, r1, #0x7F000000 ; Set exponent = 0x7FF
        ORR     r1, r1, #0x00F80000 ;  ... and set mantissa[MSb] = 1
        MOV     r3, r5              ; Move exception information
        B       dmul_check_cause


; Returns a properly signed INF.  r1 and r3 must contain the
; sign bits in the MSb.
dmul_return_inf
        EORS    r4, r1, r3          ; Check signs of Arg1 and Arg2
        MOV     r0, #0              ; Clear mantissa2 ...
        MOV     r1, #0x7F000000     ;   ... and set exponent = 0x7FF
        ORR     r1, r1, #0x00F00000 ;   ..
        ORRMI   r1, r1, #0x80000000 ; Set sign bit if negative
        MOV     r3, r5              ; Move exception information
        B       dmul_check_cause

; Returns a properly signed zero.  r1 and r3 must contain the
; sign bits in the MSb.
dmul_return_zero
        EORS    r4, r1, r3          ; Check signs of Arg1 and Arg2
        MOV     r0, #0              ; Clear sign, exponent, and mantissa
        MOV     r1, #0              ;   ..
        ORRMI   r1, r1, #0x80000000 ; Set sign bit if negative
        MOV     r3, r5              ; Move exception information
        B       dmul_check_cause


    ENTRY_END __muld
        ]

;---------------------------------------------------------------------------

        [ :DEF: div_s

; Local stack size and offset defines
LOC_SIZE    EQU 0x20            ; Size of local storage on stack
OrgOP2h     EQU 0x1C            ; Original Operand 2 high half
OrgOP2l     EQU 0x18            ; Original Operand 2 high low
OrgOP1h     EQU 0x14            ; Original Operand 1 high half
OrgOP1l     EQU 0x10            ; Original Operand 1 high low
ExDRESh     EQU 0x0C            ; Exception record default result high
ExDRESl     EQU 0x08            ; Exception record default result low
ExOp2h      EQU 0x04            ; Exception record operand 2 high half
ExOp2l      EQU 0x00            ; Exception record operand 2 low half
ExNewResh   EQU 0x14            ; Exception new result high
ExNewResl   EQU 0x10            ; Exception new result low

	AREA   |.text|, CODE, READONLY
        Double  div

        Export  __divd
        IMPORT  FPE_Raise
        IMPORT  __fp_div_common
        IMPORT  __fp_div_uncommon
 
        IMPORT  __fp_veneer_error     ; RDCFix: Get rid of this.

    NESTED_ENTRY __divd
        ; VEnter_16
        STMFD   r13!, veneer_s             ; Save off non-volatiles
        SUB     sp, sp, #LOC_SIZE          ; Local storage
    PROLOG_END

        STR      r3, [sp, #OrgOP2h]        ; Save off original args in case of exception
        STR      r2, [sp, #OrgOP2l]
        STR      r1, [sp, #OrgOP1h]
        STR      r0, [sp, #OrgOP1l]


        ; Catch the NaNs, INFs, and Zeros here.
        MOV      r5, #0              ; Exception information initialized to none.
        ORRS     r4, r0, r1, LSL #1
        BEQ      ddiv_arg1_zero      ; Arg1 is zero
        MOV      r4, r1, LSL #1
        MOV      r4, r4, LSR #21
        ADD      r4, r4, #1
        CMP      r4, #2048
        BEQ      ddiv_arg1_nan_inf   ; Arg1 is a NaN/INF

                                     ; Arg1 is non-zero and finite
        ORRS     r4, r2, r3, LSL #1
        BEQ      ddiv_zero_divide    ; Arg2 is zero so have zero divide
        MOV      r4, r3, LSL #1
        MOV      r4, r4, LSR #21
        ADD      r4, r4, #1
        CMP      r4, #2048
        BEQ      ddiv_arg2_nan_inf   ; Arg2 is a NaN/INF

        DoubleToInternal 2,ddiv_zero2,ddiv_uncommon1
        DoubleToInternal 1,ddiv_zero1,ddiv_uncommon

        MOV     Rins,#Double_mask
        BL      __fp_div_common

ddiv_return
        BL      __fp_e2d

ddiv_check_cause
        TST     r3, #FPECause_mask
        ADDEQ   sp, sp, #LOC_SIZE

        ; VReturn EQ
          LDMEQFD r13!,veneer_s
  IF Interworking :LOR: Thumbing
          BXEQ    lr
  ELSE
          MOVEQ   pc, lr
  ENDIF
        
        STR     r0, [sp, #ExDRESl]
        STR     r1, [sp, #ExDRESh]
        LDR     r0, [sp, #OrgOP2l]
        LDR     r1, [sp, #OrgOP2h]
        STR     r0, [sp, #ExOp2l]
        STR     r1, [sp, #ExOp2h]
        LDR     r2, [sp, #OrgOP1l]
        ORR     r1, r3, #_FpDivD
        LDR     r3, [sp, #OrgOP1h]
        ADD     r0, sp, #ExNewResl
	CALL    FPE_Raise
	
    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
        LDR     r0, [sp, #ExNewResl]
        LDR     r1, [sp, #ExNewResh]
        ADD     sp, sp, #LOC_SIZE
        LDMFD   r13!, veneer_s
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF


        
ddiv_uncommon1
        ORR     OP2sue,OP2sue,#Uncommon_bit
        DoubleToInternal 1,ddiv_zero3
ddiv_uncommon
        ORREQ   OP1sue,OP1sue,#Uncommon_bit
        ADR     lr,ddiv_return
        MOV     Rins,#Double_mask
        B       __fp_div_uncommon

ddiv_zero3
; Op1 is a zero, Op2 is an uncommon non-zero. Op2 is in the converted form.
; Op2 is an infinity if all bits are zero (result is a signed zero). Otherwise
; a quiet NaN/exception.

        ORRS    tmp,OP2mlo,OP2mhi,LSL #1
        BEQ     ddiv_zero1
        MOVS    OP2mhi,OP2mhi,LSL #1
        BPL     ddiv_ivo

; return any old quiet NaN

; RDCFix: Get rid of this stuff.
;ddiv_return_qnan
;        MOV     dOPh,#-1
;        VReturn

ddiv_zero2
; Op2 is a zero. If operand 1 is a zero or a SNaN, this is an invalid
; operation, otherwise it is a divide by zero.

        MOVS    tmp, dOP1h, LSL #1
        TEQEQ   dOP1l, #0                       ; Z <- zero
        BEQ     ddiv_ivo

        MVNS    tmp, tmp, ASR #32-DExp_len-1    ; Z <- QNaN
        VReturn EQ                              ; Return Op1 (QNaN)
        ; tmp==1 and mantissa==0 => Inf (Inf)
        ; tmp==1 and mantissa!=0 => SNaN (IVO)
        TEQ     tmp, #1
        BNE     ddiv_dvz
        ORRS    tmp, dOP1l, dOP1h, LSL #DExp_len+1 ; Z <- zero mantissa (Inf)
        ; MLS 2890
        ; Infinty/Zero returns appropriately signed infinity.
        ; Given the representations of Infinty and Zero, we can get
        ; this sign in a single instruction.
        EOREQ   dOP1h, dOP1h, dOP2h
        VReturn EQ                              ; Return Op1 (Inf)

ddiv_ivo
        MOV     a4, #IVO_bit:OR:Double_bit
        B       __fp_veneer_error

ddiv_dvz
        MOV     a4, #DVZ_bit:OR:Double_bit
        ; MLS report 2899
        ; division by -0.0 should return inversely signed infinity.
        EOR     dOP1h, dOP1h, dOP2h
        B       __fp_veneer_error

ddiv_zero1
; Op1 is a zero, Op2 is in the extended form, and can't be an "uncommon".

        EOR     dOP1h, dOP1h, OP2sue
        AND     dOP1h, dOP1h, #Sign_bit
        VReturn



; Arg1 is a zero.
; If Arg2 is a zero, set invalid operation and return a QNaN.
; Else if Arg2 is an SNaN, set invalid and return a QNaN version of the SNaN.
; Else if Arg2 is a QNaN, return it.
; Else return a zero.
ddiv_arg1_zero
        ORRS    r4, r2, r3, LSL #1    ; If Arg2 == 0
        ORREQ   r5, r5, #IVO_bit      ;   set invalid
        BEQ     ddiv_return_qnan      ;   return a QNaN
        MOV     r4, r3, LSL #1        ; Extract exponent2
        MOV     r4, r4, LSR #21       ;   ..
        ADD     r4, r4, #1            ; If exponent2 == 2047
        CMP     r4, #2048             ;   ..
        BNE     ddiv_return_zero      ; Arg2 finite, return a zero
        ORRS    r4, r2, r3, LSL #12   ; Mantissa2 == 0?
        BEQ     ddiv_return_zero      ; Have an INF, return a zero
        TST     r3, #dSignalBit       ; SNaN?
        ORREQ   r5, r5, #IVO_bit      ; If SNaN, set invalid
        MOV     r0, r2                ; Copy mantissa2 for QNaN return
        MOV     r1, r3                ;   ..
        B       ddiv_return_qnan      ; Return QNaN


; Arg1 is a NaN or an INF.
; If Arg1 is an INF
;   If Arg2 is an SNaN, set invalid operation and return a QNaN version of
;       the SNaN.
;   If Arg2 is a QNaN, return it.
;   If Arg2 is an INF, set invalid operation and return a QNaN.
;   Else return an INF.
; Else if Arg1 is an SNaN, set invalid operation and return a QNaN version
;     of the SNaN.
; Else if Arg1 is a QNaN.
;   If Arg2 is an SNaN, set invalid and return the QNaN.
;   Else return the QNaN.
ddiv_arg1_nan_inf
        ORRS    r4, r0, r1, LSL #12   ; Mantissa1 == 0?
        BEQ     ddiv_arg1_inf         ; If ==0, have an INF
        TST     r1, #dSignalBit       ; Check if Arg1 is an SNaN
        ORREQ   r5, r5, #IVO_bit      ; If is an SNaN, signal invalid
        BEQ     ddiv_return_qnan      ;   and return a QNaN version of it
        MOV     r4, r3, LSL #1        ; Extract exponent2
        MOV     r4, r4, LSR #21       ;   ..
        ADD     r4, r4, #1            ; If exponent2 == 2047
        CMP     r4, #2048             ;   ..
        BNE     ddiv_return_qnan      ; If !=, Arg2 finite, so return the QNaN
        ORRS    r4, r2, r3, LSL #12   ; Mantissa2 == 0?
        BEQ     ddiv_return_qnan      ; If ==, Arg2 is INF, so return the QNaN
        TST     r3, #dSignalBit       ; Check for SNaN
        ORREQ   r5, r5, #IVO_bit      ; If == 0, set invalid operation
        B       ddiv_return_qnan
        
ddiv_arg1_inf
        MOV     r4, r3, LSL #1        ; Extract exponent2
        MOV     r4, r4, LSR #21       ;   ..
        ADD     r4, r4, #1            ; If exponent2 == 2047
        CMP     r4, #2048             ;   ..
        BNE     ddiv_return_inf       ; If !=, Arg2 is finite, so return an INF
        ORRS    r4, r2, r3, LSL #12   ; Mantissa2 == 0?
        ORREQ   r5, r5, #IVO_bit      ; If ==, have an INF, so set invalid
        BEQ     ddiv_return_qnan      ;   and return a QNaN
        MOV     r0, r2                ; Copy mantissa2 for QNaN return
        MOV     r1, r3                ;   ..
        TST     r3, #dSignalBit       ; Is Arg2 an SNaN
        ORREQ   r5, r5, #IVO_bit      ; If it is, set invalid operation
        B       ddiv_return_qnan      ; Return QNaN
        


; Arg2 is a NaN or INF.  Arg1 is finite, possibly zero.
; If Arg2 is an INF, return zero.
; Else if Arg2 is an SNaN, set invalid operation and return a QNaN version of the SNaN.
; Else if Arg2 is a QNaN, return it.
ddiv_arg2_nan_inf
        ORRS    r4, r2, r3, LSL #12   ; If Arg2 == INF
        BEQ     ddiv_return_zero      ; Then return zero
        TST     r3, #dSignalBit       ; Have a NaN, check for SNaN
        ORREQ   r5, r5, #IVO_bit      ; If == 0, set invalid
        MOV     r1, r3                ; Copy mantissa2 for QNaN return
        MOV     r0, r2                ;   ..
        B       ddiv_return_qnan      ; Return QNaN
        



; Returns a QNaN.  R1 and R0 must contain the mantissa portion
; of the QNaN.  SNaNs are converted to QNaNs here.
ddiv_return_qnan
        ORR     r1, r1, #0x7F000000 ; Set exponent = 0x7FF
        ORR     r1, r1, #0x00F80000 ;  ... and set mantissa[MSb] = 1
        MOV     r3, r5              ; Move exception information
        B       ddiv_check_cause


; Sets the divide-by-zero exception and falls through to return an INF.
ddiv_zero_divide
        ORR     r5, r5, #DVZ_bit     ; Set zero divide


; Returns a properly signed INF.  r1 and r3 must contain the
; sign bits in the MSb.
ddiv_return_inf
        EORS    r4, r1, r3          ; Check signs of Arg1 and Arg2
        MOV     r0, #0              ; Clear mantissa2 ...
        MOV     r1, #0x7F000000     ;   ... and set exponent = 0x7FF
        ORR     r1, r1, #0x00F00000 ;   ..
        ORRMI   r1, r1, #0x80000000 ; Set sign bit if negative
        MOV     r3, r5              ; Move exception information
        B       ddiv_check_cause

; Returns a properly signed zero.  r1 and r3 must contain the
; sign bits in the MSb.
ddiv_return_zero
        EORS    r4, r1, r3          ; Check signs of Arg1 and Arg2
        MOV     r0, #0              ; Clear sign, exponent, and mantissa
        MOV     r1, #0              ;   ..
        ORRMI   r1, r1, #0x80000000 ; Set sign bit if negative
        MOV     r3, r5              ; Move exception information
        B       ddiv_check_cause


    ENTRY_END __divd

        ]

;---------------------------------------------------------------------------

        [ :DEF: rdv_s

        CodeArea |FPL$$drdv|
        Double  rdv

        IMPORT  __fp_rdv_common
        IMPORT  __fp_rdv_uncommon
        IMPORT  __fp_veneer_error
        ;Export  _drdv
        Export  _drdiv

;_drdv
_drdiv  VEnter_16

        DoubleToInternal 2,drdv_zero2,drdv_uncommon1
        DoubleToInternal 1,drdv_dvz,drdv_uncommon

        MOV     Rins,#Double_mask :OR: Reverse
        BL      __fp_rdv_common

drdv_return
        InternalToDouble
        
drdv_uncommon1
        ORR     OP2sue,OP2sue,#Uncommon_bit
        DoubleToInternal 1,drdv_zero1
drdv_uncommon
        ORREQ   OP1sue,OP1sue,#Uncommon_bit
        ADR     lr,drdv_return
        MOV     Rins,#Double_mask:OR:Reverse
        B       __fp_rdv_uncommon

drdv_zero1
; Op2 is uncommon, but Op1 is a zero. Return Inf for Op2=Inf, IVO for
; Op2=SNaN or a QNaN for Op2=QNaN

        MOVS    tmp, dOP2h, LSL #DExp_len+1     ; N <- QNaN
        TEQEQ   dOP1l, #0                       ; Z <- Inf
        MOVMIS  tmp, #0                         ; Z <- N
        BNE     drdv_ivo
        MOV     dOP1h, dOP2h                    ; Return a QNaN/Inf
        MOV     dOP1l, dOP2l
        VReturn

drdv_zero2
; Op2 is a zero. If Op1 is a zero or SNaN, this is an invalid operation,
; otherwise it is an appropiately signed zero unless Op1=QNaN

        MOVS    tmp, dOP1h, LSL #1
        TEQEQ   dOP1l, #0                       ; Z <- Op1=0
        BEQ     drdv_ivo
        MVNS    tmp, tmp, ASR #32-DExp_len-1    ; Z <- Op1=QNaN
        VReturn EQ                              ; Return QNaN
        ORRS    dOP1l, dOP1l, dOP1h, LSL #DExp_len+1
                                                ; Z <- zero mantissa
        BEQ     drdv_return_zero
        TEQ     tmp, #1                         ; Z <- SNaN
        BEQ     drdv_ivo

drdv_return_zero
        EOR     dOP1h, dOP1h, dOP2h
        AND     dOP1h, dOP1h, #Sign_bit
        MOV     dOP1l, #0
        VReturn

drdv_dvz
        MOV     a4,#DVZ_bit:OR:Double_bit
        B       __fp_veneer_error

drdv_ivo
        MOV     a4,#IVO_bit:OR:Double_bit
        B       __fp_veneer_error

        ]

;---------------------------------------------------------------------------

        [ :DEF: fmod_s

        CodeArea |FPL$$dfmod|
        Double  fmod

        EXPORT  fmod
        Import_32 __fp_edom

fmod    VEnter

        DoubleToInternal 2,fmod_divide_by_zero,fmod_uncommon1
        DoubleToInternal 1,fmod_Op1Zero,fmod_uncommon

        BL      Rem_Common

fmod_return
        InternalToDouble

fmod_Op1Zero

; Op1 is zero => result is Op1. Op1h/Op1l hasn't been changed.

        VReturn

fmod_uncommon1
        ORR     OP2sue,OP2sue,#Uncommon_bit
        DoubleToInternal 1
fmod_uncommon
        ORREQ   OP1sue,OP1sue,#Uncommon_bit
        ADR     lr,fmod_return
        MOV     Rins,#Double_mask
        B       Rem_Uncommon

fmod_divide_by_zero
        ; We return -HUGE_VAL and set errno=EDOM

        VPull
        MOV     a1, #Sign_bit
        MOV     a2, #1          ; true
        B_32    __fp_edom

        GET     arith.asm

        ]
        
;---------------------------------------------------------------------------

        [ :DEF: sqrt_s

        CodeArea |FPL$$dsqrt|
        Double  sqrt

        EXPORT  sqrt
        IMPORT  __fp_sqrt_common
        IMPORT  __fp_sqrt_uncommon

sqrt    VEnter

        DoubleToInternal 1,sqrt_Zero,sqrt_uncommon

        MOV     Rins,#Double_mask
        BL      __fp_sqrt_common

sqrt_return
        BL      __fp_e2d

        TST     a4, #Error_bit
        VReturn EQ

; error - set errno to EDOM and return -HUGE_VAL

        MOV     a1, #Sign_bit
        MOV     a2, #1          ; something non-zero
sqrt_edom
        Import_32 __fp_edom
; tail call
        VPull
        B_32    __fp_edom

sqrt_Zero
        ; C contains the sign bit - if set, record a domain error,
        ; but return -0.0 (which is what's in a1/a2 already)
      [ :DEF: SqrtMinusZeroGivesEDOM
        VReturn CC
        B       sqrt_edom       ; save a few bytes in error case
      |
        ; Otherwise, just return the zero passed in
        VReturn
      ]

sqrt_uncommon
        ORR     OP1sue,OP1sue,#Uncommon_bit
        ADR     lr,sqrt_return
        MOV     Rins,#Double_mask
        B       __fp_sqrt_uncommon

        ]

;===========================================================================

        END
