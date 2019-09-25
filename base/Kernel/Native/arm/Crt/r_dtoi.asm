;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

;  __dtoi double precision floating point to signed integer convert
;
;  Input: r1 - Most significant word of the double to be converted
;         r0 - Least significant word of the double to be converted
;
;  Output: r1 - Converted double in signed integer format
;

; Local storage size and offsets
LOC_SIZE     EQU    0x18
OrgOp1h      EQU    0x14
OrgOp1l      EQU    0x10
ExDResl      EQU    0x08
NewResl      EQU    0x10


        GET fpe.asm
        GET kxarm.inc

        AREA |.text|, CODE, READONLY

        Export  __dtoi
        IMPORT  FPE_Raise

    NESTED_ENTRY __dtoi
        EnterWithLR_16
        STMFD   sp!, {lr}               ; Save return address
        SUB     sp, sp, #LOC_SIZE       ; Allocate stack space
    PROLOG_END
        STR     r1, [sp, #OrgOp1h]      ; Save off original args in case of exception
        ORRS    r12, r0, r1, LSL #1     ; Check for zero
        STR     r0, [sp, #OrgOp1l]      ; Save off original args in case of exception
        ADDEQ   sp, sp, #LOC_SIZE       ; Restore stack and return
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}               ;   if zero (r0 already zero)
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}               ;   if zero (r0 already zero)
  ENDIF

        MOVS    r2, r1, LSL #1          ; Right justify exponent, save sign bit in C
        MOV     r1, r1, LSL #11         ; Left justify mantissa
        ORR     r1, r1, r0, LSR #21     ;   ..
                                        ;   ..
        MOV     r0, r0, LSL #11         ;   ..
        ORR     r1, r1, #1 << 31        ; Insert hidden one (even for denorms)

        BCS     _ffix_negative          ; If negative input, separate case

        MOV     r3, #DExp_bias+1        ; r3 = 31 + DExp_bias
        ADD     r3, r3, #30             ;   ..
        SUBS    r2, r3, r2, LSR #21     ; Determine shift amount
        BLE     shift_left              ; Negative shift is a shift left, NaN,
                                        ;   or INF; zero shift is an overflow
        CMP     r2, #32                 ; See if shifting all bits out
        BGE     shift_right_32          ; If shifting all bits out, return zero

shift_right
        RSB     r3, r2, #32             ; Check for inexact
        ORRS    r12, r0, r1, LSL r3     ;   ..
        MOV     r0, r1, LSR r2          ; Shift the result
        MOVNE   r3, #INX_bit            ; Set inexact if inexact
        MOVEQ   r3, #0                  ; Otherwise set to no exceptions
        B       __dtoi_return           ; Return

shift_left
        RSB     r2, r2, #0              ; Get left shift amount
        CMP     r2, #32                 ; If >= 32, shift by moving words, and
        MOVGE   r1, r0                  ;   adjusting shift amount
        MOVGE   r0, #0                  ;   ..
        SUBGE   r2, r2, #32             ;   ..
        MOV     r1, r1, LSL r2          ; Perform rest of shift
        RSB     r2, r2, #32             ;   ..
        ORR     r0, r1, r0, LSR r2      ;   ..
        MOV     r3, #IVO_bit            ; Overflow so set invalid operation
        B       __dtoi_return           ; Return

shift_right_32                          ; 0.0 < abs(Arg) < 1.0, so losing all bits
        BIC     r3, r3, #IVO_bit        ; Ensure invalid is clear
        MOV     r3, #INX_bit            ; Set inexact
        MOV     r0, #0                  ; Return zero
        B       __dtoi_return           ; Return

_ffix_negative
        MOV     r3, #DExp_bias+1        ; r3 = 31 + DExp_bias
        ADD     r3, r3, #30             ;   ..
        SUBS    r2, r3, r2, LSR #21     ; Determine shift amount
        BLT     shift_left_neg          ; Negative shift is a shift left, NaN,
                                        ;   or INF; zero shift is an overflow
        BEQ     special_int_min         ; Special case of INT_MIN
        CMP     r2, #32                 ; See if shifting all bits out
        BGE     shift_right_32          ; If shifting all bits out, return zero

shift_right_neg
        RSB     r3, r2, #32             ; Check for inexact
        ORRS    r12, r0, r1, LSL r3     ;   ..
        MOV     r0, r1, LSR r2          ; Shift the result
        RSB     r0, r0, #0              ; Negate result
        MOVNE   r3, #INX_bit            ; Set inexact if inexact
        MOVEQ   r3, #0                  ; Otherwise set to no exceptions
        B       __dtoi_return           ; Return

shift_left_neg
        RSB     r2, r2, #0              ; Get left shift amount
        CMP     r2, #32                 ; If >= 32, shift by moving words, and
        MOVGE   r1, r0                  ;   adjusting shift amount
        MOVGE   r0, #0                  ;   ..
        SUBGE   r2, r2, #32             ;   ..
        MOV     r1, r1, LSL r2          ; Perform rest of shift
        RSB     r2, r2, #32             ;   ..
        ORR     r0, r1, r0, LSR r2      ;   ..
        RSB     r0, r0, #0              ; Negate result
        MOV     r3, #IVO_bit            ; Have a negative so invalid
        B       __dtoi_return           ; Return

special_int_min
        TEQ     r1, #0x80000000         ; Result == INT_MIN
        MOVNE   r3, #IVO_bit            ; If not, overflow so raise invalid,
        RSBNE   r0, r1, #0              ;   negate and move result into place,
        BNE     __dtoi_return           ;   and return
        CMP     r0, #0                  ; If is, okay, check for inexact
        MOVNE   r3, #INX_bit            ; If bits lost in low word, inexact
        MOVEQ   r3, #0                  ; Otherwise, no exceptions
        MOV     r0, r1                  ; Move result into place
        


__dtoi_return
        TST     r3, #FPECause_mask      ; Any exceptions?
        ADDEQ   sp, sp, #LOC_SIZE       ; If not, pop off saved arg and
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}               ;   return
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}               ;   return
  ENDIF
        ORR     r1, r3, #_FpDToI        ; Exception information
        LDR     r3, [sp, #OrgOp1h]      ; Original operand 1
        LDR     r2, [sp, #OrgOp1l]      ;   ..
        STR     r0, [sp, #ExDResl]      ; Store default result
        ADD     r0, sp, #NewResl        ; Pointer to new result

	CALL    FPE_Raise               ; Handle exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
        LDR     r0, [sp, #NewResl]      ; Load new result
        ADD     sp, sp, #LOC_SIZE       ; Pop off exception record and result
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}               ; Return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}               ; Return
  ENDIF

    ENTRY_END __dtoi

    END
