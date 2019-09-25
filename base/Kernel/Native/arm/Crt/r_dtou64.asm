;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

;  __dtou64 double precision floating point to unsigned 64-bit integer convert
;
;  Input: r1 - Most significant word of the double to be converted
;         r0 - Least significant word of the double to be converted
;
;  Output: r1 - Most significant word of the converted double in unsigned
;                 64-bit integer format
;          r0 - Least significant word of the converted double in unsigned
;                 64-bit integer format
;

; Local storage size and offsets
LOC_SIZE     EQU    0x18
OrgOp1h      EQU    0x14
OrgOp1l      EQU    0x10
ExDResh      EQU    0x0C
ExDResl      EQU    0x08
NewResh      EQU    0x14
NewResl      EQU    0x10


        GET fpe.asm
        GET kxarm.inc

        AREA |.text|, CODE, READONLY

        Export  __dtou64
        IMPORT  FPE_Raise

    NESTED_ENTRY __dtou64
        EnterWithLR_16
        STMFD   sp!, {lr}               ; Save return address
        SUB     sp, sp, #LOC_SIZE       ; Allocate local storage
    PROLOG_END

        STR     r1, [sp, #OrgOp1h]      ; Save off original args in case of exception
        ORRS    r12, r0, r1, LSL #1     ; Check for zero
        STR     r0, [sp, #OrgOp1l]      ;   ..
        MOVEQ   r1, r0                  ;   return if zero (r0 already zero)
        ADDEQ   sp, sp, #LOC_SIZE       ;   restore stack
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}               ;   ..
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}               ;   ..
  ENDIF

        MOVS    r2, r1, LSL #1          ; Right justify exponent, save sign bit in C
        MOV     r1, r1, LSL #11         ; Left justify mantissa
        ORR     r1, r1, r0, LSR #21     ;   ..
                                        ;   ..
        MOV     r0, r0, LSL #11         ;   ..
        ORR     r1, r1, #1 << 31        ; Insert hidden one (even for denorms)

        BCS     _ffix_negative          ; If negative input, separate case

        MOV     r3, #DExp_bias+1        ; r3 = 63 + DExp_bias
        ADD     r3, r3, #62             ;   ..
        SUBS    r2, r3, r2, LSR #21     ; Determine shift amount
        BLT     shift_left              ; Negative shift is a shift left, NaN,
                                        ;   or INF
        CMP     r2, #64                 ; See if shifting all bits out
        BGE     shift_right_64          ; If shifting all bits out, return zero

shift_right
        MOV     r12, #0                 ; Need to clear r12 for inexact check
        CMP     r2, #32                 ; See if shift amount >= 32
        BLT     shift_right_31          ;  If not, shift right 31 or less
        MOV     r12, r0                 ;  If >= 32, save lost bits in temp reg,
        MOV     r0, r1                  ;  shift by moving words, and
        MOV     r1, #0                  ;  adjust the shift amount
        SUB     r2, r2, #32             ;  ..

shift_right_31
        RSB     r3, r2, #32             ; Check for inexact
        ORRS    r12, r12, r0, LSL r3    ;   ..
        MOV     r0, r0, LSR r2          ; Shift the result
        ORR     r0, r0, r1, LSL r3      ;   ..
        MOV     r1, r1, LSR r2          ;   ..
        MOVNE   r3, #INX_bit            ; Set inexact if inexact
        MOVEQ   r3, #0                  ; Otherwise set to no exceptions
        B       __dtou64_return         ; Return

shift_left
        RSB     r2, r2, #0              ; Get left shift amount
        CMP     r2, #32                 ; If >= 32, shift by moving words, and
        MOVGE   r1, r0                  ;   adjusting shift amount
        MOVGE   r0, #0                  ;   ..
        SUBGE   r2, r2, #32             ;   ..
        MOV     r1, r1, LSL r2          ; Perform rest of shift
        RSB     r3, r2, #32             ;   ..
        ORR     r1, r1, r0, LSR r3      ;   ..
        MOV     r0, r0, LSL r2          ;   ..
        MOV     r3, #IVO_bit            ; Overflow so set invalid operation
        B       __dtou64_return         ; Return

shift_right_64                          ; 0.0 < abs(Arg) < 1.0, so losing all bits
        MOV     r3, #INX_bit            ; Set inexact
        MOV     r0, #0                  ; Return zero
        MOV     r1, #0                  ;   ..
        B       __dtou64_return         ; Return

_ffix_negative
        MOV     r3, #DExp_bias+1        ; r3 = 63 + DExp_bias
        ADD     r3, r3, #62             ;   ..
        SUBS    r2, r3, r2, LSR #21     ; Determine shift amount
        BLT     shift_left_neg          ; Negative shift is a shift left, NaN,
                                        ;   or INF
        CMP     r2, #64                 ; See if shifting all bits out
        BGE     shift_right_64          ; If shifting all bits out, return zero

shift_right_neg
        CMP     r2, #32                 ; See if shift amount >= 32
        MOVGE   r0, r1                  ;   If is shift by moving words, and
        MOVGE   r1, #0                  ;   adjust the shift amount
        SUBGE   r2, r2, #32             ;   ..

shift_right_31_neg
        RSB     r3, r2, #32             ; 32 - right shift amount
        MOV     r0, r0, LSR r2          ; Shift the result
        ORR     r0, r0, r1, LSL r3      ;   ..
        MOV     r1, r1, LSR r2          ;   ..
        RSBS    r0, r0, #0              ; Negate result
        RSC     r1, r1, #0              ;   ..
        MOV     r3, #IVO_bit            ; Set invalid operation as negative
        B       __dtou64_return         ; Return

shift_left_neg
        RSB     r2, r2, #0              ; Get left shift amount
        CMP     r2, #32                 ; If >= 32, shift by moving words, and
        MOVGE   r1, r0                  ;   adjusting shift amount
        MOVGE   r0, #0                  ;   ..
        SUBGE   r2, r2, #32             ;   ..
        MOV     r1, r1, LSL r2          ; Perform rest of shift
        RSB     r3, r2, #32             ;   ..
        ORR     r1, r1, r0, LSR r3      ;   ..
        MOV     r0, r0, LSL r2          ;   ..
        RSBS    r0, r0, #0              ; Negate result
        RSC     r1, r1, #0              ;   ..
        MOV     r3, #IVO_bit            ; Overflow so set invalid operation


__dtou64_return
        TST     r3, #FPECause_mask      ; Any exceptions?
        ADDEQ   sp, sp, #LOC_SIZE       ; If not, pop off saved arg and
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}               ;   return
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}               ;   return
  ENDIF
        ORR     r12, r3, #_FpDToU64     ; Save exception info
        LDR     r3, [sp, #OrgOp1h]      ; Load original arg
        LDR     r2, [sp, #OrgOp1l]      ;   ..
        STR     r0, [sp, #ExDResl]      ; Store default result
        STR     r1, [sp, #ExDResh]      ;   ..
        MOV     r1, r12                 ; Exception information
        ADD     r0, sp, #NewResl        ; Pointer to new result
	
        CALL      FPE_Raise               ; Handle exception information
	
    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
        LDR     r0, [sp, #NewResl]      ; Load new result
        LDR     r1, [sp, #NewResh]      ;   ..
        ADD     sp, sp, #LOC_SIZE       ; Pop off exception record and result
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}               ; Return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}               ; Return
  ENDIF

    ENTRY_END __dtoi64


    END
