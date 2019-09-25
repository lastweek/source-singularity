;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

;  __stou64 single precision floating point to unsigned 64-bit integer convert
;
;  Input: r0 - float to be converted
;  Output: r1 - most significant word of converted float in
;                 unsigned 64-bit integer format
;          r0 - least significant word of converted float in
;                 unsigned 64-bit integer format
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

        Export  __stou64
        IMPORT  FPE_Raise

    NESTED_ENTRY __stou64
        EnterWithLR_16
        STMFD   sp!, {lr}               ; Save return address
        SUB     sp, sp, #LOC_SIZE       ; Allocate local storage
    PROLOG_END
        MOVS    r12, r0                 ; Save original arg in case of exception
        MOVS    r2, r0, ASR #SFrc_len   ; Right justify exponent, save sign bit
        MOV     r0, r0, LSL #SExp_len   ; Left justify mantissa and
        ORR     r1, r0, #1 << 31        ;   insert hidden one (even for denorms)
        MOV     r0, #0                  ;   clear low 32 bits of result
        BMI     _ffix_negative          ; If negative input, separate case

        RSBS    r2, r2, #63 + SExp_bias ; Determine shift amount
        BLT     shift_left              ; Negative shift is a shift left,
                                        ;   NaN or INF; all are invalid op
        CMP     r2, #64                 ; See if shifting all bits out
        BGE     shift_right_64          ; If shifting all bits out, return zero

shift_right
        ; r2 contains the right shift amount.  It is on the range of 1..63.
        CMP     r2, #32                 ; Check if we are shifting >= 32
        SUBGE   r2, r2, #32             ;   If so, do a 32 bit shift by moving
        MOVGE   r0, r1                  ;   words and adjusting the shift
        MOVGE   r1, #0                  ;   amount

        RSB     r2, r2, #32             ; 32 - right shift amount
        MOVS    r3, r0, LSL r2          ; Check for inexact
        RSB     r3, r2, #32             ; Right shift amount
        MOV     r0, r0, LSR r3          ; Shift the result
        ORR     r0, r0, r1, LSL r2      ;   ..
        MOV     r1, r1, LSR r3          ;   ..
        MOVNE   r3, #INX_bit            ; If inexact, set inexact
        MOVEQ   r3, #0                  ; Otherwise set no exceptions
        B       __stou64_return         ; Return

shift_left
        RSB     r2, r2, #0              ; Get positive left shift amount
        MOV     r3, #IVO_bit            ; Set invalid
        MOV     r1, r1, LSL r2          ; Shift result
        B       __stou64_return         ; Return

shift_right_64                          ; abs(Arg) < 1.0, so losing all bits
        MOV     r0, #0                  ; Return zero
        MOV     r1, #0                  ; Return zero
        MOVS    r2, r12, LSL #1         ; Check for inexact
        MOVNE   r3, #INX_bit            ; If bits being lost, set inexact
        MOVEQ   r3, #0
        B       __stou64_return         ; Return



_ffix_negative
        AND     r2, r2, #0xFF           ; Mask off exponent field
        RSBS    r2, r2, #63 + SExp_bias ; Determine shift amount
        BLE     shift_left_neg          ; Negative shift is a shift left, NaN
                                        ;   or INF
        CMP     r2, #64                 ; See if shifting all bits out
        BGE     shift_right_64          ; If shifting all bits out, return zero

shift_right_neg
        ; r2 contains the right shift amount.  It is on the range of 1..63.
        CMP     r2, #32                 ; Check if we are shifting >= 32
        SUBGE   r2, r2, #32             ;   If so, do a 32 bit shift by moving
        MOVGE   r0, r1                  ;   words and adjusting the shift
        MOVGE   r1, #0                  ;   amount

        RSB     r2, r2, #32             ; 32 - right shift amount
        RSB     r3, r2, #32             ; Right shift amount
        MOV     r0, r0, LSR r3          ; Shift the result
        ORR     r0, r0, r1, LSL r2      ;   ..
        MOV     r1, r1, LSR r3          ;   ..
        RSBS    r0, r0, #0              ; Negate result
        RSC     r1, r1, #0              ;   ..
        MOV     r3, #IVO_bit            ; Set invalid
        B       __stou64_return         ; Return


shift_left_neg
        MOV     r3, #IVO_bit            ; Set invalid
        RSB     r2, r2, #0              ; Get positive left shift amount
        MOV     r1, r1, LSL r2          ; Shift result
        RSBS    r0, r0, #0              ; Negate result
        RSC     r1, r1, #0              ;   ..
        B       __stou64_return         ; Return


__stou64_return
        TST     r3, #FPECause_mask      ; Any exceptions?
        ADDEQ   sp, sp, #LOC_SIZE       ; If not, restore stack
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}               ;   and return
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}               ;   and return
  ENDIF
        STR     r0, [sp, #ExDResl]      ; Store default result
        STR     r1, [sp, #ExDResh]      ;   ..
        ADD     r0, sp, #NewResl        ; Pointer to new result
        ORR     r1, r3, #_FpSToU64      ; Exception information
        MOV     r2, r12                 ; Original arg
	
        CALL      FPE_Raise             ; Handle exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
        LDR     r0, [sp, #NewResl]      ; Load new result
        LDR     r1, [sp, #NewResh]      ;   ..
        ADD     sp, sp, #LOC_SIZE       ; Pop off exception record
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}               ; Return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}               ; Return
  ENDIF

    ENTRY_END __stou64

    END
