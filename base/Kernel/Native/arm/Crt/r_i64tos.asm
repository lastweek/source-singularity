;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; __int64 to float and unsigned __int64 to float conversion routine.
;
; Input: r1 - Most significant word of 64-bit integer to be converted
;        r0 - Least significant word of 64-bit integer to be converted
;
; Output: r0 - Converted number to floating point single precision format.
;

; Local storage size and offsets
LOC_SIZE     EQU    0x18
OrgOp1h      EQU    0x14
OrgOp1l      EQU    0x10
ExDResl      EQU    0x08
NewResl      EQU    0x10

        GET fpe.asm
        GET kxarm.inc

        Export  __u64tos
        Export  __i64tos
        IMPORT  FPE_Raise

        AREA |.text|, CODE, READONLY

; Prolog must match __i64tos
    NESTED_ENTRY __u64tos
        EnterWithLR_16
        STMFD   sp!, {lr}              ; Save return address
        SUB     sp, sp, #LOC_SIZE
    PROLOG_END
        STR     r0, [sp, #OrgOp1l]     ; Save original arg in case of exception
        ORRS    r2, r0, r1             ; Check for zero
        STR     r1, [sp, #OrgOp1h]     ; Save original arg in case of exception
        ADDEQ   sp, sp, #LOC_SIZE      ; If zero, restore stack
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}              ;   and return zero
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}              ;   and return zero
  ENDIF
        MOV     r14, #_FpU64ToS        ; Initialize opcode, no exceptions
        MOV     r12, #0
        B       LongSingleNormalize
    ENTRY_END __u64tos

; Prolog must match __u64tos
    NESTED_ENTRY __i64tos
        EnterWithLR_16
        STMFD   sp!, {lr}              ; Save return address
        SUB     sp, sp, #LOC_SIZE
    PROLOG_END
        STR     r0, [sp, #OrgOp1l]     ; Save original arg in case of exception
        ORRS    r2, r0, r1             ; Check for zero
        STR     r1, [sp, #OrgOp1h]     ; Save original arg in case of exception
        ADDEQ   sp, sp, #LOC_SIZE      ; If zero, restore stack
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}              ;   and return zero
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}              ;   and return zero
  ENDIF
        MOV     r14, #_FpI64ToS        ; Initialize opcode, no exceptions
        ANDS    r12, r1, #Sign_bit     ; Extract sign
        BEQ     LongSingleNormalize    ; Positive value so do convert
        RSBS    r0, r0, #0             ; Else we have a negative number so
        RSC     r1, r1, #0             ;   take the 2's complement inverse


; Sign is in r12.
; Mantissa abs(input 64-bit integer) is stored in r1:r0.
;
; Sign
;      +-+-------------------------------+
; r12: |S|0000000000000000000000000000000|
;      +-+-------------------------------+
;
; Unnormalized mantissa
;     +--------------------------------+
; r1: |    Most Significant Word       |
;     +--------------------------------+
;
;     +--------------------------------+
; r0: |    Least Significant Word      |
;     +--------------------------------+
;
; Only the high mantissa is shifted.  After it is shifted into the correct
; position, the low mantissa is shifted into place.  The exception is the
; first shift by 32 which moves the low mantissa into the high.
;
LongSingleNormalize
        MOV     r2, #0                    ; Exponent adjustment/mantissa shift

        CMP     r1, #0                    ; Any high 32 bits set?
        ADDEQ   r2, r2, #32               ; If not, adjust exponent
        MOVEQ   r1, r0                    ;   and shift the WHOLE mantissa
        MOVEQ   r0, #0                    ;   ..

        MOVS    r3, r1, LSR #16           ; Any high 16 bits set?
        ADDEQ   r2, r2, #16               ; If not, adjust exponent
        MOVEQ   r1, r1, LSL #16           ;   and shift high mantissa

        TST     r1, #0xFF000000           ; Any high 8 bits set?
        ADDEQ   r2, r2, #8                ; If not, adjust exponent
        MOVEQ   r1, r1, LSL #8            ;   and shift high mantissa

        TST     r1, #0xF0000000           ; Any high 4 bits set?
        ADDEQ   r2, r2, #4                ; If not, adjust exponent
        MOVEQ   r1, r1, LSL #4            ;   and shift high mantissa

        TST     r1, #0xC0000000           ; Any high 2 bits set?
        ADDEQ   r2, r2, #2                ; If not, adjust exponent
        MOVEQS  r1, r1, LSL #2            ;   and shift high mantissa

        ADDPL   r2, r2, #1                ; If high bit clear, adjust exponent
        MOVPL   r1, r1, LSL #1            ;   and shift high mantissa

        RSB     r3, r2, #SExp_bias+63     ; Calculate exponent
        ORR     r12, r12, r3, LSL #SExp_pos
                                          ; Combine sign and exponent

        CMP     r2, #32                   ; If all low shifted into high ...
        MOV     r1, r1, LSL #1            ; Hide the hidden one
        ADD     r2, r2, #1                ;  ..
        BGE     insert_mantissa           ; ... just insert the mantissa

        ; R2 contains the amount the mantissa has been shifted left, including
        ; the shift for the hidden one.  It is in the range 1..32.  R1 contains
        ; the high portion of the mantissa without any of R0 shifted into it.
        ; R0 is unshifted.  Note that the case where the entire low word was
        ; shifted into the high word has already been taken care of and never
        ; reaches this code.
        RSB     r3, r2, #32               ; Determine amount of low mantissa
                                          ;   shifted into high mantissa

        ORR     r1, r1, r0, LSR r3        ; Get part of low word shifted in high
        MOVS    r0, r0, LSL r2            ; Bits lost in low word?
        ORRNE   r1, r1, #1                ; If lost bits, set sticky

insert_mantissa
        ORR     r0, r12, r1, LSR #9       ; Insert mantissa into result

        MOVS    r1, r1, LSL #23           ; Inexact?
        ORRNE   r14, r14, #INX_bit        ; If bits set, set inexact

        MOVS    r1, r1, LSL #1            ; Round
                                          ; CS -> guard bit
                                          ; MI -> round bit
                                          ; NE -> sticky bit | round bit
        BCC     __i64tos_return
        TSTEQ   r0, #0x1                  ; Check lost bit
        ADDNE   r0, r0, #1                ; If G & (L | R | S) round up


__i64tos_return
        TST     r14, #FPECause_mask       ; Any exceptions?
        ADDEQ   sp, sp, #LOC_SIZE         ;   pop off original arg, and
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}                 ;   return
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}                 ;   return
  ENDIF

        ; Have an exception
        LDR     r2, [sp, #OrgOp1l]        ; Load original operand
        LDR     r3, [sp, #OrgOp1h]        ;   ..
        STR     r0, [sp, #ExDResl]        ; Store default result
        ADD     r0, sp, #NewResl          ; Pointer to new result
        MOV     r1, r14                   ; Exception information

	CALL    FPE_Raise

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
        LDR     r0, [sp, #NewResl]        ; Load new result
        ADD     sp, sp, #LOC_SIZE         ; Pop off exception info and orig arg
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}                 ; Return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}                 ; Return
  ENDIF

    ENTRY_END __i64tos

	END
