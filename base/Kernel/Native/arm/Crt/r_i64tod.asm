;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; __i64tod: __int64 to double conversion routine.
; __u64tod: unsigned __int64 to double conversion routine.
;
; Input: r1 - Most significant word of 64-bit integer to be converted
;        r0 - Least significant word of 64-bit integer to be converted
;
; Output: r1 - Most significant word of converted number to floating point
;                double precision format.
;         r0 - Least significant word of converted number to floating point
;                double precision format.

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

        Export  __u64tod
        Export  __i64tod
        IMPORT  FPE_Raise

        AREA |.text|, CODE, READONLY

; Prolog must match __i64tod
    NESTED_ENTRY __u64tod
        EnterWithLR_16
        STMFD   sp!, {lr}              ; Save return address
        SUB     sp, sp, #LOC_SIZE      ; Allocate local storage
    PROLOG_END
        STR     r0, [sp, #OrgOp1l]     ; Save original arg in case of exception
        ORRS    r2, r0, r1             ; Check for zero
        STR     r1, [sp, #OrgOp1h]     ; Save original arg in case of exception
        ADDEQ   sp, sp, #LOC_SIZE      ;   If zero, restore stack and
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}              ;   return zero
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}              ;   return zero
  ENDIF
        MOV     r14, #_FpU64ToD        ; Initialize opcode, no exceptions
        MOV     r12, #0                ; Initialize sign to 0 (positive)
        B       LongSingleNormalize
    ENTRY_END __u64tod


; Prolog must match __u64tod
    NESTED_ENTRY __i64tod
        EnterWithLR_16
        STMFD   sp!, {lr}              ; Save return address
        SUB     sp, sp, #LOC_SIZE      ; Allocate local storage
    PROLOG_END
        STR     r0, [sp, #OrgOp1l]     ; Save original arg in case of exception
        ORRS    r2, r0, r1             ; Check for zero
        STR     r1, [sp, #OrgOp1h]     ; Save original arg in case of exception
        ADDEQ   sp, sp, #LOC_SIZE      ;   If zero, restore stack and
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}              ;   return zero
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}              ;   return zero
  ENDIF
        MOV     r14, #_FpI64ToD        ; Initialize opcode, no exceptions
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

        MOV     r3, #DExp_bias+1          ; Load r3 = DExp_bias+63
        ADD     r3, r3, #62               ;   ..
        RSB     r3, r2, r3                ; Calculate exponent

        ORR     r12, r12, r3, LSL #DExp_pos
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
        MOV     r0, r0, LSL r2            ; Shift low word into position

insert_mantissa
        ORR     r3, r12, r1, LSR #12      ; Insert high word into result high
        MOV     r2, r1, LSL #20           ; Insert high word into result low
        ORR     r2, r2, r0, LSR #12       ; Insert low word into result low

        MOVS    r0, r0, LSL #20           ; Check for inexact
        ORRNE   r14, r14, #INX_bit        ; Set inexact if bits are lost

        MOVS    r0, r0, LSL #1            ; Round
                                          ; CS -> guard bit
                                          ; MI -> round bit
                                          ; NE -> sticky bit | round bit

        BCC     __i64tod_return           ; If guard bit clear, leave result

                                          ; Guard bit is set
        MOVS    r0, r0, LSR #1            ; Must clear carry bit
                                          ;   NE -> sticky bit | round bit
        TSTEQ   r2, #0x1                  ; Check lost bit
        ADDNES  r2, r2, #1                ; If G & (L | R | S) round up
        ADC     r3, r3, #0                ;   ..


__i64tod_return
        MOV     r1, r3                    ; Move result into return regs
        MOV     r0, r2                    ;   ..

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
        STR     r1, [sp, #ExDResh]        ;   ..
        ADD     r0, sp, #NewResl          ; Pointer to new result
        MOV     r1, r14                   ; Exception information
	
        CALL    FPE_Raise                 ; Deal with exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
        LDR     r0, [sp, #NewResl]        ; Load new result
        LDR     r1, [sp, #NewResh]        ;   ..
        ADD     sp, sp, #LOC_SIZE         ; Pop off exception info and orig arg
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}                 ; Return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}                 ; Return
  ENDIF

    ENTRY_END __i64tod


    END
