;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

;  __stou single precision floating point to unsigned integer convert
;
;  Input: r0 - float to be converted
;  Output: r0 - converted float in unsigned integer format
;

; Local stack size and offsets
LOC_SIZE  EQU  0x18
OrgOp1l   EQU  0x14
ExDResl   EQU  0x08
NewResl   EQU  0x10

        GET fpe.asm
        GET kxarm.inc

        AREA |.text|, CODE, READONLY

        Export  __stou
        IMPORT  FPE_Raise

    NESTED_ENTRY __stou
        EnterWithLR_16
        STMFD   sp!, {lr}               ; Save return address
        SUB     sp, sp, #LOC_SIZE       ; Allocate local storage
    PROLOG_END

        MOVS    r12, r0                 ; Save original arg in case of exception
        MOV     r3, #_FpSToU            ; Initialize opcode, no exceptions

        MOVS    r2, r0, ASR #SFrc_len   ; Right justify exponent, save sign bit
        MOV     r0, r0, LSL #SExp_len   ; Left justify mantissa and
        ORR     r0, r0, #1 << 31        ;   insert hidden one (even for denorms)
        BMI     _ffix_negative          ; If negative input, separate case

        RSBS    r2, r2, #31 + SExp_bias ; Determine shift amount
        BLT     shift_left              ; Negative shift is a shift left, NaN,
                                        ;   or INF; zero shift is an overflow
        CMP     r2, #32                 ; See if shifting all bits out
        BGE     shift_right_32          ; If shifting all bits out, return zero

shift_right
        RSB     r1, r2, #32             ; Check for inexact
        MOVS    r1, r0, LSL r1          ;   ..
        ORRNE   r3, r3, #INX_bit        ;   ..
        MOV     r0, r0, LSR r2          ; Shift the result
        B       __stou_return           ; Return

shift_left
        ORR     r3, r3, #IVO_bit        ; Overflow so set invalid operation
        RSB     r2, r2, #0              ; Get left shift amount
        MOV     r0, r0, LSL r2          ; Perform shift
        B       __stou_return           ; Return

shift_right_32                          ; abs(Arg) < 1.0, so losing all bits
        BIC     r3, r3, #IVO_bit        ; Ensure invalid is clear
        MOV     r0, #0                  ; Return zero
        MOVS    r1, r12, LSL #1         ; Check for inexact
        ORRNE   r3, r3, #INX_bit        ; If bits being lost, set inexact
        B       __stou_return           ; Return

_ffix_negative
        ORR     r3, r3, #IVO_bit        ; Have a negative so invalid
        AND     r2, r2, #0xFF           ; Mask off exponent field
        RSBS    r2, r2, #31 + SExp_bias ; Determine shift amount
        BLT     shift_left_neg          ; Negative shift is a shift left, NaN
                                        ;   or INF
        CMP     r2, #32                 ; See if shifting all bits out
        BGE     shift_right_32          ; If shifting all bits out, return zero
                                        ;   note that this is not an invalid
                                        ;   operation exception

shift_right_neg
        MOV     r0, r0, LSR r2          ; Shift the result
        RSB     r0, r0, #0              ; Negate result
        B       __stou_return           ; Return

shift_left_neg
        RSB     r2, r2, #0              ; Get left shift amount
        MOV     r0, r0, LSL r2          ; Perform shift
        RSB     r0, r0, #0              ; Negate result
        B       __stou_return           ; Return

__stou_return
        TST     r3, #FPECause_mask      ; Any exceptions?
        ADDEQ   sp, sp, #LOC_SIZE       ; If not, restore stack and        
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}               ;   return
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}               ;   return
  ENDIF
        STR     r0, [sp, #ExDResl]      ; Store default result
        ADD     r0, sp, #NewResl        ; Pointer to new result
        MOV     r1, r3                  ; Exception information
        MOV     r2, r12                 ; Original arg
	
        CALL    FPE_Raise               ; Handle exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
        LDR     r0, [sp, #NewResl]      ; Load new result
        ADD     sp, sp, #LOC_SIZE       ; Pop off exception record
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}               ; Return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}               ; Return
  ENDIF

    ENTRY_END __stou


    END
