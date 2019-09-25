;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

        GET     fpe.asm
        GET     kxarm.inc

        CodeArea |.text|

        IMPORT  FPE_Raise

SNaNInf     EQU     NaNInfExp_Single - EIExp_bias + SExp_bias
DNaNInf     EQU     NaNInfExp_Double - EIExp_bias + DExp_bias
DExp_max    EQU     2047
SFrac_len   EQU     23

exp   RN   3
sign  RN   2
tmp   RN  12

;==============================================================================
;Format conversions

        [ :DEF: d2f_s

; Local storage size and offsets
LOC_SIZE     EQU    0x18
OrgOp1h      EQU    0x14
OrgOp1l      EQU    0x10
ExDResl      EQU    0x08
NewResl      EQU    0x10

        ; Ensure the defines are what they should be.  Note that there was
        ;  a problem when we swapped the double halves as the code relied on
        ;  the low half of the double not being the register where floats are
        ;  returned.  I have put these asserts here so the registers don't
        ;  change out from under me.  We don't really need these conditions
        ;  to hold true, just the code needs to be checked after register
        ;  defines are changed.
        ASSERT exp  = r3
        ASSERT sign = r2
        ASSERT tmp  = r12
        ASSERT dOPh = r1
        ASSERT dOPl = r0
        ASSERT fOP  = r0

        Export  __dtos

    NESTED_ENTRY __dtos
        EnterWithLR_16
        STMFD   sp!, {r4, lr}               ; Save off non-volatile, lr
        SUB     sp, sp, #LOC_SIZE           ; Allocate stack space
    PROLOG_END

        STR     r1, [sp, #OrgOp1h]          ; Save off arg in case of exception
        MOV     r4, #_FpDToS                ; Set double->float convert
        ORRS    tmp, dOPl, dOPh, LSL #1     ; Special check for zero
        STR     r0, [sp, #OrgOp1l]          ; Save off arg in case of exception
        BEQ     __dtos_return_zero          ; If zero, return it
        AND     sign, dOPh, #Sign_bit
        MOV     tmp, #(DExp_bias - SExp_bias) << (DExp_pos+1)
        RSB     dOPh, tmp, dOPh, LSL #1
        MOVS    exp, dOPh, LSR #DExp_pos+1
        BEQ     _d2f_ExpUnderflow
        CMP     exp, #254
        BHS     _d2f_uncommon
_d2f_round
        MOVS    tmp, dOPl, LSL #3           ; Check for inexact
        ORRNE   r4, r4, #INX_bit            ; Raise inexact if inexact
        ORRS    tmp, sign, dOPl, LSR #29
        MOV     r3, dOPl                    ; * Need to save dOPl somewhere else
        ADC     fOP, tmp, dOPh, LSL #2      ; dOPh already shifted 1 bit
        BCC     __dtos_return
        MOVS    r3, r3, LSL #4              ; * Was: MOVS    dOPl, dOPl, LSL #4
        BNE     __dtos_return
        BIC     fOP, fOP, #1
        B       __dtos_return

_d2f_uncommon                   ; exp out of range - check for special cases
        CMP     exp, #(-(DExp_bias - SExp_bias)) :AND: 0x7FF
        BHS     _d2f_ExpUnderflow
        ; if exponent 254 - test for overflow during rounding
        CMP     exp, #254
        MOVEQ   tmp, dOPh, LSL #DExp_len
        ORREQ   tmp, tmp, dOPl, LSR #DFhi_len
        CMNEQ   tmp, #1 << 8                    ; check if dOP rounds to overflow         
        BLO     _d2f_round                      ; no - continue (8 clk overhead)
        
_d2f_ExpOverflow                                ; overflow, inf/NaN 
        ADD     exp, exp, #1
        TEQ     exp, #DExp_max - DExp_bias + SExp_bias + 1
        MOVNE   fOP, sign
        BNE     __dtos_return_overflow          ; overflow
_d2f_Inf_or_NaN                                 ; found inf or NaN
        ORRS    tmp, dOPl, dOPh, LSL #DExp_len  ; infinity if EQ
        MOVEQ   tmp, #0xFF000000
        ORR     fOP, sign, tmp, LSR #1          ; return signed infinity
        BEQ     __dtos_return
        ; sign in fOP
        MOVS    tmp, dOPh, LSL #DExp_len
        ORRPL   r4, r4, #IVO_bit                ; Set invalid if SNaN
        LDR     r2, fNaN                        ; Return quiet NaN
        MOV     tmp, dOPh, LSL #DExp_len-9      ;   insert high mantissa bits
        ORR     tmp, tmp, dOPl, LSR #29         ;   insert low mantissa bits
        ORR     r0, r2, tmp                     ; Set exp, high mant bit
        B       __dtos_return

fNaN    DCD &7FC00000

__dtos_return_zero
        MOV     fOP, dOPh                       ; dOPh has the correctly signed
        B       __dtos_return                   ;   float zero, so return it

_d2f_ExpUnderflow
        CMP     exp, #0
        SUBNE   exp, exp, #0x800
        ; was underflow - return denorm or zero (exp is -X .. 0)
        RSB     exp, exp, #SExp_len+1   ; right shift for dOPh
        RSBS    tmp, exp, #33           ; left shift for dOPh rounding bits
        MOVLS   fOP, sign               ; LO: shift larger than 33 -> return signed zero
        ORRLS   r4, r4, #UNF_bit :OR: INX_bit
        BLS     __dtos_return

        MOV     dOPh, dOPh, LSL #DExp_len-1     ; dOPh shift left 1 bit
        ORR     dOPh, dOPh, dOPl, LSR #DFhi_len+1
        ORR     dOPh, dOPh, #1 << 31

        MOVS    tmp, dOPh, LSL tmp              ; CS -> round
        ORRNE   r4, r4, #UNF_bit :OR: INX_bit
        MOV     tmp, dOPl                       ; save dOPl since we may need it
        ADC     fOP, sign, dOPh, LSR exp
        BCC     __dtos_return
        MOVEQS  tmp, tmp, LSL #32 - (DFhi_len+1) ; * Was: MOVEQS dOPl, dOPl, LSL #32
        BICEQ   fOP, fOP, #1
        B       __dtos_return


__dtos_return_overflow
        ORR     r4, r4, #OVF_bit :OR: INX_bit   ; Set exception information
        AND     r0, r0, #0x80000000             ; Keep sign bit
        MOV     r1, #0xFF000000                 ; Set exponent to max
        ORR     r0, r0, r1, LSR #1              ;   ..
        

__dtos_return
        TST     r4, #FPECause_mask              ; Check for exceptions
        MOV     r1, r4                          ; Move exception info.
        ADDEQ   sp, sp, #LOC_SIZE               ; If none, pop input arg
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {r4, lr}                   ;   restore r4 and return
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {r4, pc}                   ;   restore r4 and return
  ENDIF

        STR     r0, [sp, #ExDResl]              ; Store default result
        LDR     r2, [sp, #OrgOp1l]              ; Load original arg
        LDR     r3, [sp, #OrgOp1h]              ;  ..
        ADD     r0, sp, #NewResl                ; Pointer to new result

        CALL      FPE_Raise                     ; Deal with exception info.

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF

        LDR     r0, [sp, #NewResl]              ; Load new result
        ADD     sp, sp, #LOC_SIZE               ; Pop exception record, arg
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {r4, lr}                   ; Restore r4 and return
        BX      lr
  ELSE
        LDMFD   sp!, {r4, pc}                   ; Restore r4 and return
  ENDIF

    ENTRY_END __dtos

        ]

;------------------------------------------------------------------------------

        [ :DEF: f2d_s

LOC_SIZE   EQU  0x18
OrgOp1l    EQU  0x14
ExDResh    EQU  0x0c
ExDResl    EQU  0x08
NewResh    EQU  0x14
NewResl    EQU  0x10

        Export  __stod
        IMPORT  FPE_Raise

        ; Ensure the defines are what they should be.  Note that there was
        ;  a problem when we swapped the double halves as the code relied on
        ;  the low half of the double not being the register where floats are
        ;  passed.  I have put these asserts here so the registers don't
        ;  change out from under me.  We don't really need these conditions
        ;  to hold true, just the code needs to be checked after register
        ;  defines are changed.
        ASSERT exp  = r3
        ASSERT sign = r2
        ASSERT tmp  = r12
        ASSERT dOPh = r1
        ASSERT dOPl = r0
        ASSERT fOP  = r0

  NESTED_ENTRY __stod
        EnterWithLR_16
        STMFD   sp!, {lr}                   ; Save return address
        SUB     sp, sp, #LOC_SIZE           ; Allocate local storage
  PROLOG_END
        STR     r0, [sp, #OrgOp1l]          ; Store original arg in case of exception
        ADD     tmp, fOP, #1 << SExp_pos    ; filter out inf/NaN/denorm/zero
        TST     tmp, #254 << SFrac_len
        BEQ     _f2d_uncommon
        MOV     tmp, fOP
        MOV     dOPl, tmp, LSL #32 - 3
        MOVS    dOPh, tmp, ASR #3
        ADD     dOPh, dOPh, #(DExp_bias - SExp_bias) << DExp_pos
        ADDPL   sp, sp, #LOC_SIZE
  IF Interworking :LOR: Thumbing
        LDMPLFD sp!, {lr}
        BXPL    lr
  ELSE
        LDMPLFD sp!, {pc}
  ENDIF
        SUB     dOPh, dOPh, #0x700 << DExp_pos
        ADD     sp, sp, #LOC_SIZE
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}
        BX      lr
  ELSE
        LDMFD   sp!, {pc}
  ENDIF

_f2d_uncommon
        TST     tmp, #1 << SExp_pos         ; inf/NaN -> EQ, zero/denorm ->NE
        MOV     tmp, fOP
        BEQ     _f2d_Inf_or_NaN
_f2d_denorm
        MOVS    dOPl, tmp, LSL #1           ; zero -> EQ
        MOVEQ   dOPh, tmp
        ADDEQ   sp, sp, #LOC_SIZE           ; dOPl zero, dOPh sign bit
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}
  ENDIF
                      

        ; We have a denormal that must be normalized.  The exponent and sign
        ; are initialized, then the input argument's mantissa is shifted left
        ; until the hidden one is left justified.  The exponent is adjusted to
        ; account for the shifts.  Then the hidden one is removed and the
        ; final result assembled.
        AND     exp, tmp, #Sign_bit         ; Extract sign
        ADD     r1, exp, #(DExp_bias-SExp_bias) << DExp_pos
                                            ; Initialize exponent
        MOV     r0, tmp, LSL #9             ; Extract mantissa and left justify

        MOVS    r2, r0, LSR #16             ; Any high 16 bits set?
        SUBEQ   r1, r1, #16 << DExp_pos     ; If not, adjust exponent
        MOVEQ   r0, r0, LSL #16             ;   shift mantissa

        TST     r0, #0xFF000000             ; Any high 8 bits set?
        SUBEQ   r1, r1, #8 << DExp_pos      ; If not, adjust exponent
        MOVEQ   r0, r0, LSL #8              ;   shift mantissa

        TST     r0, #0xF0000000             ; Any high 4 bits set?
        SUBEQ   r1, r1, #4 << DExp_pos      ; If not, adjust exponent
        MOVEQ   r0, r0, LSL #4              ;   shift mantissa

        TST     r0, #0xC0000000             ; Any high 2 bits set?
        SUBEQ   r1, r1, #2 << DExp_pos      ; If not, adjust exponent
        MOVEQS  r0, r0, LSL #2              ;   shift mantissa

        MOVPL   r0, r0, LSL #1              ; If high bit clear, adjust exponent
        SUBPL   r1, r1, #1 << DExp_pos      ;   shift mantissa
        
        MOV     r0, r0, LSL #1              ; Account for hidden 1
        ORR     r1, r1, r0, LSR #12         ; Form sign, exp, high mantissa
        MOV     r0, r0, LSL #20             ; Form low mantissa
        ADD     sp, sp, #LOC_SIZE           ; Restore stack and
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}                   ;   return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}                   ;   return
  ENDIF


_f2d_Inf_or_NaN                             ; fOP is NaN/infinity. 
        MOVS    dOPl, tmp, LSL #SExp_len+1  ; EQ -> inf
        ORREQ   dOPh, tmp, #0x007 << DExp_pos   ; tranform float inf to double inf
        ADDEQ   sp, sp, #LOC_SIZE           ; Restore stack and
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}                   ;   return
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}                   ;   return
  ENDIF
        ; MI if quiet NaN - sign in fOP
        BPL     __stod_snan
        ; Have a QNaN so copy the mantissa bits and return the QNaN
        MOV     dOPh, tmp, ASR #3           ; Load mantissa high, sign
        MOV     dOPl, tmp, LSL #29          ; Load mantissa low
        ORR     dOPh, dOPh, #0x70000000     ; Force exp to max
        ADD     sp, sp, #LOC_SIZE           ; Restore stack and
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}                   ;   return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}                   ;   return
  ENDIF

__stod_snan                                 ; Got an SNaN so raise exception
        LDR     r2, [sp, #OrgOp1l]          ; Load original operand
        MOV     r1, r12, ASR #3             ; Load mantissa high, sign
        MOV     r0, r12, LSL #29            ; Load mantissa low
        ORR     r1, r1, #0x70000000         ; Force exp to max
        ORR     r1, r1, #0x00080000         ; Make QNaN
        STR     r1, [sp, #ExDResh]          ; Store default result
        STR     r0, [sp, #ExDResl]          ;   ..
        ADD     r0, sp, #NewResl            ; Pointer to return result
        MOV     r1, #_FpSToD                ; Load opcode and exception info.
        ORR     r1, r1, #IVO_bit            ;   ..

        CALL      FPE_Raise                 ; Deal with exception info.

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF

        LDR     r1, [sp, #NewResh]          ; Load new return value
        LDR     r0, [sp, #NewResl]          ;   ..
        ADD     sp, sp, #LOC_SIZE           ; Pop space off stack
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}                   ; Return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}                   ; Return
  ENDIF

    ENTRY_END __stod
        ]

;==============================================================================

        END
