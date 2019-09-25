;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

	GBLL add_s

	GET veneer_d.asm

	END


;;;;  THE BELOW ROUTINE SHOULD WORK, BUT THE ARM ROUTINES SHOULD BE FASTER.


;
; Translated to ARM from SH3 FP emulation routines.
;
; __addd  Double precision floating point addition.
; Input:
;   r0 - Arg1.low
;   r1 - Arg1.high
;   r2 - Arg2.low
;   r3 - Arg2.high
; Output:
;   r0 - Result.low
;   r1 - Result.high
;
; Note:
;   If any FP exceptions are enabled, this routine may raise an exception.
;
;
; IEEE DOUBLE FORMAT
;
; 8 BYTES (LONG WORD * 2)
; 63 62       52 51                                                 0
; +-+-----------+----------------------------------------------------+
; |s|   e(11)   |                         m(52)                      |
; +-+-----------+----------------------------------------------------+
;               ^ point
;
; INFINITY NUMBER : e =  2047          m = 0
; ZERO            : e =     0          m = 0
; NaN             : e =  2047          m != 0
; DENORMAL NUMBER : e =     0          m != 0
;


    GET      fpe.asm

    Export   __addd
    Export   __subd

    IMPORT   FPE_Raise

    AREA |.text|, CODE, READONLY


CARRY_CHECK EQU 0x01000000
MSB         EQU 0x00800000
NORMAL      EQU 0x00100000


; Note: the SEH prolog below must match the SEH prolog for __addd.

__subd

    STMFD   sp!, {r0-r10, lr} ; Save off args and non-volatiles and lr

    MOV     r8, r1          ; Load parameter1 as R8 R0
	MOV     r4, r2          ; Load parameter2 as R2 R4
	MOV     r2, r3          ;   ...
    MOV     r5, #_FpSubD    ; Double add, assume no exceptions
    EOR     r2, r2, #0x80000000
                            ; Toggle sign bit on parameter2
    B       add_in          ; Then go add


; Note: the SEH prolog below must match the SEH prolog for __subd

__addd

    STMFD   sp!, {r0-r10, lr} ; Save off args and non-volatiles and lr

    MOV     r8, r1          ; Load parameter1 as R8 R0
	MOV     r4, r2          ; Load parameter2 as R2 R4
	MOV     r2, r3          ;   ...
    MOV     r5, #_FpAddD    ; Double add, assume no exceptions


add_in

; If abs(parameter1) < abs(parameter2) then swap them so that the resulting
; parameter1 has the larger magnitude.  This guarantees that only parameter2
; might need to be shifted right before adding.  Because of denormal numbers,
; it's not sufficient to compare only the exponents; the entire mantissa must
; be checked as well. 
;
; if ((abs(parameter1).hi < abs(parameter1).hi) ||
;     ((abs(parameter1.hi == abs(parameter2)) &&
;         (parameter1.lo < parameter2.lo)))
;     swap parameter1 and parameter2

    MOV     r3, r8, LSL #1      ; Extract copies of just the magnitudes
    CMP     r3, r2, LSL #1      ;    of each parameter
    CMPEQ   r0, r4              ; if ((abs(param1).hi < abs(param2)).hi
	                            ;     ||
	BHS     end_swap            ;   ((abs(param1).hi == abs(param2).hi)
                                ;     &&
                                ;   (param1.lo < param2.lo)))
                                ;   ..
swap
    MOV     r3,r8               ;   Swap parameter1 and parameter2
    MOV     r8,r2               ;     ..
    MOV     r2,r3               ;     ..
    MOV     r3,r0               ;     ..
    MOV     r0,r4               ;     ..
    MOV     r4,r3               ;     ..
end_swap

; Unpack parameters.
;
; R8 R0:   mantissa1            R2 R4:   mantissa2
; R9:      exponent1            R1:      exponent2
; R10:     sign1                R6:      sign2
;
; R5:      Exception flags

    MOV     r9, r8, LSL #1     ; Extract exponent1
	MOV     r9, r9, LSR #21    ;   ...
    MOV     r1, r2, LSL #1     ; Extract exponent2
	MOV     r1, r1, LSR #21    ;   ...
    MVN     r3, #0             ; Set up to extract mantissas
    MOV     r10, r8            ; Extract sign1
    MOV     r6, r2             ; Extract sign2
    AND     r8, r8, r3, LSR #12; Extract mantissa1
    AND     r2, r2, r3, LSR #12; Extract mantissa2
 

; Check for exceptional cases.  All NaNs, infinities, and 0's are eliminated.
; Denormal numbers return here after normalizing them.  After these checks,
; both parameters are normalized numbers.
;
; After potentially swapping the parameters above, it's sufficient to test
; just parameter1 for non-finite values (NaN, inf) to eliminate non-finite
; values in either parameter.  Similarly, it's sufficient to test just
; parameter2 for the unnormalized numbers (exponent2 = 0; denormals and 0).
;
; if (exponent1 == 2047)
;     exception1; parameter1 is nonfinite, parameter2 might be too
; if (exponent2 ==    0)
;     exception2; parameter is 0 or denormal, parameter1 might be too

    ADD     r3, r9, #1        ; if (exponent1==2047)
    CMP     r3, #2048         ;  ...
    BEQ     exception1        ;   exception1
    CMP     r1, #0            ; if (exponent2==0)
    BEQ     exception2        ;   exception2
exception_return2
 
; Shift the mantissas left 3 bits to make room for guard, round and sticky bits
; (G,R,S).  Then set their hidden bits.

    MOV     r8, r8, LSL #3    ; Shift mantissa1 left 3 for (G,R,S)
	ORR     r8, r8, r0, LSR #29;   ...
	MOV     r0, r0, LSL #3    ;   ...

    MOV     r2, r2, LSL #3    ; Shift mantissa2 left 3 for (G,R,S)
	ORR     r2, r2, r4, LSR #29;   ...
	MOV     r4, r4, LSL #3    ;   ...

     
    ORR     r8, r8, #0x00800000  ; Set each mantissa's hidden bit
    ORR     r2, r2, #0x00800000  ;   ..

; Scale parameter2 so that its exponent matches that of parameter1, preparing
; for the addition.  Because of the swap earlier, parameter2 always scales by
; shifting right (if it shifts at all).
;
; shift = exponent1 - exponent2
; if shift <= -55
;     // entire mantissa2 shifts into the sticky bit; just set S
; else
;     if (shift <= -32)
;         // "shift" by moving high word to low word
;     if (shift != 0)
;         // shift by dynamic shifting

scale
    SUBS    r1, r9, r1      ; shift = exponent2 - exponent1
    BEQ     scale_end       ; Shift == 0?
	CMP     r1, #3          ;**;
    BLE     scale_le_3      ;**; 0 < shift <= 3?   ..
	CMP     r1, #55         ; If shift <= 55 then
    BLE     scale_le_55     ;   ..
    MOV     R2, #0          ; Else (mantissa2,G,R,S) = 1
    MOV     R4, #1          ;   ..
    B       scale_end

scale_le_3                     ;**; No bits are ever lost
	MOV     r4, r4, LSR r1     ; mantissa2 >>= x where 0 < x <= 3
    RSB     r3, r1, #32
	ORR     r4, r4, r2, LSL r3
    MOV     r2, r2, LSR r1
    B       scale_end

scale_le_55                 ; Else shift <= 55
    CMP     r1, #31         ;   If shift < 32
    BLE     scale_le_31     ;     ..
    CMP     r4, #0          ;   Else  S = mantissa2.l != 0
    SUB     r1, r1, #32     ;     (32 fewer bits to shift)
    MOV     r4, r2          ;     Shift 32 bits by moving
    MOV     r2, #0          ;       ..
    ORRNE   r4, r4, #1      ;     Set S if shifted out bits

scale_le_31
    CMP     r1, #0          ;   If shift != 0
    BEQ     scale_end       ;     ..
    RSB     r3, r1, #32     ;   Get 32 - shift
	MOVS    r7, r4, LSL r3  ;   Extract low mantissa shifted out (Sticky==NE)
    MOV     r7, r2, LSL r3  ;   Extract high mantissa shifted into lower
    MOV     r2, r2, LSR r1  ;   Shift high mantissa into position
    MOV     r4, r4, LSR r1  ;   Shift low mantissa into position
    ORR     r4, r4, r7      ;   Insert bits from high mantissa into low
	ORRNE   r4, r4, #1      ;   Set sticky if shifted out bits

scale_end

; Add the mantissas.
;
; if (sign1 == sign2)
;     result = mantissa1 + mantissa2    // Same signs => addition
;     Scale result right if it carried
;     if (result overflowed)
;         return properly signed inf
; else if (mantissa1 == mantissa2)
;     return +0             // Equal values => result = +0
; else
;     result = mantissa1 - mantissa2    // Opposite signs => subtraction
;     Scale result left         // High-order bits were lost

    EORS    r7, r10, r6     ; If sign1 != sign2
	BMI     mantissa_sub    ;   do subtract
    ADDS    r0, r0, r4      ; Else result = mantissa1 + mantissa2
    ADC     r8, r8, r2      ;     ..
	CMP     r8, #CARRY_CHECK;   If the result carried
    BLT     end_calc        ;     ..
    MOVS    r8, r8, LSR #1  ;   Then scale right one
	MOVS    r0, r0, RRX     ;     ..
    ORRCS   r0, r0, #1      ;    (fold lost bit into S)
    ADD     r9, r9, #1      ;   Add 1 to exponent for shift
	ADD     r3, r9, #1      ;   Add 1 to exponent for compare
    CMP     r3, #2048       ;   EQ if overflow
    BLT     end_calc        ;       ..
                            ; Overflowed so
	ORR     r5, r5, #OVF_bit :OR: INX_bit
                            ;       set exception flags
    MOV     r0, #0          ;       and return properly signed inf
    MOV     r8, #0          ;         ..
    B       return_value    ;         ..

; Return +0.

plus_zero
    MOV     r8, #0           ; Return +0
    MOV     r0, #0           ;   ..
    B       return           ;   ..

mantissa_sub
    CMP     r8, r2           ; Else if mantissa1 = mantissa2
    CMPEQ   r0, r4           ;   ..
    BEQ     plus_zero        ;   return +0
man_sub1
    SUBS    r0, r0, r4       ; Else result = mantissa1 - mantissa2
    SBC     r8, r8, r2       ;   ..
;**; Parameter1 always has the larger magnitude; result is always its sign.


; Normalize since high-order bits are lost when subtracting.  Do this in
; chunks.

normalize
    CMP     r8, #0           ; If mantissa.h = 0
    BNE     norm32_end       ;   ..
    MOV     r8, r0           ;   mantissa <<= 32 by moving
    MOV     r0, #0           ;     ..
    SUB     r9, r9, #32      ;   exponent -= 32
norm32_end
    MVN     r3, #0           ; If (mantissa.h & 0xffff0000) = 0
    TST     r8, r3, LSL #16  ;   ..
    BNE     norm16_end       ;
	MOV     r8, r8, LSL #16  ;   mantissa <<= 16
	ORR     r8, r8, r0, LSR #16
	MOV     r0, r0, LSL #16
    SUB     r9, r9, #16      ;   exponent -= 16
norm16_end
    CMP     r8, #CARRY_CHECK ; If mantissa is not too far left
    BLO     overnorm_end     ;   keep normalizing, otherwise, undo

over_norm_loop
    MOVS    r8, r8, LSR #1   ;   mantissa1 >>= 1
    MOV     r0, r0, RRX      ;     ..
    ADD     r9, r9, #1       ;   exponent1++
    CMP     r8, #CARRY_CHECK ; If mantissa is still too far left
    BHS     over_norm_loop   ;   ..
    B       end_norm         ; Done

overnorm_end
    CMP     r8, #MSB         ; If mantissa is too far right
    BGE     end_norm         ;   ..

norm_loop
    MOVS    r0, r0, LSL #1   ; mantissa1 <<= 1
    MOV     r8, r8, LSL #1   ;   ..
    ORRCS   r8, r8, #1       ;   ..
    SUB     r9, r9, #1       ; exponent1--
    CMP     r8, #MSB         ; If mantissa is still too far right
    BLT     norm_loop        ;   ..

end_norm
end_calc

; Denormalize the result if necessary, with no concern for performance.
; Addition (and thus subtraction) can never generate less significant bits than
; those of the original operands.  Thus, denormalization never results in lost
; bits to fold into S.

    CMP     r9, #0          ; If exponent < 0
    BGT     end_denormal    ;   ..
    RSB     r9, r9, #0      ; Then shift right exponent1 places
    ADD     r9, r9, #1      ;   +1 for the non-hidden bit
denormal_loop
    MOVS    r8, r8, LSR #1  ;   ..
    MOV     r0, r0, RRX     ;   ..
    SUBS    r9, r9, #1      ;   ..
    BNE     denormal_loop   ;   ..
end_denormal

; Round to nearest.  If rounding occurs, set inexact and
; mantissa += G & ( L | R | S ).  If the rounding carries, then renormalize.
;
; Addition (and thus subtraction) can never generate less significant bits than
; those of the original operands.  Thus, rounding can never meet either of the
; IEEE loss of accuracy tests for underflow.  Nor can rounding cause MaxDenorm
; to carry to MinNormal.
;
; Test for inexact.
    TST     r0, #0x7        ; If G|R|S (=> rounding required)
    BEQ     end_round       ;   ..
    ORR     r5, r5, #INX_bit;   result is inexact (can't underflow)

; Round to nearest.
    TST     r0, #0x4        ; If G &&
    BEQ     end_round       ;   ..
    TST     r0, #0xB        ;   L|R|S
    BEQ     end_round       ;   ..
    ADDS    r0, r0, #0x8    ; Then round the mantissa up
    ADC     r8, r8, #0      ;

	CMP     r8, #CARRY_CHECK;   If the rounding carried
    BLT     end_round       ;     (mantissa >= 0x01000000)
    ADD     r9, r9, #2      ;   Then renormalize
    CMP     r9, #2048       ;     If rounding caused overflow
	SUB     r9, r9, #1
    ORREQ   r5, r5, #OVF_bit :OR: INX_bit
	                        ;  Report overflow (=> inexact)
end_round

; Pack the result back into IEEE format.

return_value
    MOV     r0, r0, LSR #3  ; Shift mantissa right 3
    ORR     r0, r0, r8, LSL #29 ;   ..
	MOV     r1, r8, LSR #3  ;   ..
	BIC     r1, r1, #0x0FF00000
	                        ; Mask away the hidden bit and possibly one bit
                            ;   higher if round incremented mantissa.
                            ;   0xFF<<20 is probably overkill, but safe.
    ORR     r1, r1, r9, LSL #20
                            ; Merge exponent and mantissa
    AND     r10, r10, #0x80000000
    ORR     r1, r1, r10     ; Merge sign with exponent and mantissa

; If any trap enable flags are set corresponding to exception flags set,
; set the corresponding cause bits and cause a trap.
;
; if (exception)
;     call handler
;     extract the possibly updated result
; return

return
    TST     r5, #FPECause_mask   ; If any exceptions occurred ...
    BEQ     done

;;
;;  Register usage:
;;      r0 - Default result.low
;;      r1 - Default result.high
;;      r5 - Exception information
;;
;;  Stack:
;;      0x10(sp) - up: Saved registers
;;      0xC(sp): Original Arg2.high
;;      0x8(sp): Original Arg2.low
;;      0x4(sp): Original Arg1.high
;;      0x0(sp): Original Arg1.low
;;
        LDR     r2, [sp, #0x8]           ; Load original Arg2.low
        LDR     r3, [sp, #0xC]           ; Load original Arg2.high
        SUB     sp, sp, #0x8             ; Make room for exception information
        STR     r2, [sp, #0x0]           ; Store original Arg2.low
        STR     r3, [sp, #0x4]           ; Store original Arg2.high
        LDR     r3, [sp, #0x8]           ; Load original Arg1.low
        LDR     r2, [sp, #0xC]           ; Load original Arg1.high
        STR     r0, [sp, #0x8]           ; Store default result.low
        STR     r1, [sp, #0xC]           ; Store default result.high
        MOV     r1, r5                   ; Move exception information
        ADD     r0, sp, #0x10            ; Pointer for return value

;;  Register Usage:
;;      r0 - Address for return value = 0x10(sp)
;;      r1 - Exception information
;;      r2 - Original arg1.low
;;      r3 - Original arg1.high
;;
;;  Stack Usage:
;;      0x14(sp): Return result.high
;;      0x10(sp): Return result.low
;;      0xC(sp): Default result.high
;;      0x8(sp): Default result.low
;;      0x4(sp): Original arg2.high
;;      0x0(sp): Original arg2.low

	CALL    FPE_Raise             ; Deal with exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF

        LDR     r0, [sp, #0x10]       ; Load up returned result
        LDR     r1, [sp, #0x14]       ;  ...
        ADD     sp, sp, #0x8          ; Restore extra arg passing space


done
    ADD     sp, sp, #0x10             ; Pop off original args
  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {r4-r10, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {r4-r10, pc}
  ENDIF
	                                  ; Restore off non-volatiles and return



;%%%%%%%%%%%%%%%%%%%%%%%%%
;%  Exceptional process  %
;%%%%%%%%%%%%%%%%%%%%%%%%%

; Exception 1: parameter1 is non-finite (exponent1 == 2047).  The mantissa has
; not been shifted left for the guard bits yet.  The choice of ARM SNaN
; versus QNaN (mantissa<51> = 1 => QNaN) means that abs(<any QNaN>) >
; abs(<any SNaN>) > abs(<any inf>).
; 
; exception1:
;   if (mantissa1 == 0)
;     CheckArg2INF();     // Arg1 is an INF.  Must check Arg2 for INF.
;   else if (mantissa1[MSb] == 0)
;     SignalInvalid();    // Arg1 is an SNaN so signal invalid and return it.
;   else
;     CheckArg2SNaN();    // Arg1 is a QNaN.  Check Arg2 for SNaN.
;
; CheckArg2SNaN:
;   if (exponent2 == 2047 &&
;       mantissa2 != 0 &&
;       mantissa2[MSb] == 0)
;     SignalInvalid();
;   else
;     ReturnQNaN();
;
; CheckArg2INF:
;   if (exponent2 == 2047 &&
;       mantissa2 == 0)
;     if (sign1 ^ sign2)
;       SignalInvalid();  // Arg1 and Arg2 are opposite INFs.
;     else
;       ReturnINF();      // Arg1 and Arg2 are same signed INFs.
;   else
;     ReturnINF();        // Arg1 is INF.  Arg2 is not.
;
; SignalInvalid:
;   cause |= INVALID_OPERATION;
;   ReturnQNaN();
;
; ReturnQNaN:
;   exponent1 = 2047;
;   mantissa1[MSb] = 1;
;   return();
;
; ReturnINF
;   exponent1 = 2047;
;   mantissa1 = 0;
;   return();
;
exception1
	ORRS    r3, r8, r0      ; if (mantissa1 == 0)
    BEQ     CheckArg2INF    ;   CheckArg2INF
    TST     r8, #dSignalBit ; else if (mantissa1[MSb] == 0)
    BEQ     SignalInvalid   ;   SignalInvalid
                            ; else
                            ;   CheckArg2SNaN
CheckArg2SNaN
    ADD     r3, r1, #1      ; if (exponent2 == 2047 &&
    CMP     r3, #2048       ;   ..
    BNE     ReturnQNaN      ;   ..
    ORRS    r3, r2, r4      ;     mantissa2 != 0 &&
    BEQ     ReturnQNaN      ;   ..
    TST     r2, #dSignalBit ;     mantissa2[MSb] == 0)
    BEQ     SignalInvalid   ;   SignalInvalid
    B       ReturnQNaN      ; else
                            ;   ReturnQNaN
CheckArg2INF
    ADD     r3, r1, #1      ; if (exponent2 == 2047 &&
    CMP     r3, #2048       ;   ..
    BNE     ReturnINF       ;   ..
    ORRS    r3, r2, r4      ;     mantissa2 == 0 &&
    BNE     ReturnINF       ;   ..
    EORS    r3, r10, r6     ;   if (sign1 ^ sign2)
    BMI     SignalInvalid   ;     SignalInvalid
                            ; else
                            ;   ReturnINF

ReturnINF
    AND     r1, r10, #0x80000000  ; Get sign bit
    ORR     r1, r1, r9, LSL #20   ; Insert exponent (exponent == 2047)
    B       return                ; r0 is already 0 so just return

SignalInvalid
    ORR     r5, r5, #IVO_bit      ; Set invalid operation

ReturnQNaN
    AND     r1, r10, #0x80000000  ; Get sign bit
    ORR     r1, r1, r9, LSL #20   ; Insert exponent (exponent == 2047)
    ORR     r1, r1, #dSignalBit   ; Insert mantissa high bit to ensure QNaN
    ORR     r1, r1, r8            ; OR in rest of high mantissa bits
    B       return                ; r0 already has the low mantissa bits so
                                  ;   just return


; Exception 2: parameter1 is finite, parameter2 is not normal (0 or denormal).
;
; if (exponent1 == 0)                   // parameter1 is not normal
;     if (mantissa1 == 0)               // parameter1 is 0
;         return properly signed 0
;     else if (mantissa2 == 0)          // denormal+denormal
;         go normalize both and add
;     else                              // denormal+0
;         return parameter1
; else if (mantissa != 0)               // parameter2 is denormal
;     go normalize parameter2 and add
; else                                  // parameter2 is 0
;     return parameter1

exception2
    CMP     r9, #0          ; if parameter1 is not normal
    BNE     p1_normal       ;   ..
    ORRS    r7, r8, r0      ;   if parameter1 is 0
    BNE     p1_denormal     ;     ..
;*** Rounding mode: proper sign is a function of the rounding mode.
    AND     r10, r10, r6    ;     return properly signed 0
    B       return_value    ;

p1_denormal
    ORRS    r7, r2, r4      ;   else if parameter2 is denormal
    BNE     p1_normalize    ;     go normalize both and add
    B       return_p1       ;   else parameter2 is 0
                            ;     return parameter1
p1_normal                   ; (parameter2 is denormal or 0)
    ORRS    r7, r2, r4      ; else if parameter2 is denormal
    BNE     p2_normalize    ;   go normalize parameter2 and add
return_p1                   ; else parameter2 is 0
    MOV     r8, r8, LSL #3  ;   return parameter1
    ORR     r8, r8, r0, LSR #29
                            ;   ..
    MOV     r0, r0, LSL #3  ;   ..
    B       return_value    ;   ..

; Both parameter1 and parameter2 are denormal.  Normalize both then go add.

p1_normalize                ; Stop when we shift into 1.0 bit
    MOVS    r0, r0, LSL #1  ; Account for the hidden mantissa bit
    MOV     r8, r8, LSL #1  ;   that denormals don't have
    ORRCS   r8, r8, #1      ;   ..
    CMP     r8, #NORMAL     ; While mantissa1 < 1.0
    BGE     end_p1_norm     ;   ..
p1_norm_loop
    MOVS    r0, r0, LSL #1  ;   Scale mantissa1 up by 1 place
    MOV     r8, r8, LSL #1  ;     ..
    ORRCS   r8, r8, #1      ;   ..
    SUB     r9, r9, #1      ;     and exponent1 down by 1
    CMP     r8, #NORMAL     ;   ..
    BLT     p1_norm_loop    ;   ..
end_p1_norm

; parameter1 is (now) normalized, parameter2 is denormal.  Normalize
; parameter2 then go add.

p2_normalize                ; Stop when we shift into 1.0 bit
    MOVS    r4, r4, LSL #1  ; Account for the hidden mantissa bit
    MOV     r2, r2, LSL #1  ;   that denormals don't have
    ORRCS   r2, r2, #1      ;   ..
    CMP     r2, #NORMAL     ; While mantissa2 < 1.0
    BGE     end_p2_norm     ;   ..
p2_norm_loop
    MOVS    r4, r4, LSL #1  ;   Scale mantissa2 up by 1 place
    MOV     r2, r2, LSL #1  ;     ..
    ORRCS   r2, r2, #1      ;   ..
    SUB     r1, r1, #1      ;     and exponent2 down by 1
    CMP     r2, #NORMAL     ;   ..
    BLT     p2_norm_loop    ;   ..
end_p2_norm
    B       exception_return2
                            ; Done

    END
