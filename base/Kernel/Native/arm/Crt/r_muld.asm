;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

	GBLL mul_s

	GET veneer_d.asm

	END


;;;;  THE BELOW ROUTINE SHOULD WORK, BUT THE ARM ROUTINES SHOULD BE FASTER.


;
; Translated to ARM from SH3 FP emulation routines.
;
; __muld  Double precision floating point multiplication.
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

    Export   __muld

    IMPORT   FPE_Raise

    AREA |.text|, CODE, READONLY


CARRY_CHECK EQU 0x01000000
MSB         EQU 0x00100000


__muld

    STMFD   sp!, {r0-r9, lr} ; Save off args and non-volatiles and lr

    MOV     r8, r1          ; Load parameter1 as R8 R0
    MOV     r4, r2          ; Load parameter2 as R2 R4
    MOV     r2, r3          ;   ...
    MOV     r5, #_FpMulD    ; Double multiply, assume no exceptions


; Unpack parameters.
;
; R8 R0:   mantissa1            R2 R4:   mantissa2
; R9:      exponent1            R1:      exponent2
; R7:      sign = sign1 XOR sign2
;
; R5:      Exception flags

    MOV     r9, r8, LSL #1     ; Extract exponent1
    MOV     r9, r9, LSR #21    ;   ...
    MOV     r1, r2, LSL #1     ; Extract exponent2
    MOV     r1, r1, LSR #21    ;   ...
    MVN     r3, #0             ; Set up to extract mantissas
    EOR     r7, r8, r2         ; Compute sign of result
    AND     r8, r8, r3, LSR #12; Extract mantissa1
    AND     r2, r2, r3, LSR #12; Extract mantissa2


; Check for exceptional cases.  All NaNs, infinities, and 0's are eliminated.
; Denormal numbers return here after normalizing them.  After these checks,
; both parameters are normalized numbers.
;
; if (exponent1 == 2047)
;     exception1; parameter1 is nonfinite
; if (exponent2 == 2047)
;     exception2; parameter1 is finite, parameter2 is nonfinite
; if (exponent1 ==    0)
;     exception3; parameter1 is 0 or denormal, parameter2 is finite
; if (exponent2 ==    0)
;     exception4; parameter1 is normalized, parameter2 is 0 or denormal

    ADD     r3, r9, #1      ; if (exponent1==2047)
    CMP     r3, #2048       ;   ..
    BEQ     exception1      ;   exception1

    ADD     r3, r1, #1      ; if (exponent2==2047)
    CMP     r3, #2048       ;   ..
    BEQ     exception2      ;   exception2

    CMP     r9, #0          ; if (exponent1==0)
    BEQ     exception3      ;   exception3
exception_return3

    CMP     r1, #0          ; if (exponent2==0)
    BEQ     exception4      ;   exception4
exception_return4

; Multiply the 53-bit mantissa1 and mantissa2 to produce a 106-bit product.
;
; Mantissas:
;
;  63       53   51                 32 31                                0
;  31       21   19                  0 31                                0
; +-----------+-+---------------------+-----------------------------------+
; |<--- 0 --->|1|      m1h, m2h       |             m1l, m2l              |
; +-----------+-+---------------------+-----------------------------------+
;               ^ Binary point
;
; Partial product terms:
;
;                                     m1l*m2l.h       m1l*m2l.l
;                     m1h*m2l.h < C + m1h*m2l.l
;                   + m1l*m2h.h < C + m1l*m2h.l
;   + m1h*m2h.h < C + m1h*m2h.l
;   -----------     -----------     -----------     -----------
;          res3            res2            res1            res0
;
; Intermediate result:
;
;  127                106 104 103   96 95       64 63       32 31        0
;  31                  10 9 8 7      0 31        0 31        0 31        0
; +----------------------+-+-+--------+----/\/----+----/\/----+----/\/----+
; |<-------- 0 --------->|?|?|R3: res3|  R8: res2 |  R0: res1 |  R6: res0 |
; +----------------------+-+-+--------+----/\/----+----/\/----+----/\/----+
;                            ^ Binary point

    ADD     r9, r9, r1      ; Compute exponent of result ...

    UMULL   r6, r1, r0, r4  ; Compute m1l * m2l
                            ;   r6 = m1l*m2l.l, res0
                            ;   r1 = m1l*m2l.h

    ORR     r8, r8, #MSB    ; Set mantissa1's hidden bit
    ORR     r2, r2, #MSB    ; Set mantissa2's hidden bit

    UMULL   r4, r3, r8,r4   ; Compute m1h * m2l
                            ;   r4 = m1h*m2l.l
                            ;   r3 = m1h*m2l.h

    ADDS    r4, r1, r4      ; Add 1st 2 terms of res1

    SUB     r9, r9, #0x400  ;   ... compute exponent of result
    ADD     r9, r9, #0x1    ;   ... compute exponent of result

    UMULL   r0, r1, r2, r0  ; Compute m1l * m2h
                            ;   r0 = m1l*m2h.l
                            ;   r1 = m1l*m2h.h

    ADCS    r1, r1, r3      ; Add 1st 2 terms of res2, no carry out
    ADCS    r0, r0, r4      ; Add 3rd term of res1, no carry in

    UMULL   r8, r3, r2, r8  ; Compute m1h * m2h
                            ;   r8 = m1h*m2h.l
                            ;   r3 = m1h*m2h.h

    ADCS    r8, r8, r1      ; Add 3rd term of res2
    ADC     r3, r3, #0      ; Add res2's carry to res3


; Shift the intermediate result right 17 bits, and 1 more if the product took
; 2 bits to the left of the binary point.  Fold all dropped bits from the right
; into the sticky bit S.  This leaves the result in standardized form for
; rounding.
;
; Result:
;  63     56   54                   32 31                            3 2 0
;  31     24   22                    0 31                            3 2 0
; +---------+-+-----------------------+-----------------------------------+
; |<-- 0 -->|1|         R8            |               R0             L|GRS|
; +---------+-+-----------------------+-----------------------------------+
;             ^ Binary point

normalize
    CMP     r6, #0              ; Fold bits we're about to lose into a
    ORRNE   r0, r0, #1          ;   sticky bit
    MOV     r6, r6, LSR #17     ; Shift intermediate result right 17
    ORR     r6, r6, r0, LSL #15 ;   ..
    MOV     r0, r0, LSR #17     ;   ..
    ORR     r0, r0, r8, LSL #15 ;   ..
    MOV     r8, r8, LSR #17     ;   ..
    ORR     r8, r8, r3, LSL #15 ;   ..
    TST     r8, #CARRY_CHECK    ; If product has 2 bits to the left of the
    BEQ     end_normalize       ;   binary point
    MOVS    r8, r8, LSR #1      ; Then normalize by scaling right 1
    MOVS    r0, r0, RRX         ;   more bit
    MOV     r6, r6, RRX         ;   ..
    ADD     r9, r9, #1          ;   ..
end_normalize

; There are still 17 or 18 guard bits on the left of R6 that need to be folded
; into the sticky bit S.  It's safe to check the right ones over again because
; we're only concerned with stickiness.

    CMP     r6,#0              ; If any guard bits below S are set
    ORRNE   r0, r0, #1         ;   fold them into S

; Denormalize the result if necessary, with no concern for performance.

    CMP     r9, #0             ; If exponent <= 0
    BGT     end_denormal       ;   ..
    RSB     r9, r9, #0         ; Then shift right exponent1 places
    ADD     r9, r9, #1         ;   +1 for the non-hidden bit
denormal_loop
    MOVS    r8, r8, LSR #1     ;   ..
    MOVS    r0, r0, RRX        ;   ..
    ORRCS   r0, r0, #1         ;   Fold the lost bit into the sticky bit
    SUBS    r9, r9, #1         ;   ..
    BNE     denormal_loop      ;   ..
end_denormal

; Round to nearest.  If rounding occurs, set inexact and
; mantissa += G & ( L | R | S ).  If the rounding carries, then renormalize.

; Test for inexact.
    TST     r0, #0x7           ; If G|R|S (=> rounding required)
    BEQ     end_round          ;   ..
    ORR     r5, r5, #INX_bit   ;   result is inexact

; Round to nearest.
    TST     r0, #0x4           ; If G &&
    BEQ     end_round          ;   ..
    TST     r0, #0xB           ;   L|R|S
    BEQ     end_round          ;     ..
    ADDS    r0, r0, #0x8       ; Then round the mantissa up
    ADC     r8, r8, #0         ;   ..

    CMP     r8, #CARRY_CHECK   ;   If the rounding carried
    BLT     no_normal_carry    ;     (mantissa >= 0x01000000)
    
    MOVS    r8, r8, LSR #1     ;   Then renormalize
    MOV     r0, r0, RRX        ;     ..
    ADD     r9, r9, #1         ;     ..
    B       end_round          ;     ..

no_normal_carry
    CMP     r9, #0             ;   Else if (exponent == 0)
    BNE     end_round          ;     ..
    CMP     r8, #CARRY_CHECK>>1;     && (mantissa >= 0x00800000)
    MOVGE   r9, #1             ;   Then rounded MaxDenorm to MinNormal

end_round

; Test for overflow.  Do this after rounding in case rounding caused overflow.
    ADD     r3, r9, #1         ; If (exponent >= 2047)
    CMP     r3, #2048          ;   ..
    BGE     return_overflow    ;   return overflow exception

; Test tininess after rounding.
    TST     r5, #INX_bit        ; If already inexact
    BEQ     end_check_underflow1;  ..
    CMP     r9, #0              ;   and if exponent = 0
    ORREQ   r5, r5, #UNF_bit    ;     result has underflowed too
end_check_underflow1

; Pack the result back into IEEE format.

return_value

    MOV     r0, r0, LSR #3      ; Shift mantissa right 3 to remove GRS
    ORR     r0, r0, r8, LSL #29 ;   ..
    MOV     r8, r8, LSR #3      ;   ..
    MVN     r3, #0              ; Mask away the hidden bit
    AND     r8, r8, r3, LSR #12 ;   ..
    ORR     r1, r8, r9, LSL #20 ; Merge exponent and mantissa
    MOVS    r7, r7              ; Merge sign with exponent and mantissa
    ORRMI   r1, r1, #0x80000000 ;   ..

; If any trap enable flags are set corresponding to exception flags set,
; set the corresponding cause bits and cause a trap.
;
; if (exception)
;     call handler
;     extract the possibly updated result
; return

return

    TST     r5, #FPECause_mask ; If any exceptions occurred ...
    BEQ     done               ;   ..

cause_trap
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
    LDMIA   sp!, {r4-r9, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {r4-r9, pc}
  ENDIF
                                      ; Restore off non-volatiles and return


;%%%%%%%%%%%%%%%%%%%%%%%%%
;%  Exceptional process  %
;%%%%%%%%%%%%%%%%%%%%%%%%%

; Exception 1: parameter1 is non-finite (exponent1 == 2047); it's either a
; NaN or inf.  The mantissa has not been shifted left for the guard bits yet.
;
; If either parameter is an SNaN, return an invalid op exception with a QNaN.
; Otherwise, if either parameter is a QNaN, silently return a QNaN.  Otherwise,
; parameter1 is inf.  Return an invalid op exception with a QNaN for inf*0, or
; inf for inf*inf or inf*<non-0 finite>.
;
; if (mantissa1<51> == 0 &           // parameter1 is an SNaN
;     mantissa1 != 0)                //  ..
;     return invalid op exception
; else if (exponent2 == 2047 &       // parameter2 is an SNaN
;          mantissa2<51> == 0 &      //   ..
;          mantissa2 != 0)           //   ..
;     return invalid op exception
; else if (mantissa1 != 0)           // parameter1 is a QNaN
;     return QNaN
; else if (exponent2 != 2047)        // parameter2 is finite
;     if (parameter2 != 0)           // inf*<non-0 finite>
;         return inf
;     else                           // inf*0
;         return invalid op exception
;     return inf
; else if (mantissa2 != 0)           // parameter2 is a QNaN
;     return QNaN
; else                               // inf*inf
;     return inf

exception1
    ORRS    r3, r8, r0         ; if (mantissa1 !=0 &&
    BEQ     e1_p2_snan_check   ;   ..
    TST     r8, #dSignalBit    ;     mantissa1[MSb] == 0)
    BEQ     return_invalid     ;   return invalid operation

e1_p2_snan_check
    ADD     r3, r1, #1         ; else if (exponent2 == 2047 &&
    CMP     r3, #2048          ;   ..
    BNE     e1_p2_not_snan     ;   ..
    ORRS    r3, r2, r4         ;          mantissa2 != 0 &&
    BEQ     e1_p2_not_snan     ;   ..
    TST     r2, #dSignalBit    ;          mantissa2[MSb] == 0)
    MOVEQ   r8, r2             ;   copy mantissa2 to mantissa1
    MOVEQ   r0, r4             ;     ..
    BEQ     return_invalid     ;   return invalid operation

e1_p2_not_snan
    ORRS    r3, r8, r0         ; else if (mantissa1 != 0)
    BNE     return_QNaN        ;   return QNaN

e1_p1_is_INF
    ADD     r3, r1, #1         ; else if (exponent2 != 2047)
    CMP     r3, #2048          ;   ..
    BEQ     e1_p2_INF_NaN      ;   ..
    CMP     r1, #0             ;   if (parameter2 != 0)
    ORREQS  r3, r2, r4         ;     ..
    BNE     return_inf         ;     return INF
    MOV     r8, #0             ;   else
    MOV     r0, #0             ;     zero out mantissa1 for QNaN
    B       return_invalid     ;     return invalid operation

e1_p2_INF_NaN
    ORRS    r3, r2, r4         ; else if (mantissa2 != 0)
    MOV     r8, r2             ;   copy mantissa2 to mantissa1
    MOV     r0, r4             ;     ..
    BNE     return_QNaN        ;   return QNaN
    B       return_inf         ; else
                               ;   return INF


; Exception 2: parameter1 is finite.  parameter2 is non-finite (exponent2 ==
; 2047); it's either a NaN or inf.  The mantissa has not been shifted left
; for the guard bits yet.
;
; If parameter2 is an SNaN, return an invalid op exception with a QNaN.
; Otherwise, if it's a QNaN, silently return a QNaN.  Otherwise it's finite*inf
; so return an invalid op exception with a QNaN for 0*inf, or
; <non-0 finite>*inf.
;
; if (mantissa2 != 0 &
;     mantissa2<51> == 1)       // parameter2 is an SNaN
;     return invalid op exception
; else if (mantissa2 != 0)      // parameter2 is a QNaN
;     return QNaN
; else if (parameter1 != 0)     // parameter1 is non-0 finite
;     return inf
; else                          // it's 0*inf
;     return invalid op exception

exception2
    ORRS    r3, r2, r4      ; if (mantissa2 != 0 &&
    BEQ     e2_p2_is_inf    ;   ..
    TST     r2, #dSignalBit ;     mantissa2[MSb] == 0)
    BEQ     return_invalid  ;   return invalid operation
    MOV     r8, r2          ; else if (mantissa2 != 0)
    MOV     r0, r4          ;   copy mantissa2 into mantissa1 for QNaN
    B       return_QNaN     ;   return QNaN

e2_p2_is_inf
    ORRS    r3, r8, r0      ; else if (parameter1 != 0)
    CMPEQ   r9, #0          ;   ..
    MOVEQ   r8, r2          ; copy mantissa2 to mantissa1 for QNaN
    MOVEQ   r0, r4          ; ..
    BEQ     return_invalid  ; ..
    B       return_inf      ;   return INF



; Exception 3: parameter1 is 0 or denormal (exponent1 = 0), parameter2 is
; finite.
;
; if (mantissa1 == 0)
;     return zero
; else normalize parameter1

exception3
    ORRS    r3, r8, r0      ; if (mantissa1 == 0)
    BEQ     return_zero     ;   return zero
p1_norm                     ; Normalize parameter1 stop when shift into 1.0 bit
    MOVS    r0, r0, LSL #1  ; Account for the hidden mantissa bit
    MOV     r8, r8, LSL #1  ;   that denormals don't have
    ORRCS   r8, r8, #0x1    ;   ..
    CMP     r8, #MSB        ; While mantissa1 < 1.0
    BGE     end_p1_norm     ;   ..
p1_norm_loop
    MOVS    r0, r0, LSL #1  ;   Scale mantissa1 up by 1 place
    MOV     r8, r8, LSL #1  ;     ..
    ORRCS   r8, r8, #0x1    ;     ..
    SUB     r9, r9, #1      ;   and exponent1 down by 1
    CMP     r8, #MSB        ;
    BLT     p1_norm_loop    ;
end_p1_norm
    B       exception_return3
                            ; Done


; Exception 4: parameter1 is finite and (now) normalized, parameter2 is 0 or
; denormal (exponent2 = 0).
;
; if (mantissa2 == 0)
;     return zero
; else normalize parameter2
exception4
    ORRS    r3, r2, r4      ; if (mantissa2 == 0)
    BEQ     return_zero     ;   return zero
p2_norm                     ; Normalize parameter2 stop when shift into 1.0 bit
    MOVS    r4, r4, LSL #1  ; Account for the hidden mantissa bit
    MOV     r2, r2, LSL #1  ;   that denormals don't have
    ORRCS   r2, r2, #0x1    ;   ..
    CMP     r2, #MSB        ; While mantissa2 < 1.0
    BGE     end_p2_norm     ;   ..
p2_norm_loop
    MOVS    r4, r4, LSL #1  ;   Scale mantissa2 up by 1 place
    MOV     r2, r2, LSL #1  ;     ..
    ORRCS   r2, r2, #0x1    ;     ..
    SUB     r1, r1, #1      ;   and exponent2 down by 1
    CMP     r2, #MSB        ;
    BLT     p2_norm_loop    ;
end_p2_norm
    B       exception_return4
                            ; Done



; Cause an overflow exception (=> inexact) and return properly signed inf.
return_overflow
    ORR     r5, r5, #OVF_bit :OR: INX_bit
                            ; Report overflow (=> inexact)
                            ; Fall thru to return inf

; Return properly signed inf.
return_inf
    MVN     r9, #0          ; exponent1 = 2047
    MOV     r9, r9, LSR #21 ;   ..
    MOV     r8, #0          ; mantissa1 = 0
    MOV     r0, #0          ;   ..
    B       return_value


; Return 0.
return_zero
    MOV     r1, r7, LSR #31 ; Apply the sign to zero
    MOV     r1, r1, LSL #31 ;   ..
    MOV     r0, #0          ; Zero low mantissa
    B       return          ; Done

; Cause an invalid operation exception and return a QNaN.
return_invalid
    ORR     r5, r5, #IVO_bit; Report invalid op exception
                            ; Fall thru to return a QNaN

; Return a QNaN.
return_QNaN
    ORR     r1, r8, #0x7F000000
                            ; Return a QNaN
    ORR     r1, r1, #0x00F80000
                            ;  ..
    B       return          ;  ..

    END
