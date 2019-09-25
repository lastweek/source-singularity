;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; basic_d.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

; Basic floating point functions
;
;
; Revisions:
;   Fixed == and != compares to be IEEE-754 compliant when input QNaNs.
;     No exceptions are raised when only QNaNs are the only NaNs input to
;     == and !=.  Moved NaN detection and exception raising here.
;   Removed unnecessary macros for compares that return results in flags.
;   Added WindowsCE SEH mechanism support.
;   Renamed routines.
;

; Local storage size and offsets
LOC_SIZE    EQU   0x20
OrgOp2h     EQU   0x1C
OrgOp2l     EQU   0x18
OrgOp1h     EQU   0x14
OrgOp1l     EQU   0x10
ExDResl     EQU   0x08
ExOp2h      EQU   0x04
ExOp2l      EQU   0x00
NewResl     EQU   0x10


        GET     fpe.asm
        GET     kxarm.inc

;==============================================================================
; Compare
;
; BUGBUG: This documentation is not completely correct.  For == and !=
;         comparisions, only SNANs can raise the invalid operation
;         exception.  For all other compares, both SNANs and QNANs
;         can raise the invalid operation exception and return FALSE
;         (they actually compare unordered).  When == compares unordered
;         (contains 1 or more NANs) it also returns FALSE.  When !=
;         compares unordered, it returns TRUE.  See IEEE-754-1985 for
;         details.  The described behavior is implemented here.
;
;
;
; This isn't as simple as it could be. The problem is that NaNs may cause an
; exception and always compare as FALSE if not signalling. Infinities need to
; be treated as normal numbers, although they look like NaNs.
; Furthermore +0 = -0 needs a special check.
;
; General comparison instruction flow: (this is less than)
;
;                              OP1 < 0 OR OP2 < 0
;                                       |
;               +--------Y--------------+------------N-------------+
;               |                                                  |
;       (OP1 OR OP2) NaN?                                   (OP1 OR OP2) NaN?
;               |                                                  |
;      +----N---+---Y------+                         +-----Y-------+----N-----+
;      |                   |                         |                        |
; RET OP1 < OP2      OP1 or OP2 inf/NaN?     OP1 or OP2 inf/NaN?       RET OP1 > OP2
;                            |                       |                     AND NOT 
;                     +---N--+---Y--+         +---Y--+--N----+        (OP1 = 0 AND OP2 = 0)
;                     |             |         |              |            
;              RET OP1 < OP2   (OP1 NaN?) OR (OP2 NaN?)  RET OP1 > OP2 
;                     |                   |                  |
;                     |             +--N--+--Y--> exception  |
;                     |             |                        |
;                     |     OP1 < 0 OR OP2 < 0?              |
;                     |             |                        |
;                     +-----N-------+------------Y-----------+
;
; The first layer selects between the case where both operands are positive or
; when at least one is negative. The second layer uses a quick test on the
; operands orred together to determine whether they look like a NaN. This check is
; weak: it will get about 4% or 9% 'false hits' for doubles and floats, where 
; none of the operands is a NaN. In general false hits occur for very large numbers,
; or for both numbers around 2.0 (one larger, one smaller).  
; If the operands are not categorized a NaNs, a normal unsigned compare does the
; actual work. It returns immediately if the highwords of the operands are different.
; Note that the negative case uses a compare with the operands swapped,
; as the order is reversed for negative numbers. The negative case also checks for
; -0 == 0 as a special case. In the NaN code, a more precise check is done, which
; filters out NaNs and infinities, and the normal compare follows otherwise.
; The exception handler raises a Invalid Operation exception if one of the operands
; is a NaN (ignoring the signal bit).
; There are thus 3 different checks on NaNs, with increasing accuracy: 
; 1. one of the operands looks like a NaN (but might not be one). 
; 2. one of the operands is infinite or NaN. 
; 3. one of the operands is a NaN.
;
; The compare routine can either be used as a boolean returning function (dgt, 
; dge, dlt, dle) or as a flags returning function (returning < as LO, <= as LS,
; > as HI, >= as HS). 
;
; The routine is optimised for the both operands positive which not look like
; NaNs case. It is also assumed the chance that the highwords of the operands are 
; equal is less than 50%. Timing:
; Flags: 7/9 (pos), 11/13 (false NaN), 10/12 (neg), 13/15 (false NaN) SA1.1 cycles.
; EQ/NE/HI/HS/LO/LS: 10 / 14 / 13 / 16
;==============================================================================

        MACRO
        CmpReturn $cc
            MOV     a1, #0
            MOV$cc  a1, #1
            ADD     sp, sp, #LOC_SIZE
  IF Interworking :LOR: Thumbing
            LDMFD   sp!, {lr}
            BX      lr
  ELSE
            LDMFD   sp!, {pc}
  ENDIF
        MEND



        MACRO
$lab    DoubleCompare $cc, $NaN_lab

        ASSERT "$cc"="LO":LOR:"$cc"="LS":LOR:"$cc"="HS":LOR:"$cc"="HI":LOR:"$cc"="EQ":LOR:"$cc"="NE"
 
    NESTED_ENTRY $lab
        EnterWithLR_16
        STMFD   sp!, {lr}                   ; Save return address
        SUB     sp, sp, #LOC_SIZE           ; Allocate local storage
    PROLOG_END

        ORRS    tmp, dOP1h, dOP2h
        BMI     $lab._negative              ; one of the operands negative? (MI)
        CMN     tmp, #0x00100000            ; check whether operands might be infinite/NaN
        BMI     $lab._check_NaN_pos
        CMP     dOP1h, dOP2h
        CMPEQ   dOP1l, dOP2l
        CmpReturn $cc

$lab._check_NaN_pos                         ; opnd1/2 might be inf/NaNs - do more accurate check
        CMN     dOP1h, #0x00100000          ; overhead 4 cycles for false hit
        CMNPL   dOP2h, #0x00100000
        BMI     $lab._Inf_or_NaN
$lab._cmp_pos
        CMP     dOP1h, dOP2h
        CMPEQ   dOP1l, dOP2l
        CmpReturn $cc

$lab._negative
        CMN     tmp, #0x00100000  
        BPL     $lab._check_NaN_neg         ; check whether operands might be infinite/NaN
        ORRS    tmp, dOP1l, dOP1h, LSL #1   ; check for -0 == 0
        ORREQS  tmp, dOP2l, dOP2h, LSL #1
        CMPNE   dOP2h, dOP1h
        CMPEQ   dOP2l, dOP1l
        CmpReturn $cc

$lab._check_NaN_neg                         ; opnd1/2 might be inf/NaNs - do more accurate check
        MOV     tmp, #0x00200000            ; overhead 3 cycles for false hit    
        CMN     tmp, dOP1h, LSL #1
        CMNCC   tmp, dOP2h, LSL #1
        BCS     $lab._Inf_or_NaN
$lab._cmp_neg                               ; -0 == 0 test omitted (cannot give a false hit)
        CMP     dOP2h, dOP1h
        CMPEQ   dOP2l, dOP1l
        CmpReturn $cc

$lab._Inf_or_NaN                            ; one of the operands is infinite or NaN
        MOV     tmp, #0x00200000
        CMN     tmp, dOP1h, LSL #1
        CMPEQ   dOP1l, #0                   ; HI -> NaN found
        CMNLS   tmp, dOP2h, LSL #1          ; no NaN, check opnd2          
        CMPEQ   dOP2l, #0
        BHI     $NaN_lab                    ; NaN found -> exception
        ORRS    tmp, dOP1h, dOP2h
        BPL     $lab._cmp_pos
        B       $lab._cmp_neg

        MEND








;==============================================================================
;Invalid Operation checking (NaNs on compares)
;;

  
    IMPORT FPE_Raise
  
  
;;
;; NANs on compares <, >, <=, and >=
;;
;; SNANs and QNANs both raise the invalid operation exception, so we don't
;; care which kind of NAN we get.  This is because if we get an SNAN or SNANs,
;; we raise the invalid operation exception.  If we get a QNAN or QNANs, we
;; have an unordered compare and must also raise the invalid operation
;; exception.
;;
;;  Register usage on entry:
;;  r0 - Arg1.low
;;  r1 - Arg1.high
;;  r2 - Arg2.low
;;  r3 - Arg2.high
;;  r14 - available for scratch
;;  All others have normal usage semantics.
;;
    MACRO
$l  DCmpNaN $Filter_lab
$l  STR     r2, [sp, #ExOp2l]             ;; Push Arg2.low
    STR     r3, [sp, #ExOp2h]             ;; Push Arg2.high
    MOV     r3, #_FpCompareUnordered      ;; Load default result
    STR     r3, [sp, #ExDResl]            ;; Push default result
    MOV     r3, r1                        ;; Arg1.high
    MOV     r2, r0                        ;; Arg1.low
    MOV     r1, #_FpCmpD                  ;; ExInfo: InvalidOp, double compare
    ORR     r1, r1, #IVO_bit              ;;   ..
    ADD     r0, sp, #NewResl              ;; Pointer to result

    CALL    FPE_Raise                     ;; Deal with exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
    LDR     r0, [sp, #NewResl]            ;; Load return value
    ADD     sp, sp, #LOC_SIZE             ;; Restore stack

;;
;; Register usage:
;;
;;  r0 - Result from exception handler
;;
;; We must now examine the result from the exception handler and change it
;; to TRUE or FALSE, depending on the operation.  After changing the result,
;; we return to the caller of the FP double compare routine.
;;
    B       $Filter_lab
    MEND





;;
;; NANs on compares == and !=
;;
;; SNANs and QNANs are treated differently for == and !=.  If we get an SNAN
;; or SNANs, we must raise the invalid operation exception.  If we only have
;; a QNAN or QNANs, then we simply return false and true for == and !=,
;; respectively.  Unordered comparisions for == and != do not raise the
;; invalid operation exception.
;;
;;  Register usage on entry:
;;  r0 - Arg1.low
;;  r1 - Arg1.high
;;  r2 - Arg2.low
;;  r3 - Arg2.high
;;  r14 - available for scratch
;;  All others have normal usage semantics.
;;

    MACRO
$l  DCmpSNaN $Filter_lab
$l  MOV     r12, #0x7F0                 ;; r12 = Max exponent = 0x7FF
    ORR     r12, r12, #0x00F            ;;   ...
    MOV     r14, r1, LSL #1             ;; Extract exponent from Arg1
    MOV     r14, r14, LSR #21           ;;   ...
    CMP     r14, r12                    ;; Arg1.exponent == 0x7FF?
    BNE     $l.checkArg2                ;; Arg1 not a NaN so check Arg2
    MOV     r14, r1, LSL #14            ;; r14 = Arg1.Mantissa.High
    ORRS    r14, r14, r0                ;; Any Arg1.Mantissa bits set?
    BEQ     $l.checkArg2                ;; Arg1 not a NaN so check Arg2
    TST     r1, #dSignalBit             ;; Check if SNAN
    BEQ     $l.SNaN                     ;; If high mant. bit clear, SNaN

$l.checkArg2
    MOV     r14, r3, LSL #1             ;; Extract exponent from Arg2
    MOV     r14, r14, LSR #21           ;;   ...
    CMP     r14, r12                    ;; Arg2.exponent == 0x7FF?
    BNE     $l.cmpUnordered             ;; Arg2 not a NaN so Arg1 is a QNaN
    MOV     r14, r3, LSL #12            ;; r14 = Arg2.Mantissa.High
    ORRS    r14, r14, r2                ;; Any Arg2.Mantissa bits set?
    BEQ     $l.cmpUnordered             ;; Arg2 not a NaN so Arg1 is a QNaN
    TST     r3, #dSignalBit             ;; Check if SNAN
    BEQ     $l.SNaN                     ;; If high mant. bit clear, SNaN

$l.cmpUnordered
    MOV     r0, #_FpCompareUnordered    ;; Have an unordered compare so
    B       $Filter_lab                 ;;   don't raise an exception

$l.SNaN
    STR     r2, [sp, #ExOp2l]             ;; Push Arg2.low
    STR     r3, [sp, #ExOp2h]             ;; Push Arg2.high
    MOV     r3, #_FpCompareUnordered      ;; Load default result
    STR     r3, [sp, #ExDResl]            ;; Push default result
    MOV     r3, r1                        ;; Arg1.high
    MOV     r2, r0                        ;; Arg1.low
    MOV     r1, #_FpCmpD                  ;; ExInfo: InvalidOp, double compare
    ORR     r1, r1, #IVO_bit              ;;   ..
    ADD     r0, sp, #NewResl              ;; Pointer to result
	
    CALL      FPE_Raise                     ;; Deal with exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
    LDR     r0, [sp, #NewResl]            ;; Load return value

;;
;; Register usage:
;;
;;  r0 - Result from exception handler
;;
;; We must now examine the result from the exception handler and change it
;; to TRUE or FALSE, depending on the operation.  After changing the result,
;; we return to the caller of the FP double compare routine.
;;
    B       $Filter_lab
    MEND





;==============================================================================
;Equality

        [ :DEF: eq_s
        
        Export __eqd

        AREA |.text|, CODE, READONLY

__eqd   DoubleCompare EQ, __eqd_NaN

__eqd_NaN DCmpSNaN __eqd_Filter

__eqd_Filter
        CMP     r0, #_FpCompareEqual              ;; Check if compared ==
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
        ADD     sp, sp, #LOC_SIZE                 ;; Restore stack
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __eqd
        ]

;==============================================================================
;Inequality

        [ :DEF: neq_s

        Export __ned

        AREA |.text|, CODE, READONLY

__ned   DoubleCompare NE, __ned_NaN

__ned_NaN DCmpSNaN __ned_Filter

__ned_Filter
        CMP     r0, #_FpCompareEqual              ;; Check if compared ==
        MOVEQ   r0, #0                            ;; If did, return false
        MOVNE   r0, #1                            ;;   else return true
        ADD     sp, sp, #LOC_SIZE                 ;; Restore stack
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __ned
        ]


;==============================================================================
;Less Than

        [ :DEF: ls_s

        Export __ltd

        AREA |.text|, CODE, READONLY

__ltd   DoubleCompare LO, __ltd_NaN

__ltd_NaN DCmpNaN __ltd_Filter

__ltd_Filter
        CMP     r0, #_FpCompareLess               ;; Check if compared <
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __ltd
        ]

;==============================================================================
;Less Than or Equal

        [ :DEF: leq_s

        Export __led

        AREA |.text|, CODE, READONLY

__led   DoubleCompare LS, __led_NaN

__led_NaN DCmpNaN __led_Filter

__led_Filter
        CMP     r0, #_FpCompareLess               ;; Check if compared <
        MOVEQ   r0, #1                            ;; If did,
        BEQ     __led_Filter_end                  ;;   return true
        CMP     r0, #_FpCompareEqual              ;; Check if compared ==
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
__led_Filter_end
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __led
        ]

;==============================================================================
;Greater Than

        [ :DEF: gr_s

        Export __gtd

        AREA |.text|, CODE, READONLY

__gtd   DoubleCompare HI, __gtd_NaN

__gtd_NaN DCmpNaN __gtd_Filter

__gtd_Filter
        CMP     r0, #_FpCompareGreater            ;; Check if compared >
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __gtd
        ]

;==============================================================================
;Greater Than or Equal

        [ :DEF: geq_s

        Export __ged

        AREA |.text|, CODE, READONLY

__ged   DoubleCompare HS, __ged_NaN

__ged_NaN DCmpNaN __ged_Filter

__ged_Filter
        CMP     r0, #_FpCompareGreater            ;; Check if compared >
        MOVEQ   r0, #1                            ;; If did,
        BEQ     __ged_Filter_end                  ;;   return true
        CMP     r0, #_FpCompareEqual              ;; Check if compared ==
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
__ged_Filter_end
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __ged
        ]


        END
