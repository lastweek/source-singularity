;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; basic_f.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

; Basic floating point functions
;
;   Fixed == and != compares to be IEEE-754 compliant when input QNaNs.
;     No exceptions are raised when only QNaNs are the only NaNs input to
;     == and !=.  Moved NaN detection and exception raising here.
;   Removed unnecessary macros for compares that return results in flags.
;   Added WindowsCE SEH mechanism support.
;   Renamed routines.
;

LOC_SIZE  EQU  0x18
OrgOp1l   EQU  0x14
OrgOp2l   EQU  0x10
ExDResl   EQU  0x08
ExOp2l    EQU  0x00
NewResl   EQU  0x10


        GET     fpe.asm
        GET     kxarm.inc


;This code is very similar to the "double" versions. The documentation isn't
;extensively repeated. Refer to basic_d.s for further documentation.


;==============================================================================
; Compare.
;
; Timing:
; Flags: 7 (pos), 11 (false NaN), 9 (neg), 13 (false NaN) SA1.1 cycles
; Others: 9 / 13 / 11 / 15
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
$lab    FloatCompare $cc, $NaN_lab

        ASSERT "$cc"="LO":LOR:"$cc"="LS":LOR:"$cc"="HS":LOR:"$cc"="HI":LOR:"$cc"="EQ":LOR:"$cc"="NE"

    NESTED_ENTRY $lab
        EnterWithLR_16
        STMFD   sp!, {lr}               ; Save return address
        SUB     sp, sp, #LOC_SIZE       ; Allocate local storage
    PROLOG_END

        ORRS    tmp, fOP1, fOP2         ; separate into opnd1/2 both positive, or one negative
        BMI     $lab._negative
        CMN     tmp, #1 << 23           ; check whether operands might be infinite/NaN
        BMI     $lab._NaN_check_pos
        CMP     fOP1, fOP2
        CmpReturn $cc
        
$lab._NaN_check_pos                     ; opnd1/2 might be inf/NaNs - now do the real check
        CMN     fOP1, #1 << 23          ; these get about 9% false hits - overhead 4 cycles
        CMNPL   fOP2, #1 << 23
        BMI     $lab._Inf_or_NaN_pos
$lab._cmp_pos
        CMP     fOP1, fOP2
        CmpReturn $cc

$lab._Inf_or_NaN_pos                    ; at least one operand infinite or NaN - filter out infinities
        MOV     tmp, #1 << 24
        CMN     tmp, fOP1, LSL #1
        CMNLS   tmp, fOP2, LSL #1
        BLS     $lab._cmp_pos           ; no NaN - continue compare
        B       $NaN_lab

$lab._negative                          ; at least one negative operand
        CMN     tmp, #1 << 23
        BPL     $lab._NaN_check_neg
        MOVS    tmp, tmp, LSL #1        ; check -0 == 0 (CS & EQ -> HS and LS)
        CMPNE   fOP2, fOP1
        CmpReturn $cc

$lab._NaN_check_neg                     ; opnd1/2 might be inf/NaNs - now do the real check
        MOV     tmp, #1 << 24           ; these get about 9% false hits - overhead 4 cycles
        CMN     tmp, fOP1, LSL #1
        CMNLS   tmp, fOP2, LSL #1
        BHI     $NaN_lab
        CMP     fOP2, fOP1              ; -0 == 0 check not needed...
        CmpReturn $cc

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
;;  r0 - Arg1
;;  r1 - Arg2
;;  r14 - available for scratch
;;  All others have normal usage semantics.
;;
    MACRO
$l  FCmpNaN $Filter_lab
$l  STR     r1, [sp, #ExOp2l]             ;; Push Arg2
    MOV     r3, #_FpCompareUnordered      ;; Load default result
    STR     r3, [sp, #ExDResl]            ;; Push default result
    MOV     r2, r0                        ;; Arg1
    MOV     r1, #IVO_bit                  ;; ExInfo: InvalidOp,
    ORR     r1, r1, #_FpCmpS              ;;   float compare
    ADD     r0, sp, #NewResl              ;; Pointer to result
	
    CALL    FPE_Raise                     ;; Deal with exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
    LDR     r0, [sp, #NewResl]            ;; Load return value
    ADD     sp, sp, #LOC_SIZE             ;; Retore stack

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
;;  r0 - Arg1
;;  r1 - Arg2
;;  r14 - available for scratch
;;  All others have normal usage semantics.
;;

    MACRO
$l  FCmpSNaN $Filter_lab

$l  MOV     r14, r0, LSL #1             ;; Extract exponent from Arg1
    MOV     r14, r14, LSR #24           ;;   ...
    CMP     r14, #0xFF                  ;; Arg1.exponent == 0xFF?
    BNE     $l.checkArg2                ;; Arg1 not a NaN so check Arg2
    MOVS    r14, r0, LSL #9             ;; Arg1.Mantissa bits set?
    BEQ     $l.checkArg2                ;; Arg1 not a NaN so check Arg2
    TST     r0, #fSignalBit             ;; Check if SNAN
    BEQ     $l.SNaN                     ;; If high mant. bit clear, SNaN

$l.checkArg2
    MOV     r14, r1, LSL #1             ;; Extract exponent from Arg2
    MOV     r14, r14, LSR #24           ;;   ...
    CMP     r14, #0xFF                  ;; Arg2.exponent == 0xFF?
    BNE     $l.cmpUnordered             ;; Arg2 not a NaN so Arg1 is a QNaN
    MOVS    r14, r1, LSL #9             ;; Arg2.Mantissa bits set?
    BEQ     $l.cmpUnordered             ;; Arg2 not a NaN so Arg1 is a QNaN
    TST     r1, #fSignalBit             ;; Check if SNAN
    BEQ     $l.SNaN                     ;; If high mant. bit clear, SNaN

$l.cmpUnordered
    MOV     r0, #_FpCompareUnordered    ;; Have an unordered compare so
    B       $Filter_lab                 ;;   don't raise an exception

$l.SNaN
    STR     r1, [sp, #ExOp2l]           ;; Push Arg2
    MOV     r3, #_FpCompareUnordered    ;; Load default result
    STR     r3, [sp, #ExDResl]          ;; Push default result
    MOV     r2, r0                      ;; Arg1
    MOV     r1, #IVO_bit                ;; ExInfo: InvalidOp,
    ORR     r1, r1, #_FpCmpS            ;;   float compare
    ADD     r0, sp, #NewResl            ;; Pointer to result
	
    CALL      FPE_Raise                 ;; Deal with exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
		
    LDR     r0, [sp, #NewResl]          ;; Load return value

 
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
; Equality

        [ :DEF: eq_s

        Export __eqs

        AREA |.text|, CODE, READONLY

__eqs   FloatCompare EQ, __eqs_NaN

__eqs_NaN FCmpSNaN __eqs_Filter

__eqs_Filter
        CMP     r0, #_FpCompareEqual              ;; Check if compared ==
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
        ADD     sp, sp, #0x18                     ;; Pop extra arg passing space
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __eqs

        ]

;==============================================================================
;Inequality

        [ :DEF: neq_s

        Export __nes

        AREA |.text|, CODE, READONLY

__nes   FloatCompare NE, __nes_NaN

__nes_NaN FCmpSNaN __nes_Filter

__nes_Filter
        CMP     r0, #_FpCompareEqual              ;; Check if compared ==
        MOVEQ   r0, #0                            ;; If did, return false
        MOVNE   r0, #1                            ;;   else return true
        ADD     sp, sp, #0x18                     ;; Pop extra arg passing space
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __nes

        ]


;==============================================================================
;Less Than

        [ :DEF: ls_s

        Export __lts

        AREA |.text|, CODE, READONLY

__lts   FloatCompare LO, __lts_NaN

__lts_NaN FCmpNaN __lts_Filter

__lts_Filter
        CMP     r0, #_FpCompareLess               ;; Check if compared <
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __lts
        ]

;==============================================================================
;Less Than or Equal

        [ :DEF: leq_s

        Export __les

        AREA |.text|, CODE, READONLY

__les   FloatCompare LS, __les_NaN

__les_NaN FCmpNaN __les_Filter

__les_Filter
        CMP     r0, #_FpCompareLess               ;; Check if compared <
        MOVEQ   r0, #1                            ;; If did,
        BEQ     __les_Filter_end                  ;;   return true
        CMP     r0, #_FpCompareEqual              ;; Check if compared ==
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
__les_Filter_end
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __les

        ]

;==============================================================================
;Greater Than

        [ :DEF: gr_s

        Export __gts

        AREA |.text|, CODE, READONLY

__gts   FloatCompare HI, __gts_NaN

__gts_NaN FCmpNaN __gts_Filter

__gts_Filter
        CMP     r0, #_FpCompareGreater            ;; Check if compared >
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __gts
        ]

;==============================================================================
;Greater Than or Equal

        [ :DEF: geq_s

        Export __ges

        AREA |.text|, CODE, READONLY

__ges   FloatCompare HS, __ges_NaN

__ges_NaN FCmpNaN __ges_Filter

__ges_Filter
        CMP     r0, #_FpCompareGreater            ;; Check if compared >
        MOVEQ   r0, #1                            ;; If did,
        BEQ     __ges_Filter_end                  ;;   return true
        CMP     r0, #_FpCompareEqual              ;; Check if compared ==
        MOVEQ   r0, #1                            ;; If did, return true
        MOVNE   r0, #0                            ;;   else return false
__ges_Filter_end
  IF Interworking :LOR: Thumbing
        LDMIA   sp!, {lr}                         ;; Return
        BX      lr
  ELSE
        LDMIA   sp!, {pc}                         ;; Return
  ENDIF

    ENTRY_END __ges
        ]

;==============================================================================

        END
