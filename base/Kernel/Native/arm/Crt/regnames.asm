;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; Assembler source for FPA support code and emulator
; ==================================================
; Register allocations. Also used by "fplib".

; Register usage at top level in undefined instruction handler.

Rsp     RN      R13     ;Our stack pointer
Rfp     RN      R12     ;Our "frame pointer" - points to ARM register dump
Rins    RN      R11     ;Offending instruction itself
Rwp     RN      R10     ;The workspace pointer/an entry sequence temporary
Rtmp2   RN      R9      ;A temporary
Rtmp    RN      R8      ;A temporary

; Register usage in the arithmetic and rounding routines, and the Prepare
; and Round stage exception routines. Rfpsr, Rins, Rwp, Rfp and Rsp are
; also part of this interface.

OP1sue  RN      R1      ;The sign, uncommon bit and (sometimes) exponent of
                        ; the first or only operand
OP1mhi  RN      R0      ;The mantissa of the first or only operand - high
                        ; word
OP1mlo  RN      R2      ;The mantissa of the first or only operand - low
                        ; word
RNDexp  RN      R3      ;The exponent of the number being rounded
OP2sue  RN      R3      ;The sign, uncommon bit and (sometimes) exponent of
                        ; the second operand
RNDdir  RN      R4      ;Direction number has already been rounded (0 = exact,
                        ; positive = rounded up, negative = rounded down)
OP2mhi  RN      R5      ;The mantissa of the second operand - high word
RNDprm  RN      R5      ;Precision and rounding mode for rounding, as two
                        ; adjacent 2 bit fields, lower one at position RM_pos
                        ; within word, higher one at RM_pos+2.
OP2mlo  RN      R4      ;The mantissa of the second operand - low word
Rarith  RN      R6      ;A temporary
Rfpsr   RN      R7      ;FPSR contents

; Two more temporaries, used when accessing ARM registers. The requirements
; are (a) that they are not equal to any of the result registers (OP1sue,
; OP1mhi, OP1mlo and Rarith); (b) that they are not equal to Rfpsr, Rins,
; Rwp, Rfp or Rsp; (c) that they are not banked registers; (d) that they
; are not equal to RNDprm.

Rregno  RN      R3
Rregval RN      R4

        ASSERT  Rregno <> OP1sue
        ASSERT  Rregno <> OP1mhi
        ASSERT  Rregno <> OP1mlo
        ASSERT  Rregno <> Rfpsr
        ASSERT  Rregno <> Rins
        ASSERT  Rregno <> Rwp
        ASSERT  Rregno <> Rfp
        ASSERT  Rregno <> Rsp
        ASSERT  Rregno < R8
        ASSERT  Rregno <> RNDprm

        ASSERT  Rregval <> OP1sue
        ASSERT  Rregval <> OP1mhi
        ASSERT  Rregval <> OP1mlo
        ASSERT  Rregval <> Rfpsr
        ASSERT  Rregval <> Rins
        ASSERT  Rregval <> Rwp
        ASSERT  Rregval <> Rfp
        ASSERT  Rregval <> Rsp
        ASSERT  Rregval < R8
        ASSERT  Rregval <> RNDprm

        ASSERT  Rregno <> Rregval

; Some commonly used register lists:

OP1regs RLIST   {OP1mhi,OP1sue,OP1mlo}
;        ASSERT  OP1sue < OP1mhi
        ASSERT  OP1mhi < OP1mlo

OP2regs RLIST   {OP2sue,OP2mlo,OP2mhi}
        ASSERT  OP2sue < OP2mhi
;        ASSERT  OP2mhi < OP2mlo

        END
