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
; Definitions and default values of optional optimisations. Also used by
; "fplib".
;
; Copyright (C) Advanced RISC Machines Limited, 1992-7. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

;===========================================================================

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; No Thumbing or Interworking for now.
;
         GBLL   Thumbing
Thumbing SETL   {FALSE}
         GBLL   Interworking
Interworking SETL   {FALSE}
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
        
; The "traps never return" code size optimisation.

                GBLL    TrapsCanReturn
TrapsCanReturn  SETL    {TRUE}

; The "FPE context uses 4 words per register" speed optimisation.

                GBLL    FPE4WordsPerReg
FPE4WordsPerReg SETL    {FALSE}

; The "do integer powers" optimisation.

                GBLL    DoIntegerPowers
DoIntegerPowers SETL    {TRUE}

; The value of 0^0.

                GBLS    ZeroToTheZero
ZeroToTheZero   SETS    "One"

; The "FPE checks whether next instruction is floating point" optimisation.

                GBLL    FPEChecksNextInstr
FPEChecksNextInstr SETL {TRUE}

; The "no transcendentals" optimisation.

                GBLL    NoTranscendentals
NoTranscendentals SETL  {FALSE}

; The "no packed precision" optimisation.

                GBLL    NoPacked
NoPacked        SETL    {FALSE}

;===========================================================================

        END
