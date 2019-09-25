;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; normal.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

;===========================================================================
;Veneers onto the arith.s functions.
;
;This block should be assembled multiple times, once for each function.
;The possible functions are:
;
;       normalise_s     Normalisation functions

        GBLL    SinglePrecision
        GBLL    DoublePrecision
        GBLL    ExtendPrecision

        GET     fpe.asm

;===========================================================================

        [ :DEF: thumb
        CODE32
        ]

	AREA   |.text|, CODE, READONLY

        EXPORT  __fp_normalise_op1
        EXPORT  __fp_normalise_op2
        EXPORT  __fp_normalise_op1neg
        EXPORT  __fp_norm_denorm_op1
        EXPORT  __fp_norm_denorm_op2

        GBLL    normalise_s

SinglePrecision SETL    {FALSE}
DoublePrecision SETL    {FALSE}
ExtendPrecision SETL    {FALSE}
normalise_s     SETL    {TRUE}

;===========================================================================

        GET     arith.asm

        END
