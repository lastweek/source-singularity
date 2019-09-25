;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; veneer.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

;===========================================================================
;Veneers onto the arith.asm functions.
;
;This block should be assembled multiple times, once for each function.
;The possible functions are:
;
;       addsub_s        shared add and subtract
;       mul_s           shared multiply
;       div_s           shared divide

        GET     fpe.asm

        [ :DEF: thumb
        CODE32
        ]

;===========================================================================
; Veneer functions

        [ :DEF: addsub_s

	AREA   |.text|, CODE, READONLY

        EXPORT  __fp_addsub_common
        EXPORT  __fp_addsub_uncommon

        ]

;------------------------------------------------------------------------------

        [ :DEF: mul_s

	AREA   |.text|, CODE, READONLY

        EXPORT  __fp_mult_common
        EXPORT  __fp_mult_fast_common
        EXPORT  __fp_mult_uncommon

        ]

;---------------------------------------------------------------------------

        [ :DEF: div_s

	AREA   |.text|, CODE, READONLY
        
        EXPORT  __fp_div_common
        EXPORT  __fp_rdv_common
        EXPORT  __fp_div_uncommon
        EXPORT  __fp_rdv_uncommon

        ]

;---------------------------------------------------------------------------

        [ :DEF: sqrt_s

	AREA   |.text|, CODE, READONLY

        EXPORT  __fp_sqrt_common
        EXPORT  __fp_sqrt_uncommon

        ]

;---------------------------------------------------------------------------

        [ :DEF: fix_s

	AREA   |.text|, CODE, READONLY

        EXPORT  __fp_fix_common
        EXPORT  __fp_fix_uncommon

        ]

;---------------------------------------------------------------------------

        [ :DEF: fixu_s

	AREA   |.text|, CODE, READONLY

        EXPORT  __fp_fixu_common
        EXPORT  __fp_fixu_uncommon

        ]

;===========================================================================

        [ :DEF: compare_s

	AREA   |.text|, CODE, READONLY

        EXPORT  __fp_compare

        ]

;===========================================================================

        GET     arith.asm

        END
