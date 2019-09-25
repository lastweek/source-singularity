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
; Definitions relating to the ARM. Also used by "fplib".
;
; Copyright (C) Advanced RISC Machines Limited, 1992-7. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

;===========================================================================

; PSR fields.

Flags_mask      EQU     &F0000000
N_bit           EQU     &80000000
Z_bit           EQU     &40000000
C_bit           EQU     &20000000
V_bit           EQU     &10000000
                [ {CONFIG}=26
IntMasks_mask     EQU     &0C000000
I_bit             EQU     &08000000
F_bit             EQU     &04000000
Mode_mask         EQU     &00000003
PSR_mask          EQU     Flags_mask:OR:IntMasks_mask:OR:Mode_mask
                ]
                [ {CONFIG}=32
IntMasks_mask     EQU     &000000C0
I_bit             EQU     &00000080
F_bit             EQU     &00000040
Mode_mask         EQU     &0000001F
Mode_32not26      EQU     &00000010
Mode_USR32        EQU     &00000010
Mode_FIQ32        EQU     &00000011
Mode_IRQ32        EQU     &00000012
Mode_SVC32        EQU     &00000013
Mode_ABT32        EQU     &00000017
Mode_UND32        EQU     &0000001B
Mode_SYS32        EQU     &0000001F
                ]
Mode_USR26      EQU     &00000000
Mode_FIQ26      EQU     &00000001
Mode_IRQ26      EQU     &00000002
Mode_SVC26      EQU     &00000003

; The ARM vectors.

Reset_vector    EQU     &00
Undef_vector    EQU     &04
SWI_vector      EQU     &08
Prefetch_vector EQU     &0C
Data_vector     EQU     &10
        [ {CONFIG}=26
AdrExc_vector   EQU     &14
        ]
IRQ_vector      EQU     &18
FIQ_vector      EQU     &1C

; Other ARM constants.

TopBit          EQU     &80000000

;===========================================================================

        END
