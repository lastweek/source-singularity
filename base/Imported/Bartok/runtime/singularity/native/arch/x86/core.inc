;
; Bartok
; Copyright (C) Microsoft Corporation.  All Rights Reserved.
;

; Common include file for all assembly files.

include hal.inc

ifdef SINGULARITY_KERNEL
externdef ?g_setStopContext@Class_System_Threading_Thread@@SIXPAU1@PAUClass_System_Exception@@@Z:NEAR
externdef __throwBeyondMarker:NEAR
endif ; SINGULARITY_KERNEL

; This is a nop on Singularity
ResetGuardPageOnStackOverflow MACRO
        ENDM
