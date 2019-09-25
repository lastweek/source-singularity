; 
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

include hal.inc

ifdef SINGULARITY_KERNEL
externdef ?g_setStopContext@Class_System_Threading_Thread@@SAXPEAU1@PEAUClass_System_Exception@@@Z:NEAR
externdef __throwBeyondMarker:NEAR
endif ; SINGULARITY_KERNEL

ResetGuardPageInStackOverflow MACRO
        ENDM
