;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Copyright (c) Microsoft Corporation.   All rights reserved.
;
; Include file for kernel assembly files.
;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Include platform definitions

include ix.inc

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Include singularity declarations

include halclass.inc

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Macros for accessing fields inside ProcessorContext
;

GET_PROCESSOR_CONTEXT MACRO reg
        mov         REG32(reg), [?c_currentCpuOffset@Class_Microsoft_Singularity_Isal_Isa@@2HA]
        mov         reg, PSEG:[REG32(reg)]
        ENDM

GET_THREAD_CONTEXT MACRO reg
        mov         REG32(reg), [?c_currentThreadOffset@Class_Microsoft_Singularity_Isal_Isa@@2HA]
        mov         reg, PSEG:[REG32(reg)]
        ENDM

GET_PROCESSOR_CONTEXT_FIELD MACRO reg, field
        GET_PROCESSOR_CONTEXT reg
        mov         reg, [reg].Struct_Microsoft_Singularity_ProcessorContext.field
ENDM    

SET_PROCESSOR_CONTEXT_FIELD MACRO field, reg
        push        reg
        GET_PROCESSOR_CONTEXT reg
        pop         [reg].Struct_Microsoft_Singularity_ProcessorContext.field
        mov         reg, [reg].Struct_Microsoft_Singularity_ProcessorContext.field
ENDM    
        
GET_THREAD_CONTEXT_FIELD MACRO reg, field
        GET_THREAD_CONTEXT reg
        mov         reg, [reg].Struct_Microsoft_Singularity_ThreadContext.field
ENDM    

SET_THREAD_CONTEXT_FIELD MACRO field, reg
        push        reg
        GET_THREAD_CONTEXT reg
        pop         [reg].Struct_Microsoft_Singularity_ThreadContext.field
        mov         reg, [reg].Struct_Microsoft_Singularity_ThreadContext.field
ENDM    
        
GET_CPU_RECORD_FIELD MACRO reg, field
        GET_PROCESSOR_CONTEXT reg
        mov         reg, [reg].Struct_Microsoft_Singularity_Isal_CpuRecord.field
ENDM    

SET_CPU_RECORD_FIELD MACRO field, reg
        push        reg
        GET_PROCESSOR_CONTEXT reg
        pop         [reg].Struct_Microsoft_Singularity_Isal_CpuRecord.field
        mov         reg, [reg].Struct_Microsoft_Singularity_Isal_CpuRecord.field
ENDM    

GET_THREAD_RECORD_FIELD MACRO reg, field
        GET_THREAD_CONTEXT reg
        mov         reg, [reg].Struct_Microsoft_Singularity_Isal_ThreadRecord.field
ENDM    
        
SET_THREAD_RECORD_FIELD MACRO field, reg
        push        reg
        GET_THREAD_CONTEXT reg
        pop         [reg].Struct_Microsoft_Singularity_Isal_ThreadRecord.field
        mov         reg, [reg].Struct_Microsoft_Singularity_Isal_ThreadRecord.field
        ENDM

; define CurrentThread() function as a macro.
CurrentThread MACRO reg
        GET_THREAD_CONTEXT_FIELD(__thread,reg)
        ENDM

CurrentThreadContext MACRO reg
	    GET_THREAD_CONTEXT reg
        ENDM

CurrentThreadRecord MACRO reg
	    GET_THREAD_CONTEXT reg
        ENDM

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Big/Little Endian Definitions for Long Integers
;

ifdef   bigend                  ; Big Endian (hi word at low address)
LOWORD  equ     [4]
HIWORD  equ     [0]
else                            ; Little Endian (low word at low address)
LOWORD  equ     [0]
HIWORD  equ     [4]
endif

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; X64 specific stuff

ifdef ISA_IX64

include halx64.inc

endif

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; End of File.
