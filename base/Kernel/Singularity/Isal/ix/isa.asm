;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; Assembly code for Isal.Target class

include hal.inc

SYMFIX(?g_GetCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SIPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@XZ) proc

        GET_THREAD_CONTEXT PAX
        ret

SYMFIX(?g_GetCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SIPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@XZ) endp
        
SYMFIX(?g_GetCurrentCpu@Class_Microsoft_Singularity_Isal_Isa@@SIPAUStruct_Microsoft_Singularity_Isal_CpuRecord@@XZ) proc

        GET_PROCESSOR_CONTEXT PAX
        ret

SYMFIX(?g_GetCurrentCpu@Class_Microsoft_Singularity_Isal_Isa@@SIPAUStruct_Microsoft_Singularity_Isal_CpuRecord@@XZ) endp

ifdef SINGULARITY_KERNEL
        
SYMFIX(?g_InitializeCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SIXPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@@Z) proc

        mov     eax, [?c_currentThreadOffset@Class_Microsoft_Singularity_Isal_Isa@@2HA]
        mov     PSEG:[eax], PCX
        ret

SYMFIX(?g_InitializeCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SIXPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@@Z) endp

SYMFIX(?g_SetCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SIXPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@@Z) proc

        mov     eax, [?c_currentThreadOffset@Class_Microsoft_Singularity_Isal_Isa@@2HA]
        
        ;; Must preserve active stack limit across thread context switch
        mov     PDX, PSEG:[eax]
        mov     PDX, [PDX].Struct_Microsoft_Singularity_Isal_ThreadRecord._activeStackLimit
        mov     [PCX].Struct_Microsoft_Singularity_Isal_ThreadRecord._activeStackLimit, PDX

        mov     PSEG:[eax], PCX
        ret

SYMFIX(?g_SetCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SIXPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@@Z) endp

SYMFIX(?g_InitializeCurrentCpu@Class_Microsoft_Singularity_Isal_Isa@@SIXPAUStruct_Microsoft_Singularity_Isal_CpuRecord@@@Z) proc

        mov     eax, [?c_currentCpuOffset@Class_Microsoft_Singularity_Isal_Isa@@2HA]
        mov     PSEG:[eax], PCX
        ret

SYMFIX(?g_InitializeCurrentCpu@Class_Microsoft_Singularity_Isal_Isa@@SIXPAUStruct_Microsoft_Singularity_Isal_CpuRecord@@@Z) endp

SYMFIX(?c_DefaultReturnFromInterrupt@Class_Microsoft_Singularity_Isal_Isa@@2EA) label byte
        IRETP

SYMFIX(?g_SwitchToInterruptStackAndCallback@Class_Microsoft_Singularity_Isal_Isa@@SIPAUuintPtr@@PAUClass_Microsoft_Singularity_Isal_Isa_ICallback@@PAU2@@Z) proc

        ;; use an ebp frame so we can easily restore the old stack
        push    PBP
        mov     PBP, PSP

        ;; switch to the interrupt stack
        GET_CPU_RECORD_FIELD PAX, _interruptStackBegin
        mov     PSP, PAX

        ;; Save previous limit
        GET_THREAD_RECORD_FIELD PAX, _activeStackLimit
        push    PAX
        
        ;; set the new stack limit
        GET_CPU_RECORD_FIELD PAX, _interruptStackLimit
        SET_THREAD_RECORD_FIELD _activeStackLimit, PAX

        ;; call the callback
        call    SYMFIX(?g_DoCallback@Class_Microsoft_Singularity_Isal_Isa_ICallback@@SIPAUuintPtr@@PAU1@PAU2@@Z)

        ;; restore the stack limit
        pop     PCX
        SET_THREAD_RECORD_FIELD _activeStackLimit, PCX

        ;; pop ebp frame
        mov     PSP, PBP
        pop     PBP

        ret
        
SYMFIX(?g_SwitchToInterruptStackAndCallback@Class_Microsoft_Singularity_Isal_Isa@@SIPAUuintPtr@@PAUClass_Microsoft_Singularity_Isal_Isa_ICallback@@PAU2@@Z) endp

endif

SYMFIX(?g_GetCs@Class_Microsoft_Singularity_Isal_Isa@@SIPAUuintPtr@@XZ) proc

        mov PAX, cs
        ret

SYMFIX(?g_GetCs@Class_Microsoft_Singularity_Isal_Isa@@SIPAUuintPtr@@XZ) endp
        
SYMFIX(?g_InitFpu@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ) proc

        finit
        mov     PAX, 37Eh
        push    PAX
        fldcw   [PSP]
        pop     PAX
        ret

SYMFIX(?g_InitFpu@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ) endp

SYMFIX(?g_ReadFpuStatus@Class_Microsoft_Singularity_Isal_Isa@@Z@@XZ) proc

        xor PAX,PAX
        push PAX
        fnstsw [PSP]
        pop PAX
        ret

SYMFIX(?g_ReadFpuStatus@Class_Microsoft_Singularity_Isal_Isa@@Z@@XZ) endp

SYMFIX(?g_ClearFpuStatus@Class_Microsoft_Singularity_Isal_Isa@@Z@@XZ) proc

        fnclex
        ret

SYMFIX(?g_ClearFpuStatus@Class_Microsoft_Singularity_Isal_Isa@@Z@@XZ) endp

SYMFIX(?g_EnterUserMode@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ) proc

   ;; warning: preserve return values eax, edx (for returning from ABI)

        push PDX
        mov PCX, PSP
        mov PDX, ring3
        ;;sysexit
        db   0fh
        db   35h
      ring3:
        pop PDX

ifdef ISA_IX86
        mov cx, ss
        mov ds, cx
        mov es, cx
endif
        mov cx, Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt._pp + 3
        mov PSEG, cx

        ret
        
SYMFIX(?g_EnterUserMode@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ) endp

SYMFIX(?g_GetFramePointer@Class_Microsoft_Singularity_Isal_Isa@@SIPAUuintPtr@@XZ) proc
        mov PAX, PBP
        ret
SYMFIX(?g_GetFramePointer@Class_Microsoft_Singularity_Isal_Isa@@SIPAUuintPtr@@XZ) endp

END
