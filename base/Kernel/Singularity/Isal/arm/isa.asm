;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;;
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; Assembly code for Isal.Isa class

        CODE32

        AREA    |.text|, CODE, ARM

|defining ?g_GetCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SAPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@XZ| EQU 1
|defining ?g_GetCurrentCpu@Class_Microsoft_Singularity_Isal_Isa@@SAPAUStruct_Microsoft_Singularity_Isal_CpuRecord@@XZ| EQU 1
|defining ?g_InitializeCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SAXPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@@Z| EQU 1
|defining ?g_SetCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SAXPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@@Z| EQU 1
|defining ?g_InitializeCurrentCpu@Class_Microsoft_Singularity_Isal_Isa@@SAXPAUStruct_Microsoft_Singularity_Isal_CpuRecord@@@Z| EQU 1
|defining ?c_DefaultReturnFromInterrupt@Class_Microsoft_Singularity_Isal_Isa@@2EA| EQU 1
|defining ?g_SwitchToInterruptStackAndCallback@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@PAUClass_Microsoft_Singularity_Isal_Isa_ICallback@@PAU2@@Z| EQU 1
|defining ?g_Halt@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ| EQU 1
|defining ?g_EnableInterrupts@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ| EQU 1
|defining ?g_DisableInterrupts@Class_Microsoft_Singularity_Isal_Isa@@SA_NXZ| EQU 1
|defining ?g_AreInterruptsDisabled@Class_Microsoft_Singularity_Isal_Isa@@SA_NXZ| EQU 1
|defining ?g_GetCpsr@Class_Microsoft_Singularity_Isal_Isa@@SAIXZ| EQU 1

|defining ?g_GetFramePointer@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@XZ| EQU 1
|defining ?g_GetFrameCallerFrame@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@PAU2@@Z| EQU 1
|defining ?g_GetStackReturnAddresses@Class_Microsoft_Singularity_Isal_Isa@@SAIPAUClassVector_uintPtr@@@Z| EQU 1
|defining ?g_GetFrameReturnAddress@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@PAU2@@Z| EQU 1
|defining ?g_GetStackPointer@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@XZ| EQU 1

        include hal.inc

;;;
        LEAF_ENTRY ?g_GetCpsr@Class_Microsoft_Singularity_Isal_Isa@@SAIXZ
        msr     cpsr, r0
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_GetCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SAPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@XZ
        GET_THREAD_FIELD_ADDR r0, r12, #0
        bx      lr
        LEAF_END


        LEAF_ENTRY ?g_GetCurrentCpu@Class_Microsoft_Singularity_Isal_Isa@@SAPAUStruct_Microsoft_Singularity_Isal_CpuRecord@@XZ
        GET_CPU_FIELD_ADDR r0, r12, #0
        bx      lr
        LEAF_END

        if :DEF:SINGULARITY_KERNEL

;;;
;;; void InitializeCurrentThread(ref CpuRecord record)
;;;
;;; Set the pointer to the CPU's CpuRecord
;;;
;;;     mov eax, [?c_currentCpuOffset@Class_Microsoft_Singularity_Isal_Isa@@2HA]
;;;     mov PSEG:[eax], PCX
;;;
        LEAF_ENTRY ?g_InitializeCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SAXPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@@Z
        GET_THREAD_ADDR r1, r12
        str     r0, [r1]
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_SetCurrentThread@Class_Microsoft_Singularity_Isal_Isa@@SAXPAUStruct_Microsoft_Singularity_Isal_ThreadRecord@@@Z
        GET_THREAD_ADDR r1, r12

        ;; get active stack limit
        ldr     r2, [r1]
        ldr     r2, [r2, #Struct_Microsoft_Singularity_Isal_ThreadRecord___activeStackLimit]

        ;; Set new thread value
        str     r0, [r1]

        ;; maintain same active stack limit
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_ThreadRecord___activeStackLimit]

        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_InitializeCurrentCpu@Class_Microsoft_Singularity_Isal_Isa@@SAXPAUStruct_Microsoft_Singularity_Isal_CpuRecord@@@Z
        GET_CPU_ADDR r1, r12
        str     r0, [r1]
        bx      lr
        LEAF_END

        LEAF_ENTRY ?c_DefaultReturnFromInterrupt@Class_Microsoft_Singularity_Isal_Isa@@2EA
        bkpt    0xffff
        bx      lr
        LEAF_END

|?g_SwitchToInterruptStackAndCallback@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@PAUClass_Microsoft_Singularity_Isal_Isa_ICallback@@PAU2@@Z| PROC

        ;; stack frame
        stmfd   sp!, {r11,lr}
        mov     r11, sp

        ;; Switch to the interrupt stack
        GET_CPU_FIELD_ADDR r2, r12, #Struct_Microsoft_Singularity_Isal_CpuRecord___interruptStackBegin
        ldr     sp, [r2]
        GET_CPU_FIELD_ADDR r2, r12, #Struct_Microsoft_Singularity_Isal_CpuRecord___interruptStackLimit
        GET_THREAD_FIELD_ADDR r3, r12, #Struct_Microsoft_Singularity_Isal_ThreadRecord___activeStackLimit
        ldr     r2, [r2]
        str     r2, [r3]

        bl      |?g_DoCallback@Class_Microsoft_Singularity_Isal_Isa_ICallback@@SAPAUuintPtr@@PAU1@PAU2@@Z|

        mov     sp, r11
        ldmfd   sp!, {r11,lr}

        bx      lr
        ENDP

        endif

        LEAF_ENTRY ?g_Halt@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ
;;        DCD     0xe320f003      ;; WFI Note: ARMv7 Specific.
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_EnableInterrupts@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ
        mrs     r0, cpsr
        bic     r0, r0, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        msr     cpsr_c, r0
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_DisableInterrupts@Class_Microsoft_Singularity_Isal_Isa@@SA_NXZ

        mrs     r1, cpsr
        ;; remember previous bit for later
        and     r0, r1, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        orr     r1, r1, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        msr     cpsr_c, r1

        ;; if bit is 1, we return false, so negate the bit with an xor
        eors    r0, r0, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        ;; normalize true value
        movne   r0, #1

        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_AreInterruptsDisabled@Class_Microsoft_Singularity_Isal_Isa@@SA_NXZ
        mrs     r0, cpsr
        ands    r0, r0, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        ;; normalize true value
        movne   r0, #1
        bx      lr
        LEAF_END

;;;
;;; "public: static struct uintPtr * __cdecl Class_Microsoft_Singularity_Isal_Isa::g_GetStackPointer(void)"
;;;
        LEAF_ENTRY ?g_GetStackPointer@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@XZ
        mov     r0, sp
        bx      lr
        LEAF_END

;;;
;;; "public: static struct uintPtr * __cdecl Class_Microsoft_Singularity_Isal_Isa::g_GetFramePointer(void)"
;;;
        LEAF_ENTRY ?g_GetFramePointer@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@XZ
        mov     r0, r11
        bx      lr
        LEAF_END

;;;
;;; "public: static struct uintPtr * __cdecl Class_Microsoft_Singularity_Isal_Isa::g_GetFrameReturnAddress(struct uintPtr *)"
;;;
        LEAF_ENTRY ?g_GetFrameReturnAddress@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@PAU2@@Z
        mov     r0, #0 ; [r0, #0]
        ;; ldr     r0, [r0, #4]
        bx      lr
        LEAF_END

;;;
;;; "public: static struct uintPtr * __cdecl Class_Microsoft_Singularity_Isal_Isa::g_GetFrameCallerFrame(struct uintPtr *)"
;;;
        LEAF_ENTRY ?g_GetFrameCallerFrame@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@PAU2@@Z
        mov     r0, #0 ; [r0, #0]
        ;; ldr     r0, [r0, #0]
        bx      lr
        LEAF_END

        END

