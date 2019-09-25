;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code for the kernel debugger.
;;;

|defining ?g_Break@Class_Microsoft_Singularity_DebugStub@@SAXXZ| EQU 1

        include hal.inc

        TEXTAREA
        
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; KD Support.
;;;
        
;;;
;;; "public: static void Class_Microsoft_Singularity_DebugStub::g_Break(void)"
;;;
        LEAF_ENTRY ?g_Break@Class_Microsoft_Singularity_DebugStub@@SAXXZ
        ; bkpt    0xffff
        swi     0xffff03
        bx      lr
        LEAF_END

;;;
;;; "void KdpPause(void)"
;;;
        LEAF_ENTRY ?KdpPause@@YAXXZ
        DCD     0xe320f002      ;; WFE Note: ARMv7 Specific.
        bx      lr
        LEAF_END
        
;;;
;;; "bool KdpDisableInterruptsInline(void)"
;;;
        LEAF_ENTRY ?KdpDisableInterruptsInline@@YA_NXZ

        mrs     r1, cpsr
        ;; remember previous bit for later
        and     r0, r1, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        orr     r1, r1, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        msr     cpsr_c, r1

        ;; include a nop so the linker doesn't merge with Target.DisableInterrupts.
        nop
        
        ;; if bit is 1, we return false, so negate the bit with an xor
        eors    r0, r0, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        ;; normalize true value
        movne   r0, #1
        
        bx      lr
        LEAF_END
        
;;;
;;; "void KdpEnableInterruptsInline(void)"
;;;
        LEAF_ENTRY ?KdpEnableInterruptsInline@@SAXXZ

        mrs     r0, cpsr
        bic     r0, r0, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        msr     cpsr_c, r0
        
        bx      lr
        LEAF_END
        
;;;
;;; "void KdpRestoreInterruptsInline(bool)"
;;;
        LEAF_ENTRY ?KdpRestoreInterruptsInline@@YAX_N@Z
        cmp     r0, #0
        bne     |?KdpEnableInterruptsInline@@SAXXZ|
        bx      lr
        LEAF_END
        
;;;
;;; "void KdNotifyTrap(KdDebugTrapData *)"
;;;
        LEAF_ENTRY ?KdNotifyTrap@@YAXPAUKdDebugTrapData@@@Z
        swi     0xffff2e
        bx      lr
        LEAF_END

;;;
;;; "void KdNotifyException(System_Exception *, unsigned int throwAddr)"
;;;
        LEAF_ENTRY ?KdNotifyException@@YAXPAUClass_System_Exception@@I@Z
        ;; FIXME!!!
        swi     0xffff03
        bx      lr
        LEAF_END

;;;
;;; "void KdpArmSetControlReport(Struct_Microsoft_Singularity_Kd_ArmKdControlReport *)"
;;;
        LEAF_ENTRY ?KdpArmSetControlReport@@YAXPAUStruct_Microsoft_Singularity_Kd_ArmKdControlReport@@@Z
        ;; No support needed yet.
        bx      lr
        LEAF_END
        
        END
