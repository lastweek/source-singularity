;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains x86-specific assembly code related to context save and restore.
;;; The key goal here is to keep this set of code as small as possible, in favor
;;; of portable C++ or C# code.

        CODE32

        AREA    |.text|, CODE, ARM

|defining ?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SA_NPAU1@@Z| EQU 1
|defining ?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SA_NPAU1@PAUStruct_Microsoft_Singularity_Isal_InterruptContext@@@Z| EQU 1
|defining ?m_Resume@Struct_Microsoft_Singularity_Isal_SpillContext@@SAXPAU1@@Z| EQU 1
|defining ?g_ResetCurrent@Struct_Microsoft_Singularity_Isal_SpillContext@@SAXXZ| EQU 1

        include hal.inc

;;; Save takes one argument - a context record to save the context in. It saves all the
;;; nonvolatile state (it does not bother saving caller save regs.)
;;;
;;; This function returns true after saving the context. When the context is resumed, control
;;; resumption will occur at the point this function returned, but with a false
;;; return value.
;;; 
;;; Calling conventions are normal __fastcall.
    
;; __fastcall bool SaveContext(Context *context)
    
        LEAF_ENTRY ?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SA_NPAU1@@Z 
        
        ;; Save the bulk of the registers (r0-r12).
        stmia   r0, {r0-r12}

        ;; Save sp and (stale) lr.
        str     sp, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___sp]
        str     lr, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___lr]
        
        ;; Save lr as the pc.
        str     lr, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___pc]

        ;; Save cpsr
        mrs     r1, cpsr
        str     r1, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___cpsr]

        ;; Overright r0, so the return value contains zero on context resume
        ldr     r1, =0
        str     r1, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___r0]

        ;; Save stack limit
        GET_THREAD_FIELD_ADDR r2, r12, #Struct_Microsoft_Singularity_Isal_ThreadRecord___activeStackLimit
        ldr     r2, [r2]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___stackLimit]

        ;; Set spilled flag
        ldr     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___spillFlags]
        orr     r2, r2, #Struct_Microsoft_Singularity_Isal_SpillContext_ContentsSpilled
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___spillFlags]

        ;; return true for initial save
        ldr     r0, =1
        bx      lr
        
        LEAF_END

;;; Save takes two arguments - a context record to save the context in, and
;;; an interrupt frame to describe an interruption location.
;;;
;;; Calling conventions are normal __fastcall.
    
;; __fastcall bool SaveContext(Context *context, InterruptContext *interrupt)

        LEAF_ENTRY ?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SA_NPAU1@PAUStruct_Microsoft_Singularity_Isal_InterruptContext@@@Z

        ;; Pick up registers from the interrupt context

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___r0]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___r0]

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___r1]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___r1]

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___r2]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___r2]

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___r3]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___r3]

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___r12]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___r12]

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___lr]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___lr]

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___sp]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___sp]

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___pc]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___pc]

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___cpsr]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___cpsr]

        ldr     r2, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___instruction]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___instruction]

        ;; Save the rest of the registers from the current state
        add     r2, r0, #Struct_Microsoft_Singularity_Isal_SpillContext___r4
        stmia   r2, {r4-r11}

        ;; Save stack limit
        GET_THREAD_FIELD_ADDR r2, r12, #Struct_Microsoft_Singularity_Isal_ThreadRecord___activeStackLimit
        ldr     r2, [r2]
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___stackLimit]

        ;; Set spilled flag
        ldr     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___spillFlags]
        orr     r2, r2, #Struct_Microsoft_Singularity_Isal_SpillContext_ContentsSpilled
        str     r2, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___spillFlags]

        ;; We're done
        bx      lr

        LEAF_END


;;; Resume restores the processor state to the state described in the given
;;; context record.
;;; 
;;; __fastcall void ResumeContext(Struct_Microsoft_Singularity_Isal_SpillContext *context);
    
|?m_Resume@Struct_Microsoft_Singularity_Isal_SpillContext@@SAXPAU1@@Z| PROC

        ;; Switch to supervisor mode so we can get an atomic resume including CPSR.
        mrs     r1, cpsr
        bic     r1, r1, #Struct_Microsoft_Singularity_Isal_Arm_ProcessorMode_Mask
        orr     r1, r1, #Struct_Microsoft_Singularity_Isal_Arm_ProcessorMode_Supervisor
        msr     cpsr_c, r1

        ;; Clear spilled flag.
        ldr     r1, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___spillFlags]
        bic     r1, r1, #Struct_Microsoft_Singularity_Isal_SpillContext_ContentsSpilled
        str     r1, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___spillFlags]

        ;; Restore stack limit.
        ldr     r1, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___stackLimit]
        GET_THREAD_FIELD_ADDR r2, r12, #Struct_Microsoft_Singularity_Isal_ThreadRecord___activeStackLimit
        str     r1, [r2]

        ;; Move saved CPSR into SPSR.
        ldr     r1, [r0, #Struct_Microsoft_Singularity_Isal_SpillContext___cpsr]
        msr     spsr, r1

        ;; Restore banked pre-interrupt registers (use R3 as pointer to banked registers).
        add     r3, r0, #Struct_Microsoft_Singularity_Isal_SpillContext___sp
        ldmia   r3, {sp,lr}^

        ;; Resume unbanked pre-interrupt state.
        ldmia   r0, {r0-r12,pc}^
        
        ENDP
    
;;; ResetContext resets the current context fp & debug register state to a canonical state
;;; for interrupt handler code.  This should only be used after saving the current context.
;;;
;;; Calling conventions are normal __fastcall.
;;; 
;;; __fastcall void ResetCurrent();
    
        LEAF_ENTRY ?g_ResetCurrent@Struct_Microsoft_Singularity_Isal_SpillContext@@SAXXZ
        bx      lr
        LEAF_END

        END

