;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;;
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code handling dispatching of interrupts.

        CODE32

        AREA    |.text|, CODE, ARM, ALIGN=5

|defining ?g_LoadResetVector@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ|      EQU 1
|defining ?g_DispatchVector@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ|              EQU 1
|defining ?g_SetModeSp@Class_Microsoft_Singularity_Isal_Isa@@SAXHPAUuintPtr@@@Z|      EQU 1
        INCLUDE hal.inc

;;; These are exported so we can see, in the debugger, which exception was triggered.

        EXPORT |DispatchReset|
        EXPORT |DispatchUndefinedInstruction|
        EXPORT |DispatchSupervisorCall|
        EXPORT |DispatchPrefetchAbort|
        EXPORT |DispatchDataAbort|
        EXPORT |DispatchUnused|
        EXPORT |DispatchIrq|
        EXPORT |DispatchFiq|

        EXPORT |VectorReset|
        EXPORT |VectorUndefinedInstruction|
        EXPORT |VectorSupervisorCall|
        EXPORT |VectorPrefetchAbort|
        EXPORT |VectorDataAbort|
        EXPORT |VectorUnused|
        EXPORT |VectorIrq|
        EXPORT |VectorFiq|

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Isa::g_LoadIdt(void)"
;;; Loads the address of the exception vectors into the VBAR.
;;;
        LEAF_ENTRY ?g_LoadResetVector@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ
        ;; Load the address of the 0 interrupt vector into r0.
        adr     r0, VectorReset
        ;; Load R0 into VBAR. Note: This code is ARMv7 specific.
        mcr     p15,0,r0,c12,c0,0
        bx      lr
        LEAF_END

;;; SetModeSp sets the stack pointer in the target mode to the value passed in.

        LEAF_ENTRY ?g_SetModeSp@Class_Microsoft_Singularity_Isal_Isa@@SAXHPAUuintPtr@@@Z

        ;; r0 arg contains the target mode
        ;; r1 arg contains the value for sp

        mrs     r2, cpsr
        bic     r3, r2, #Struct_Microsoft_Singularity_Isal_Arm_ProcessorMode_Mask
        orr     r3, r3, r0
        msr     cpsr_c, r3
        mov     sp, r1
        msr     cpsr_c, r2

        bx      lr

        LEAF_END

        LTORG

;;; VectorX indicates a branch instruction in the exception vector
;;; Note that these 8 1-instruction functions must be laid out in exactly
;;; this order as this *IS* the hardware exception vector on ARM.

        LEAF_ENTRY VectorReset
        ldr pc, [pc, #24]  ;       b |DispatchReset|
        LEAF_END
        LEAF_ENTRY VectorUndefinedInstruction
        ldr pc, [pc, #24]  ;b |DispatchUndefinedInstruction|
        LEAF_END
        LEAF_ENTRY VectorSupervisorCall
        ldr pc, [pc, #24]  ;b |DispatchSupervisorCall|
        LEAF_END
        LEAF_ENTRY VectorPrefetchAbort
        ldr pc, [pc, #24]  ;b |DispatchPrefetchAbort|
        LEAF_END
        LEAF_ENTRY VectorDataAbort
        ldr pc, [pc, #24]  ;b |DispatchDataAbort|
        LEAF_END
        LEAF_ENTRY VectorUnused
        ldr pc, [pc, #24]  ;b |DispatchUnused|
        LEAF_END
        LEAF_ENTRY VectorIrq
        ldr pc, [pc, #24]  ;b |DispatchIrq|
        LEAF_END
        LEAF_ENTRY VectorFiq
        ldr pc, [pc, #24]  ;b |DispatchFiq|
        LEAF_END

BeginRedirections
        DCD |DispatchReset|
        DCD |DispatchUndefinedInstruction|
        DCD |DispatchSupervisorCall|
        DCD |DispatchPrefetchAbort|
        DCD |DispatchDataAbort|
        DCD |DispatchUnused|
        DCD |DispatchIrq|
        DCD |DispatchFiq|
EndOfRedirections

;;; Interrupt dispatching on ARM occurs at fixed memory locations (either 0-based or
;;; FFFF0000-based).  For now we use the zero base exclusively.

;;; ARM has 7 interrupt categories.  Currently we use a simplified model, which
;;; matches other architectures (i.e. we move to a single per-processor interrupt
;;; stack for all interrupt handling.)
;;;
;;; Modes:
;;; IRQ: this is normal device interrupt we expect to get.
;;; Abort: both types of aborts correspond to normal software exceptions,
;;;     (which are currently just forwarded to the debugger)
;;; All other interrupts are assumed to be anomalous, and are also passed to the debugger.
;;;     FIQ: we don't want to write special interrupt handlers currently, so this
;;;             mode has no benefit
;;;     SWI, Reset: no cases of these yet.
;;;
;;; We do not execute substantial amounts of code in IRQ mode.  This is because
;;; a nested IRQ interrupt would trash our lr register. (We don't take nested IRQ's
;;; now, but likely will eventually.)


;;; The GO_DISPATCH macro creates an InterruptContext at the top of the interrupted
;;; stack and save R0-R3 and the exception vector number into it (takes as an argument).
;;; GO_DISPATCH branches to |GoDispatchPhase2| which saves the rest of the caller-saved
;;; registers and switches to system mode.  If $save is true, the faulting instruction
;;; opcode is saved as well.

;;; Note that this code requires the interrupt mode sp to point to a DispatchStack structure.

        MACRO
        GO_DISPATCH $vector, $save

        ;; Sp in interrupt mode will always point at a per-cpu DispatchStack structure

        ;; Free R4 and fetch interrupted SP.
        stmia   sp, {r4,sp}^ ; Stored to Struct_Microsoft_Isal_Arm_DispatchStack

        ;; Load address of interrupt context from interrupted SP.
        ldr     r4, [sp, #Struct_Microsoft_Singularity_Isal_Arm_DispatchStack___sp]
        sub     r4, r4, #Struct_Microsoft_Singularity_Isal_InterruptContext___SIZE

        ;; Save the unbanked user volatile regs (this gets us some scratch regs)
        stmia   r4, {r0-r3,r12}

        ;; Save vector
        ldr     r0, =$vector
        str     r0, [r4, #Struct_Microsoft_Singularity_Isal_InterruptContext___vector]

        ;; Save interrupted PC.
        sub     r0, lr, #4
        str     r0, [r4, #Struct_Microsoft_Singularity_Isal_InterruptContext___pc]

        ;; Save faulting instruction (from the pc in r0)
        IF $save
        ldr     r0, [r0]
        ELSE
        ldr     r0, =0
        ENDIF
        str     r0, [r4, #Struct_Microsoft_Singularity_Isal_InterruptContext___instruction]

        ;; Continue in share code (with r4 == InterruptContext)
        b |GoModePhase2|


        MEND

;;;

|GoModePhase2| PROC

        ;; Save the banked interrupted registers (use R3 as pointer to banked registers).
        add     r3, r4, #Struct_Microsoft_Singularity_Isal_InterruptContext___sp
        stmia   r3, {sp,lr}^

        ;; Save interrupted CPSR.
        mrs     r0, spsr
        str     r0, [r4, #Struct_Microsoft_Singularity_Isal_InterruptContext___cpsr]

        ;; Move InterruptContext pointer to r3 and restore r4 from DispatchStack.
        mov     r3, r4
        ldr     r4, [sp, #Struct_Microsoft_Singularity_Isal_Arm_DispatchStack___r4]

        ;; Switch to system mode
        mrs     r0, cpsr
        bic     r0, r0, #Struct_Microsoft_Singularity_Isal_Arm_ProcessorMode_Mask
        orr     r0, r0, #Struct_Microsoft_Singularity_Isal_Arm_ProcessorMode_System
        msr     cpsr_c, r0

        ;; Restore SP to top of the InterruptContext (i.e. old sp - sizeof(InterruptContext)).
        mov     sp, r3

        ;; Jump to common dispatch routine. (with r3 = InterruptContext)
        b |?g_DispatchVector@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ|

        ENDP

;;; DispatchX is the dispatch routine for vector X.  This code is largely identical
;;; for all the vectors, except for the ID constant which is pushed in the frame
;;; TBD: sharing more code would be a good thing, but it's tough to find a place to stash
;;; the interrupt id.

        LEAF_ENTRY DispatchReset
        GO_DISPATCH Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_Reset,{false}
        LEAF_END
        LEAF_ENTRY DispatchUndefinedInstruction
        GO_DISPATCH Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_UndefinedInstruction,{true}
        LEAF_END
        LEAF_ENTRY DispatchSupervisorCall
        GO_DISPATCH Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_SoftwareInterrupt,{true}
        LEAF_END
        LEAF_ENTRY DispatchPrefetchAbort
        GO_DISPATCH Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_PrefetchAbort,{false}
        LEAF_END
        LEAF_ENTRY DispatchDataAbort
        GO_DISPATCH Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_DataAbort,{true}
        LEAF_END
        LEAF_ENTRY DispatchUnused
        GO_DISPATCH Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_Unused,{false}
        LEAF_END
        LEAF_ENTRY DispatchIrq
        GO_DISPATCH Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_Irq,{false}
        LEAF_END
        LEAF_ENTRY DispatchFiq
        GO_DISPATCH Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_Fiq,{false}
        LEAF_END
|DispatchTableEnd|

;;; DispatchVector implements the meat of the low level interrupt dispatching logic. Its goal
;;; is to implement the transition to high level code with minimal overhead.

|?g_DispatchVector@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ| PROC

        ;; Pick the correct spill context based on the interrupt vector.

        ;; Our normal scheduler-capable interrupts are IRQ's. Other exceptions
        ;; are just reported to the debugger for now.
        ;;
        ;; TODO: Note that we are not implementing a "no scheduler switch" category
        ;; of interrupts for now, so we won't be able to handle nested interrupts.  This will
        ;; be easy to change if we can figure out the right criteria to identify such interrupts
        ;; at this level later on.
        ;;
        ;;

        ldr     r0, [sp, #Struct_Microsoft_Singularity_Isal_InterruptContext___vector]
        cmp     r0, #Struct_Microsoft_Singularity_Isal_Arm_ExceptionVector_Irq
        bne     |debug|

        ;; Use current thread's spill context
        GET_THREAD_FIELD_ADDR r0, r12, #Struct_Microsoft_Singularity_Isal_ThreadRecord___spill
        b       |save|

|debug| ;; Use cpu's spill context
        GET_CPU_FIELD_ADDR r0, r12, #Struct_Microsoft_Singularity_Isal_CpuRecord___spill

|save|  ;; Save to spill context
        mov     r1, sp
        bl      |?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SA_NPAU1@PAUStruct_Microsoft_Singularity_Isal_InterruptContext@@@Z|

        ;; Save previous stack limit
        GET_THREAD_FIELD_ADDR r0, r12, #Struct_Microsoft_Singularity_Isal_ThreadRecord___activeStackLimit
        ldr     r0, [r0]
        PUSH    r0

        ;; See if we are already on the interrupt stack
        GET_CPU_FIELD_ADDR r1, r12, #Struct_Microsoft_Singularity_Isal_CpuRecord___interruptStackLimit
        ldr     r1, [r1]
        cmp     r1, r0

        ;; Stash current sp
        mov     r0, sp

        beq     |no_switch|

        ;; Now switch to the interrupt stack
        GET_CPU_FIELD_ADDR r2, r12, #Struct_Microsoft_Singularity_Isal_CpuRecord___interruptStackBegin
        ldr     sp, [r2]
        GET_THREAD_FIELD_ADDR r2, r12, #Struct_Microsoft_Singularity_Isal_ThreadRecord___activeStackLimit
        str     r1, [r2]

|no_switch|
        ;; Save the old stack pointer
        PUSH    r0

        ;; Interrupt context is old stack pointer + 4
        add     r0, r0, #4

        ;; Call dispatch routine
        bl      |?g_DispatchInterrupt@Class_Microsoft_Singularity_Isal_Isa@@SAXPAUStruct_Microsoft_Singularity_Isal_InterruptContext@@@Z|

        ;; Restore the old stack pointer and limit
        POP     sp
        POP     r0
        GET_THREAD_FIELD_ADDR r1, r12, #Struct_Microsoft_Singularity_Isal_ThreadRecord___activeStackLimit
        str     r0, [r1]

        ;; Now we need to switch back to interrupt mode so we can do a proper atomic resume (using spsr)

        mov     r1, sp

        mrs     r0, cpsr
        bic     r0, r0, #Struct_Microsoft_Singularity_Isal_Arm_ProcessorMode_Mask
        orr     r0, r0, #Struct_Microsoft_Singularity_Isal_Arm_ProcessorMode_Supervisor
        msr     cpsr_c, r0

        ;; Move saved CPSR into SPSR
        ldr     r0, [r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___cpsr]
        msr     spsr, r0

        ;; Restore banked pre-interrupt registers (use R3 as pointer to banked registers).
        add     r3, r1, #Struct_Microsoft_Singularity_Isal_InterruptContext___sp
        ldmia   r3, {sp,lr}^

        ;; Resume unbanked pre-interrupt state
        ldmfd   r1, {r0-r3,r12,pc}^

        ENDP

        END
