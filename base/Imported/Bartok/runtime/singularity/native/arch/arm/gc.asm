;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;;
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code for transitioning GC domain boundaries.
;;;

    AREA |.text|, CODE, READONLY

|defining ?g_SwitchToThreadContext@Class_Microsoft_Singularity_Processor@@SAXPAUStruct_Microsoft_Singularity_ThreadContext@@0@Z| EQU 1
|defining ?g_CollectBodyTransition@Class_System_GC@@SIXPAUClass_System_Threading_Thread@@H@Z| EQU 1
|defining ?g_setStopContext@Class_System_Threading_Thread@@SAXPAU1@PAUClass_System_Exception@@@Z| EQU 1

PAGE_BITS   EQU     12

        include hal.inc

        MACRO
        BREAKPOINT
        ;; bkpt    0xffff
        swi     0xffff03
        MEND


; static void __fastcall VTable.ssbRecordWriteBarrier(void*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; pushStackMark: If a function may be called by C, push a pointer to its
; frame on to a stack at the beginning of the function.
;
; Transition record layout:
;
; (lower addresses)
; --------------------------
; |Old stack marker record |
; --------------------------
; |Addr of call instr      |
; --------------------------
; |Bottom of stack frame   |
; --------------------------
; |r4                      |
; --------------------------
; |r5                      |
; --------------------------
; |r6                      |
; --------------------------
; |r7                      |
; --------------------------
; |r8                      |
; --------------------------
; |r9                      |
; --------------------------
; |r10                     |
; --------------------------
; |r11                     |
; --------------------------
; (higher addresses);
;

    EXPORT __pushStackMark
    NESTED_ENTRY __pushStackMark

        stmdb sp!, {lr}
        sub sp, sp, #16 ; Space to save r0-r3

    PROLOG_END

        ;; Save the callee-save registers in the transition record.
        ;; Since the transition record is located immediately below the FP,
        ;; we index off the FP rather than the pointer to the struct itself.
        stmdb fp, {r4-r11}         ; Store callee-save registers in record
        ;; From this point forward, we use r8, r9, and r10 as temps.
        ;; R12 may hold the address of the call
        ;; TransitionRecord *newRecord(r9) = FP - sizeof(TransitionRecord);
        sub r9, fp, #|Struct_System_GCs_CallStack_TransitionRecord___SIZE|

        ;; link new stack marker into chain starting at CurrentThread
        ;; ThreadContext *currentThread(r10) = Thread.CurrentThread()
        GET_THREAD_ADDR r10, r8
        ldr     r10, [r10]       ; GET_THREAD_ADDR returns ThreadContext**

        ;; Get the old transition record (r8)
        ldr r8, [r10, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]

        ;; newRecord(r9)->oldTransitionRecord = oldRecord(r8)
        str r8, [r9, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]

        ;; Set the new transition record
        str r9, [r10, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]

        ;; newRecord(r9)->callAddr = return address of this call (lr).
        str lr, [r9, #|Struct_System_GCs_CallStack_TransitionRecord___callAddr|]
        ;; newRecord(r9)->stackBottom = bottom of stack frame (sp)
        str sp, [r9, #|Struct_System_GCs_CallStack_TransitionRecord___stackBottom|]

        ; r0 = &threadContext->gcStates;
        stmia sp, {r0-r3}
        add r0, r10, #|Struct_Microsoft_Singularity_ThreadContext___gcStates|

        ldr r7, =0x800360a0
        cmp r0, r7
        bne NotTheRightThreadInPush
        BREAKPOINT
NotTheRightThreadInPush

        ;; Temp hack -- certain threads on ARM are not getting initialized like
        ;; they do on x86 -- the gcStates field is still 0 at first...
        mov r1, #|Class_System_GCs_Transitions_MutatorState| + |Class_System_GCs_Transitions_OtherDormantState|
        mov r2, #0
        mov r8, r0 ;; save r0 for the next call to CompareExchange
        ;;; uint32 InterlockedCompareExchange(uint32 * dst, uint32 exc, uint32 cmp)
        bl |?g_CompareExchange@Class_System_Threading_Interlocked@@SAIPAIII@Z|
        mov r0, r8 ;; restore r0 for the next call to CompareExchange
        ;; End temp hack

        ;; Allow the GC to work while this thread is out
        mov r1, #|Class_System_GCs_Transitions_DormantState| + |Class_System_GCs_Transitions_OtherMutatorState|
        mov r2, #|Class_System_GCs_Transitions_MutatorState| + |Class_System_GCs_Transitions_OtherDormantState|
        ;;; uint32 InterlockedCompareExchange(uint32 * dst, uint32 exc, uint32 cmp)
        bl |?g_CompareExchange@Class_System_Threading_Interlocked@@SAIPAIII@Z|

        ;; We skip the call to g_LeaveManagedSpace if we modified gcStates,
        ;; which is to say that the thread was previously in Mutator.
        cmps r0, #|Class_System_GCs_Transitions_MutatorState| + |Class_System_GCs_Transitions_OtherDormantState|
        ldmia sp, {r0-r3}
        beq pushFastPath

        ;; Get the min thread context
        mov r0, r10

        stmia sp, {r0-r3}
        mov r0, r8
        bl |?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SAXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z|
        ldmia sp, {r0-r3}

pushFastPath
        add sp, sp, #16
        ldmia sp!, {lr}
        ;; Restore registers r7-r10 (and the ummodified r11)
        ldmdb fp, {r7-r11}
        ;; return
        mov pc, lr

    ENTRY_END


;
; popStackMark: pop the pointer before returning from the function
;
    EXPORT __popStackMark
    NESTED_ENTRY __popStackMark

        stmdb sp!, {lr}
        sub sp, sp, #16  ; Space to save r0-r3

    PROLOG_END

        ;; Save the callee-save registers in the transition record.
        ;; Since the transition record is located immediately below the FP,
        ;; we index off the FP rather than the pointer to the struct itself.
        stmdb fp, {r4-r11}         ; Store callee-save registers in record

        ;; From this point forward, we use r7, r8, r9, and r10 as temps.
        ;; R12 may hold the address of the call
        ;; TransitionRecord *newRecord(r9) = FP - sizeof(TransitionRecord);
        sub r9, fp, #|Struct_System_GCs_CallStack_TransitionRecord___SIZE|

        ;; ThreadContext *currentThread(r10) = Thread.CurrentThread()
        GET_THREAD_ADDR r10, r8
        ldr     r10, [r10]       ; GET_THREAD_ADDR returns ThreadContext**

        mov r8, r10

        stmia sp, {r0-r3}   ;; push these here so we can use r0 as a scratch variable

        ; r0 = &threadContext->gcStates;
        add r0, r10, #|Struct_Microsoft_Singularity_ThreadContext___gcStates|

        ldr r7, =0x800360a0
        cmp r0, r7
        bne NotTheRightThreadInPop
        BREAKPOINT
NotTheRightThreadInPop

        ; r1 = *r0;
        ; if (r1 & MutatorState) ReturnToManagedSpace
        ; *r0 = r1;
        ldr  r1, [r0]
        tst r1, #|Class_System_GCs_Transitions_MutatorState|
        bne popFastPath  ;; even if we don't have to call ReturnToManagedSpace, still need to pop r0-r3

        mov r0, r10
        bl |?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SAXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z|
popFastPath
        ldmia sp, {r0-r3}

        ;; TransitionRecord *oldRecord(r8) = newRecord(r9)->oldTransitionRecord
        ldr r7, [r9, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]

        ;; currentThread(r10) = oldRecord(r8)
        str r7, [r10, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]

        ;; Restore callee-save registers from the transition record.
        ;; Since the transition record is located immediately below the FP,
        ;; we index off the FP rather than the pointer to the struct itself.
        add sp, sp, #16
        ldmdb fp, {r4-r11}
        ldmia sp!, {lr}
        ;; Restore registers r7-r10 (and the ummodified r11)
        ldmdb fp, {r7-r11}
        ;; return
        mov pc, lr

    ENTRY_END


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; void CollectBodyTransition(Thread thread, int generation):
;   Save the callee-save registers in a transition record and then call
;   System.GC.CollectBody(thread, generation)
;

;
;  Note: If you modify the amount of stack that this function uses,
;  you MUST make update the StackBound attribute for
;  System.GC.CollectBodyTransition.
;
;  It is conservatively set to 128 bytes.     This includes the frame size
;  for the function + 88 bytes for a possible linked stack call in
;  CollectBody

    EXPORT |?g_CollectBodyTransition@Class_System_GC@@SAXPAUClass_System_Threading_Thread@@H@Z|
    NESTED_ENTRY "?g_CollectBodyTransition@Class_System_GC@@SAXPAUClass_System_Threading_Thread@@H@Z"

        mov r12, sp
        ;; Save the two words of the arguments (only two are in use)
        stmdb sp!, {r0-r1}
        ;; Save the FP, SP, and the LR
        stmdb sp!, {r4-r11, r12, lr}
        ;; Establish the new FP
        sub fp, r12, #8

        ;; TransitionRecord transitionRecord = new TransitionRecord()
        ;; TransitionRecord *newRecord(sp) = &transitionRecord
        ;; The transition record includes the saves.  Sub an extra 8 for the sp and lr
        sub sp, fp, #|Struct_System_GCs_CallStack_TransitionRecord___SIZE|
        sub sp, sp, #8
    PROLOG_END

        ;; ThreadContext* context(10)
    IF :DEF:SINGULARITY_KERNEL
        add r10, r0, #|Class_System_Threading_Thread___context|
    ELSE ; SINGULARITY_KERNEL
        ldr r10, [r0, #|Class_System_Threading_Thread___context|]
    ENDIF ; SINGULARITY_KERNEL
    
        ;; Get the old transition record (r9)
        ldr r9, [r10, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]

        ;; newRecord(sp)->oldTransitionRecord = oldRecord(r9)
        str r9, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]

        ;; Set the new transition record
        str sp, [r10, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]

        ;; newRecord(sp)->callAddr = return address of this call (lr).
        str lr, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___callAddr|]
        ;; newRecord(sp)->stackBottom = bottom of stack frame (r12)
        str r12, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___stackBottom|]
        ;; Thread *currentThread(r0) = System.GC.CollectBody(r0, r1)
        bl |?g_CollectBody@Class_System_GC@@SAPAUClass_System_Threading_Thread@@PAU2@H@Z|
        ;; TransitionRecord *newRecord(sp) = &transitionRecord
        ;; TransitionRecord *oldRecord(r9) = newRecord(sp)->oldTransitionRecord
        ldr r9, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]

        ;; Restore the old transition record
        str r9, [r10, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]

        ;; Restore permanents, FP, SP, and return
        ldmdb fp, {r4-r11, sp, pc}

    ENTRY_END


    IF :DEF:SINGULARITY_KERNEL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;  void Thread.setStopContext(Thread t, Exception exn)
;
    EXPORT |?g_setStopContext@Class_System_Threading_Thread@@SAXPAU1@PAUClass_System_Exception@@@Z|
    NESTED_ENTRY "?g_setStopContext@Class_System_Threading_Thread@@SAXPAU1@PAUClass_System_Exception@@@Z"

        mov     r12, sp
        stmdb   sp!, {r8-r11, r12, lr}

    PROLOG_END

        BREAKPOINT
        ldr r8, [r0, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]

        ;; TODO -- Actually implement this???

        ;; Epilog & restore all registers
        ldmia   sp!, {r8-r11, sp, lr}
        bx      lr
    ENTRY_END
    ENDIF ;; SINGULARITY_KERNEL


    IF :DEF:SINGULARITY_KERNEL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; void Processor.SwitchToThreadContext(ref ThreadContext oldContext,
;                                      ref ThreadContext newContext);
;
; precondition: Scheduler.dispatchLock held
;
    IMPORT |?g_SwitchToThreadContextNoGC@Class_Microsoft_Singularity_Processor@@SAXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z|

    NESTED_ENTRY ?g_SwitchToThreadContext@Class_Microsoft_Singularity_Processor@@SAXPAUStruct_Microsoft_Singularity_ThreadContext@@0@Z

        mov     r12, sp
        stmdb   sp!, {r4-r11, r12, lr}
        sub     sp, sp, #12            ;; Extra room for additional TR fields

    PROLOG_END

        ;; Store SP and LR
        str     r12, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___stackBottom|]
        str     lr, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___callAddr|]

        ;; Link in the new record
        ldr     r6, [r0, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]
        str     r6, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]
        str     sp, [r0, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]

        ;; Save the contexts
        mov     r4, r0
        mov     r5, r1

        ;; Suspend/Revive the thread around switching context
        bl      |?g_SuspendThread@Class_System_GCs_Transitions@@SAXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z|
        mov     r0, r5
        bl      |?g_SwitchToThreadContextNoGC@Class_Microsoft_Singularity_Processor@@SAXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z|
        mov     r0, r4
        bl      |?g_ReviveThread@Class_System_GCs_Transitions@@SAXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z|

        ;; Unlink the transition record
        ldr     r6, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]
        str     r6, [r4, #|Struct_Microsoft_Singularity_ThreadContext___stackMarkers|]

        ;; Epilog & restore all registers
        add     sp, sp, #12
        ldmia   sp!, {r4-r11, sp, lr}
        bx      lr
    NESTED_END

    ENDIF ;; SINGULARITY_KERNEL

    END
