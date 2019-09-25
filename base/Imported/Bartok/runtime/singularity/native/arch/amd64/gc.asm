;; ----------------------------------------------------------------------------
;;
;;  Copyright (c) Microsoft Corporation.  All rights reserved.
;;
;; ----------------------------------------------------------------------------

.code

include hal.inc

PAGE_BITS               EQU     12
MASK_OWNER              EQU     03h

extern ?g_CollectBody@Class_System_GC@@SAPEAUClass_System_Threading_Thread@@PEAU2@H@Z:proc
externdef ?g_CollectBody@Class_System_GC@@SAPEAUClass_System_Threading_Thread@@PEAU2@H@Z:NEAR
; static void __fastcall GC.CollectBody(Thread, int)

ifdef SINGULARITY
externdef ?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SAXPEAUStruct_Microsoft_Singularity_X86_ThreadContext@@@Z:NEAR
externdef ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SAXPEAUStruct_Microsoft_Singularity_X86_ThreadContext@@@Z:NEAR
else
externdef ?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SAXPEAUClass_System_Threading_Thread@@@Z:NEAR
externdef ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SAPEAUClass_System_Threading_Thread@@H@Z:NEAR
endif

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
; |rbx                     |
; --------------------------
; |rdi                     |
; --------------------------
; |rsi                     |
; --------------------------
; |rbp                     |
; --------------------------
; (higher addresses);
;

align 16
__pushStackMark proc frame
        ; save caller-save registers
        PrologPush rax
        PrologPush rcx
        PrologPush rdx
        PrologPush r8
        PrologPush r9
        PrologPush r10
        PrologPush r11
        .endprolog
        lea  rcx, [rbp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)]           ; calculate new stack marker address
ifdef SINGULARITY
        CurrentThreadContext(rax)           ; get current threadcontext
        mov  rdx, [eax].Struct_Microsoft_Singularity_ThreadContext._stackMarkers ;save old stack marker address
else
        CurrentThread rax,eax, rdx           ; get current thread
        mov  rdx, [rax].Class_System_Threading_Thread._asmStackMarker ;save old stack marker address
endif
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord, rdx
ifdef SINGULARITY
        mov  [rax].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, rcx ; update thread record field
else
        mov  [rax].Class_System_Threading_Thread._asmStackMarker,rcx                 ; update thread record field
endif
    ;; REVIEWx64: x86=12, x64=56, symbolic value maybe?
        mov  rdx, [rsp+56]  ; load return address of this call
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._callAddr,rdx
    ;; REVIEWx64: x86=16, x64=64, symbolic value maybe?
        lea  rdx, [rsp+64]
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._stackBottom, rdx    ; save bottom of stack frame
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX, rbx            ; save callee-save registers
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI, rdi
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI, rsi
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP, rbp
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R12, r12
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R13, r13
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R14, r14
        mov  [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R15, r15
        mov  rcx, rax
ifdef SINGULARITY
        call ?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SAXPEAUStruct_Microsoft_Singularity_ThreadContext@@@Z
else
        call ?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SAXPEAUClass_System_Threading_Thread@@@Z
endif
        pop  r11
        pop  r10
        pop  r9
        pop  r8
        pop  rdx
        pop  rcx
        pop  rax
        ret
__pushStackMark endp


;
; popStackMark: pop the pointer before returning from the function
;
align 16
__popStackMark proc frame
        ; save caller-save registers
        PrologPush rax
        PrologPush rcx
        PrologPush rdx
        PrologPush r8
        PrologPush r9
        PrologPush r10
        PrologPush r11
        .endprolog
ifdef SINGULARITY
        CurrentThreadContext rcx      ; get current thread
        call ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SAXPEAUStruct_Microsoft_Singularity_ThreadContext@@@Z
        CurrentThreadContext(rax)      ; get current thread
else
        CurrentThreadIndex rax,eax, rcx     ; get current thread
        mov rcx, rax
        call ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SAPEAUClass_System_Threading_Thread@@H@Z
endif
        lea rcx, [rbp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)]
        mov rdx, [rcx].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord ; get old stack marker value
ifdef SINGULARITY
        mov [rax].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, rdx; update thread record field
else
        mov [rax].Class_System_Threading_Thread._asmStackMarker, rdx; update thread record field
endif
        mov rbx, [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX   ; restore callee-save registers
        mov rdi, [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI
        mov rsi, [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI
        mov rbp, [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP
        mov r12, [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R12
        mov r13, [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R13
        mov r14, [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R14
        mov r15, [rcx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R15
        pop r11
        pop r10
        pop r9
        pop r8
        pop rdx                      ; restore caller-save registers
        pop rcx
        pop rax
        ret
__popStackMark endp

;++
;
; Routine Description:
;
;     This routine creates and links a new transition record containig all callee-saved
;     registers, invokes System.GC.CollectBody, and then removes the transition record.
;
; Arguments:
;
;     Thread (rcx)      - Supplies the current thread.
;
;     Generation (rdx)  - Supplies generation.
;
; Return Value:
;
;     None.
;
;--

align 16
?g_CollectBodyTransition@Class_System_GC@@SAXPEAUClass_System_Threading_Thread@@H@Z proc frame

;
; Create frame.
;

        PrologPush rbp
        SetFramePointer rbp
        .endprolog

;
; Allocate a transition record on the stack.
;

        sub     rsp, (size Struct_System_GCs_CallStack_TransitionRecord) + 32
        and     rsp, NOT 0Fh

;
; Save arguments.
;

        push    rcx
        push    rdx

;
; Calculate the address of the transition record.
;

        lea     rdx, qword ptr [rbp - (size Struct_System_GCs_CallStack_TransitionRecord)]

;
; Get the current stack marker.
;

ifdef SINGULARITY_KERNEL

        mov     rax, qword ptr [rcx].Class_System_Threading_Thread._context.Struct_Microsoft_Singularity_ThreadContext._stackMarkers

else

        mov     rax, qword ptr [rcx].Class_System_Threading_Thread._context
        mov     rax, qword ptr [rax].Struct_Microsoft_Singularity_ThreadContext._stackMarkers

endif

;
; Initialize new transition record.
;

        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord, rax

        mov     rax, qword ptr [rbp + 8]
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._callAddr, rax

        lea     rax, qword ptr [rbp + 16]

        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._stackBottom, rax
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX, rbx
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI, rdi
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI, rsi
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R12, r12
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R13, r13
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R14, r14
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R15, r15

        mov     rax, qword ptr [rbp]
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP, rax

;
; Set new stack marker.
;

ifdef SINGULARITY_KERNEL

        mov     qword ptr [rcx].Class_System_Threading_Thread._context.Struct_Microsoft_Singularity_ThreadContext._stackMarkers, rdx

else

        mov     rax, qword ptr [rcx].Class_System_Threading_Thread._context
        mov     qword ptr [rax].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, rdx

endif

;
; Restore arguments
;

        pop     rdx
        pop     rcx

ifdef DEBUG

;
; Check if the stack pointer is properly aligned.
;

        mov     rax, rsp
        and     rax, 08h
        cmp     rax, 0
        je      @F

        int     3

@@:

endif

;
; Invoke System.GC.CollectBody, which returns the current thread address.
;

        call    ?g_CollectBody@Class_System_GC@@SAPEAUClass_System_Threading_Thread@@PEAU2@H@Z

;
; Restore previous stack marker.
;

        lea     rdx, qword ptr [rbp - (size Struct_System_GCs_CallStack_TransitionRecord)]
        mov     rcx, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord

ifdef SINGULARITY_KERNEL

        mov     qword ptr [rax].Class_System_Threading_Thread._context.Struct_Microsoft_Singularity_ThreadContext._stackMarkers, rcx

else

        mov     rax, qword ptr [rax].Class_System_Threading_Thread._context
        mov     qword ptr [rax].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, rcx

endif

;
; Restore all callee-saved registers from the transition record.
;

        ; NOTE: DO NOT restore rbp direct, otherwise upon return we will
        ; skip a frame.  Instead, restore value to the rbp stack slot.
        mov     rbx, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP
        mov     qword ptr [rbp], rbx

        mov     rbx, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX
        mov     rsi, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI
        mov     r12, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R12
        mov     r13, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R13
        mov     r14, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R14
        mov     r15, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R15
        mov     rdi, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI

        mov     rsp, rbp
        pop     rbp
        ret

?g_CollectBodyTransition@Class_System_GC@@SAXPEAUClass_System_Threading_Thread@@H@Z endp

ifdef SINGULARITY_KERNEL

;++
;
; Routine Description:
;
;     This routine suspends GC for the old context, switches to and revives GC for the new context.
;
; Arguments:
;
;     OldContext (rcx)  - Supplies the old context.
;
;     NewContext (rdx)  - Supplies the new context.
;
; Return Value:
;
;     None.
;
;--

align 16
?g_SwitchToThreadContext@Class_Microsoft_Singularity_Processor@@SAXPEAUStruct_Microsoft_Singularity_ThreadContext@@0@Z proc frame

SwapGCContext label byte

;
; Prepare call frame.
;

        PrologPush rbp
        SetFramePointer rbp
        .endprolog

;
; Allocate a transition record on the stack.
;

        sub     rsp, (size Struct_System_GCs_CallStack_TransitionRecord) + 16 + 32
        and     rsp, NOT 0Fh
        
;
; Save arguments.
;

        mov     qword ptr [rbp - (size Struct_System_GCs_CallStack_TransitionRecord) - 16], rcx
        mov     qword ptr [rbp - (size Struct_System_GCs_CallStack_TransitionRecord) - 8], rdx

;
; Calculate the address of the transition record.
;

        lea     rdx, qword ptr [rbp - (size Struct_System_GCs_CallStack_TransitionRecord)]

;
; Get the current stack marker.
;

        mov     rax, qword ptr [rcx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers

;
; Initialize new transition record.
;

        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord, rax

        mov     rax, qword ptr [rbp + 8]
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._callAddr, rax

        lea     rax, qword ptr [rbp + 16]
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._stackBottom, rax

        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX, rbx
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI, rdi
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI, rsi
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R12, r12
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R13, r13
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R14, r14
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R15, r15

        mov     rax, qword ptr [rbp]
        mov     qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP, rax

;
; Set new stack marker.
;

        mov     qword ptr [rcx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, rdx

;
; Suspend GC for the old thread.
;

        call    ?g_SuspendThread@Class_System_GCs_Transitions@@SAXPEAUStruct_Microsoft_Singularity_ThreadContext@@@Z

;
; Switch context.
;

        mov     rcx, qword ptr [rbp - (size Struct_System_GCs_CallStack_TransitionRecord) - 8]
        call    ?g_SwitchToThreadContextNoGC@Class_Microsoft_Singularity_Processor@@SAXPEAUStruct_Microsoft_Singularity_ThreadContext@@@Z

;
; Revive GC.
;

        mov     rcx, qword ptr [rbp - (size Struct_System_GCs_CallStack_TransitionRecord) - 16]
        call    ?g_ReviveThread@Class_System_GCs_Transitions@@SAXPEAUStruct_Microsoft_Singularity_ThreadContext@@@Z

;
; Restore previous stack marker.
;

        mov     rcx, qword ptr [rbp - (size Struct_System_GCs_CallStack_TransitionRecord) - 16]
        lea     rdx, qword ptr [rbp - (size Struct_System_GCs_CallStack_TransitionRecord)]

        mov     rax, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord
        mov     qword ptr [rcx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, rax

;
; Restore all callee-saved registers from the transition record.
;

        mov     rbx, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX
        mov     rsi, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI
        mov     rbp, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP
        mov     r12, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R12
        mov     r13, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R13
        mov     r14, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R14
        mov     r15, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._R15
        mov     rdi, qword ptr [rdx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI

        mov     rsp, rbp
        pop     rbp
        ret

?g_SwitchToThreadContext@Class_Microsoft_Singularity_Processor@@SAXPEAUStruct_Microsoft_Singularity_ThreadContext@@0@Z endp

public SwapGCContext

endif

end
