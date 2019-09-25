; 
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

include core.inc

externdef __throwDispatcherExplicitAddrAfter:NEAR
externdef __throwDispatcherExplicitAddrAfterCore:NEAR

;
;  __throwDispatcherExplictAddrAfter (ecx=exception, edx=throwAddress)
;
; Description:
;    This is to be used when the address of the instruction immediately after
;    the one that actually threw the exception is passed as an argument.
;
; Arguments:
;    ecx = pointer to exception object being thrown
;    edx = address of the instruction following the one where
;          the exception was thrown
;
; This is used, for example, in stack unwinding, where edx is the
; return address on the stack for the current procedure. 
;
; Stack unwinding occurs when the current procedure does not have a handler
; for the routine.   The idea is to pop the stack frame and treat the call
; instruction in the caller as though it threw.    We only have the return
; address, though, which points to the instruction *after* the call.   
;

align 16
__throwDispatcherExplicitAddrAfter proc 
        push        rcx
        push        rdx
        mov         rcx, rdx
        call        ?g_IsUnlinkStack@Class_System_Exception@@SA_NPEAUuintPtr@@@Z
        pop         rdx
        pop         rcx
        test        al, al      
        je          normal
        mov         rax, rcx                       ; save exception type
        mov         rcx, rdx            
        mov         rdx, [rbp+8]                   ; save the return addr in caller
        push        rax
        mov         rax, afterUnlinkStack
        mov         [rbp+8], rax      ; override return addr to instr after
        pop         rax
        jmp         rcx                            ; unlink stack which saves eax, edx
afterUnlinkStack:      
        mov         rcx, rax                       ; restore return addr in caller
normal:
        jmp         __throwDispatcherExplicitAddrAfterCore
__throwDispatcherExplicitAddrAfter endp

ifdef SINGULARITY_KERNEL
; There are 3 control paths that merge here:
;  (1) When Thread.cs stops a process mode thread, it sets eip to point here.
;  (2) When Thread.cs stops a blocked kernel thread, it sets eip to point here.
;  (3) The stack unwinder falls through to this case when a kernel exception
;      reaches a process's frames.
; For control path (3), a finally block puts us in a gc safe state
; just before we reach here.
; We also expect to be in the gc safe state most of the
; time for control paths (1) and (2), but
; because pushStackMark and popStackMark are not atomic operations,
; we cannot be 100% sure that we're in the gc safe state.
;   eax: kernel->process or kernel->kernel marker
;   ecx: exception
__throwBeyondMarker LABEL NEAR
        push rcx
        push rax
        ; Leave the gc safe state (if we're actually in it)
        call ?g_RestoreMutatorControlIfNeeded@Class_System_GCs_Transitions@@SAXXZ
        pop rax
        pop rcx
;   eax: kernel->process or kernel->kernel marker
;   ecx: exception
        ; Restore state from the marker, skipping over any intermediate frames.
        ; Keep the original exception in ecx.
        ; Get the return address for the frame beyond the marker into edx:
        mov         rdx, qword ptr [rax].Struct_System_GCs_CallStack_TransitionRecord._stackBottom
        mov         rdx, qword ptr [rdx - 8]
        ; Restore the kernel's ebx, edi, esi, ebp from the marker:
        mov         rbx, qword ptr [rax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX
        mov         rdi, qword ptr [rax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI
        mov         rsi, qword ptr [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI
        mov         rbp, qword ptr [rax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP
        ; Keep a copy of transition record (eax) and oldTransitionRecord
        push        rax
        push        qword ptr [rax].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord
        ; Read _stackBottom (the new esp) from the kernel->process marker:
        mov         rax, qword ptr [rax].Struct_System_GCs_CallStack_TransitionRecord._stackBottom
        ; Save ecx, edx to new stack -- this may overwrite the transition record,
        ; so don't read any more fields from the transition record after this point.
        mov         [rax - 8], ecx  ; (exception)
        mov         [rax - 16], edx  ; (return address)
        ; Set up the two arguments to DiscardStackSegments
        pop         rdx  ; (oldTransitionRecord)
        pop         rcx  ; (marker)
        ; Restore the kernel's esp from the kernel->process marker:
        lea         rsp, [rax - 16]
        ; Free any stack segments that we skipped over:
        ;; TODO: are we sure there's enough stack space to call this?
        call        ?g_DiscardSkippedStackSegments@Class_System_Threading_Thread@@SAXPEAUStruct_System_GCs_CallStack_TransitionRecord@@0@Z
        pop         rdx  ; (return address)
        pop         rcx  ; (exception)

;
;  void Thread.setStopContext(Thread t, Exception exn)
;

align 16

?g_setStopContext@Class_System_Threading_Thread@@SAXPEAU1@PEAUClass_System_Exception@@@Z proc frame
        PrologPush  rbp          ; create ebp chain entry
        SetFramePointer rbp      ; set new ebp
        .endprolog
        ; rcx = rcx.context
        add rcx, Class_System_Threading_Thread._context
        ; context.eip = __throwBeyondMarker
        ; context.ecx = processStopException
        ; context.eax = context.stackMarkers
        mov     rax, __throwBeyondMarker
        mov     [rcx].Struct_Microsoft_Singularity_ThreadContext._threadRecord._spill._ip, rax
        mov     [rcx].Struct_Microsoft_Singularity_ThreadContext._threadRecord._spill._cx, rdx
        mov     rax, [rcx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers
        mov     [rcx].Struct_Microsoft_Singularity_ThreadContext._threadRecord._spill._ax, rax
        ; Epilogue
        mov esp, ebp
        pop rbp;
        ret
?g_setStopContext@Class_System_Threading_Thread@@SAXPEAU1@PEAUClass_System_Exception@@@Z endp

endif ; SINGULARITY_KERNEL


?g_ZeroPages@Class_System_Buffer@@SAXPEAEH@Z proc frame
        ;; ECX = dst
        ;; EDX = len (bytes)
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        pxor    mm0, mm0
next:
        movntq  [rcx + 0], mm0
        movntq  [rcx + 8], mm0
        movntq  [rcx + 16], mm0
        movntq  [rcx + 24], mm0
        movntq  [rcx + 32], mm0
        movntq  [rcx + 40], mm0
        movntq  [rcx + 48], mm0
        movntq  [rcx + 56], mm0
        add     rcx, 64
        sub     rdx, 64
        ja      next

        sfence
        emms
        pop     rbp
        ret
?g_ZeroPages@Class_System_Buffer@@SAXPEAEH@Z endp

?g_CopyPages@Class_System_Buffer@@SAXPEAE0H@Z proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog

        ;; RCX = dst
        ;; RX  = src
        ;; r8  = len (bytes)

        mov     rax, r8

        cmp     rcx, rdx
        js      down

        ;; destination is lower than source
        add     rcx, rax
        add     rdx, rax
        sub     rcx, 64
        sub     rdx, 64

up:
        movq    mm0, [rdx +  0]
        movq    mm1, [rdx +  8]
        movq    mm2, [rdx + 16]
        movq    mm3, [rdx + 24]
        movq    mm4, [rdx + 32]
        movq    mm5, [rdx + 40]
        movq    mm6, [rdx + 48]
        movq    mm7, [rdx + 56]
        movntq  [rcx +  0], mm0
        movntq  [rcx +  8], mm1
        movntq  [rcx + 16], mm2
        movntq  [rcx + 24], mm3
        movntq  [rcx + 32], mm4
        movntq  [rcx + 40], mm5
        movntq  [rcx + 48], mm6
        movntq  [rcx + 56], mm7
        sub     rcx, 64
        sub     rdx, 64
        sub     rax, 64
        ja      up

        sfence
        emms
        pop     rbp
        ret

        ;; destination is higher than source
down:
        movq    mm0, [rdx +  0]
        movq    mm1, [rdx +  8]
        movq    mm2, [rdx + 16]
        movq    mm3, [rdx + 24]
        movq    mm4, [rdx + 32]
        movq    mm5, [rdx + 40]
        movq    mm6, [rdx + 48]
        movq    mm7, [rdx + 56]
        movntq  [rcx +  0], mm0
        movntq  [rcx +  8], mm1
        movntq  [rcx + 16], mm2
        movntq  [rcx + 24], mm3
        movntq  [rcx + 32], mm4
        movntq  [rcx + 40], mm5
        movntq  [rcx + 48], mm6
        movntq  [rcx + 56], mm7
        add     rcx, 64
        add     rdx, 64
        sub     rax, 64
        ja      down

        sfence
        emms
        pop     rbp
        ret
?g_CopyPages@Class_System_Buffer@@SAXPEAE0H@Z endp

extern ?brtmain@@3P6AHPEAUClassVector_Class_System_String@@@ZEA:qword

align 16
?g_CallMain@Class_Microsoft_Singularity_AppRuntime@@SAHPEAUClassVector_Class_System_String@@@Z proc
        jmp     qword ptr [?brtmain@@3P6AHPEAUClassVector_Class_System_String@@@ZEA]
?g_CallMain@Class_Microsoft_Singularity_AppRuntime@@SAHPEAUClassVector_Class_System_String@@@Z endp

end
