;
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

include core.inc

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
        push        ecx
        push        edx
        mov         ecx, edx
        call        ?g_IsUnlinkStack@Class_System_Exception@@SI_NPAUuintPtr@@@Z
        pop         edx
        pop         ecx
        test        al, al      
        je          normal
        mov         eax, ecx                       ; save exception type
        mov         ecx, edx            
        mov         edx, [ebp+4]                   ; save the return addr in caller
        mov         [ebp+4], afterUnlinkStack      ; override return addr to instr after
        jmp         ecx                            ; unlink stack which saves eax, edx
afterUnlinkStack:      
        mov         ecx, eax                       ; restore return addr in caller
normal:
        ; Have we reached a kernel->process or process->kernel boundary?
        ; Call Exception.CheckKernelProcessBoundary(esp, ebp, exception)
        push        ecx
        push        edx
        push        ecx      ; arg 3 (exception)
        mov         ecx, esp ; arg 2 (ebp)
        mov         edx, ebp ; arg 1 (esp)
        call        ?g_CheckKernelProcessBoundary@Class_System_Threading_Thread@@SIPAUuintPtr@@PAU2@0PAUClass_System_Exception@@@Z
        pop         edx
        pop         ecx
        ; A non-zero return value means we reached a boundary.
        test        eax, eax      
        jz          normal2
ifdef SINGULARITY_PROCESS
        ;; The process's exception reached the kernel's frames.
        ; Return gracefully to the kernel (i.e. jump to the kernel's
        ;   return address), and the kernel's popStackMark
        ;   will check uncaughtFlag and throw a new exception.
        jmp edx
endif ; SINGULARITY_PROCESS
ifdef SINGULARITY_KERNEL
; There are 3 control paths that merge here:
;  (1) When Thread.cs stops a process mode thread, it sets eip to point here.
;  (2) When Thread.cs stops a blocked kernel thread, it sets eip to point here.
;  (3) The stack unwinder falls through to this case when a kernel exception
;      reaches a process's frames.
; For control path (3), a finally block puts us in a GC safe state
; just before we reach here.
; We also expect to be in the GC safe state most of the
; time for control paths (1) and (2), but
; because pushStackMark and popStackMark are not atomic operations,
; we cannot be 100% sure that we're in the GC safe state.
;   eax: kernel->process or kernel->kernel marker
;   ecx: exception
__throwBeyondMarker LABEL NEAR
        push ecx
        push eax
        ; Leave the GC safe state (if we're actually in it)
        call ?g_RestoreMutatorControlIfNeeded@Class_System_GCs_Transitions@@SIXXZ
        pop eax
        pop ecx
;   eax: kernel->process or kernel->kernel marker
;   ecx: exception
        ; Restore state from the marker, skipping over any intermediate frames.
        ; Keep the original exception in ecx.
        ; Get the return address for the frame beyond the marker into edx:
        mov         edx, dword ptr [eax].Struct_System_GCs_CallStack_TransitionRecord._stackBottom
        mov         edx, dword ptr [edx - 4]
        ; Restore the kernel's ebx, edi, esi, ebp from the marker:
        mov         ebx, dword ptr [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX
        mov         edi, dword ptr [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI
        mov         esi, dword ptr [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI
        mov         ebp, dword ptr [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP
        ; Keep a copy of transition record (eax) and oldTransitionRecord
        push        eax
        push        dword ptr [eax].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord
        ; Read _stackBottom (the new esp) from the kernel->process marker:
        mov         eax, dword ptr [eax].Struct_System_GCs_CallStack_TransitionRecord._stackBottom
        ; Save ecx, edx to new stack -- this may overwrite the transition record,
        ; so don't read any more fields from the transition record after this point.
        mov         [eax - 4], ecx  ; (exception)
        mov         [eax - 8], edx  ; (return address)
        ; Set up the two arguments to DiscardStackSegments
        pop         edx  ; (oldTransitionRecord)
        pop         ecx  ; (marker)
        ; Restore the kernel's esp from the kernel->process marker:
        lea         esp, [eax - 8]
        ; Free any stack segments that we skipped over:
        ;; TODO: are we sure there's enough stack space to call this?
        call        ?g_DiscardSkippedStackSegments@Class_System_Threading_Thread@@SIXPAUStruct_System_GCs_CallStack_TransitionRecord@@0@Z
        pop         edx  ; (return address)
        pop         ecx  ; (exception)
endif ; SINGULARITY_KERNEL
normal2:
        jmp         __throwDispatcherExplicitAddrAfterCore
__throwDispatcherExplicitAddrAfter endp



ifdef SINGULARITY_KERNEL
;
;  void Thread.setStopContext(Thread t, Exception exn)
;

align 16
?g_setStopContext@Class_System_Threading_Thread@@SIXPAU1@PAUClass_System_Exception@@@Z proc
        ; ecx = ecx.context
        add ecx, Class_System_Threading_Thread._context
        ; context.eip = __throwBeyondMarker
        ; context.ecx = processStopException
        ; context.eax = context.stackMarkers
        mov     [ecx].Struct_Microsoft_Singularity_ThreadContext._threadRecord._spill._ip, __throwBeyondMarker
        mov     [ecx].Struct_Microsoft_Singularity_ThreadContext._threadRecord._spill._cx, edx
        mov     eax, [ecx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers
        mov     [ecx].Struct_Microsoft_Singularity_ThreadContext._threadRecord._spill._ax, eax
        ret
?g_setStopContext@Class_System_Threading_Thread@@SIXPAU1@PAUClass_System_Exception@@@Z endp

endif ; SINGULARITY_KERNEL

?g_ZeroPages@Class_System_Buffer@@SIXPAEH@Z proc
        ;; ECX = dst
        ;; EDX = len (bytes)
        
        push    ebp
        mov     ebp, esp
        pxor    mm0, mm0
next:
        movntq  [ecx + 0], mm0
        movntq  [ecx + 8], mm0
        movntq  [ecx + 16], mm0
        movntq  [ecx + 24], mm0
        movntq  [ecx + 32], mm0
        movntq  [ecx + 40], mm0
        movntq  [ecx + 48], mm0
        movntq  [ecx + 56], mm0
        add     ecx, 64
        sub     edx, 64
        ja      next
        
        sfence
        emms
        pop     ebp
        ret
?g_ZeroPages@Class_System_Buffer@@SIXPAEH@Z endp

?g_CopyPages@Class_System_Buffer@@SIXPAE0H@Z proc
        ;; ECX = dst
        ;; EDX = src
        ;; [ebp+8]  len (bytes)
        
        push    ebp
        mov     ebp, esp
        mov     eax, [ebp + 8]

        cmp     ecx, edx
        js      down

        ;; destination is lower than source
        add     ecx, eax
        add     edx, eax
        sub     ecx, 64
        sub     edx, 64
         
up:
        movq    mm0, [edx +  0]
        movq    mm1, [edx +  8]
        movq    mm2, [edx + 16]
        movq    mm3, [edx + 24]
        movq    mm4, [edx + 32]
        movq    mm5, [edx + 40]
        movq    mm6, [edx + 48]
        movq    mm7, [edx + 56]
        movntq  [ecx +  0], mm0
        movntq  [ecx +  8], mm1
        movntq  [ecx + 16], mm2
        movntq  [ecx + 24], mm3
        movntq  [ecx + 32], mm4
        movntq  [ecx + 40], mm5
        movntq  [ecx + 48], mm6
        movntq  [ecx + 56], mm7
        sub     ecx, 64
        sub     edx, 64
        sub     eax, 64
        ja      up

        sfence
        emms
        pop     ebp
        ret     4
        
        ;; destination is higher than source
down:
        movq    mm0, [edx +  0]
        movq    mm1, [edx +  8]
        movq    mm2, [edx + 16]
        movq    mm3, [edx + 24]
        movq    mm4, [edx + 32]
        movq    mm5, [edx + 40]
        movq    mm6, [edx + 48]
        movq    mm7, [edx + 56]
        movntq  [ecx +  0], mm0
        movntq  [ecx +  8], mm1
        movntq  [ecx + 16], mm2
        movntq  [ecx + 24], mm3
        movntq  [ecx + 32], mm4
        movntq  [ecx + 40], mm5
        movntq  [ecx + 48], mm6
        movntq  [ecx + 56], mm7
        add     ecx, 64
        add     edx, 64
        sub     eax, 64
        ja      down

        sfence
        emms
        pop     ebp
        ret     4
?g_CopyPages@Class_System_Buffer@@SIXPAE0H@Z endp

end
