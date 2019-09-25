;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

include hal.inc

PAGE_BITS               EQU     12
MASK_OWNER              EQU     03h

externdef ?g_ssbRecordWriteBarrier@Class_System_VTable@@SIXPAUUntracedPtr_void@@@Z:NEAR

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
; |ebx                     |
; --------------------------
; |edi                     |
; --------------------------
; |esi                     |
; --------------------------
; |ebp                     |
; --------------------------
; (higher addresses);
;

align 16
__pushStackMark proc
        ;; Free up a register
        push ecx
        ;; Fill the new transition record
        lea  ecx, [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)]
        ;; Stash the callee-save registers
        mov  [ecx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX, ebx
        mov  [ecx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI, edi
        mov  [ecx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI, esi
        mov  [ecx].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP, ebp
        ;; record.callAddr = <return addr of this call>
        mov  ebx, [esp+4]
        mov  [ecx].Struct_System_GCs_CallStack_TransitionRecord._callAddr, ebx
        ;; record.stackBottom = <bottom of stack frame>
        lea  ebx, [esp+8]
        mov  [ecx].Struct_System_GCs_CallStack_TransitionRecord._stackBottom, ebx
        
ifdef SINGULARITY
        ;; Link in new transition record
        CurrentThreadContext(ebx)
        mov  edi, [ebx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers
        mov  [ecx].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord, edi
        ;; The next instruction officially switches modes (process->kernel only).
        ;; Make sure that the transition record is complete at this point.
        mov  [ebx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, ecx
        ;; We are now officially in a different mode.
        ;; Allow the GC to work while this thread is out
        mov ecx, Class_System_GCs_Transitions_DormantState + Class_System_GCs_Transitions_OtherMutatorState
        mov eax, Class_System_GCs_Transitions_MutatorState + Class_System_GCs_Transitions_OtherDormantState
        lock cmpxchg [ebx].Struct_Microsoft_Singularity_ThreadContext._gcStates, ecx
        jz pushFastPath
        ;; Transitions.LeaveManagedSpace(threadContext)
        mov ecx, ebx
        push eax
    push edx
        call ?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SIXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z
    pop  edx
        pop  eax
pushFastPath:
else ; SINGULARITY
        ;; Link in new transition record
        CurrentThread(ebx)
        mov  edi, [ebx].Class_System_Threading_Thread._asmStackMarker
        mov  [ecx].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord, edi
        mov  [ebx].Class_System_Threading_Thread._asmStackMarker, ecx
        ;; Allow the GC to work while this thread is out
    mov ecx, ebx
        push eax
        push edx
        call ?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SIXPAUClass_System_Threading_Thread@@@Z
        pop  edx
        pop  eax
endif ; SINGULARITY
        pop  ecx
        ret
__pushStackMark endp

;
; popStackMark: pop the pointer before returning from the function
;
align 16
__popStackMark proc
        ;; Preserve caller-save registers
        push eax
ifdef SINGULARITY
        CurrentThreadContext(ebx)
        ;; NOTE: replacing the following two instructions with a "test"
        ;; instruction has a 1-cycle penalty!
        mov edi, [ebx].Struct_Microsoft_Singularity_ThreadContext._gcStates
        and edi, Class_System_GCs_Transitions_MutatorState
        jnz popFastPath
    push ecx
        push edx
        mov ecx, ebx
        call ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SIXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z
        pop edx
        pop ecx
popFastPath:
ifndef SINGULARITY_KERNEL
        cmp byte ptr [ebx].Struct_Microsoft_Singularity_ThreadContext._suspendAlert, 0
        je noAlert
        push ecx
        push edx
        call ?g_SuspendBarrier@Struct_Microsoft_Singularity_V1_Processes_ProcessHandle@@SIXXZ
        pop edx
        pop ecx
noAlert:
endif ; SINGULARITY_KERNEL
        ;; Unlink transition record
    lea  edi, [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)]
        mov  esi, [edi].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord
        ;; The next instruction officially switches modes (process<-kernel only).
        mov  [ebx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, esi
        ;; We are now officially in a different mode.
ifdef SINGULARITY_KERNEL
        ;; Assert(ebx == current context)
        ;; Assert(edi == transition record in caller's frame)
        ;; If we're returning to the kernel from a process that threw an
        ;; exception, throw a new kernel exception:
        cmp  byte ptr [ebx].Struct_Microsoft_Singularity_ThreadContext._uncaughtFlag, 0
        je   noProcessUncaughtException
        add  esp, 8   ; discard eax, retaddr
    ;; push TransitionRecord.callAddr as the new return address
        push [edi].Struct_System_GCs_CallStack_TransitionRecord._callAddr
        ;; Restore callee-save registers
        mov  ebx, [edi].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX
        mov  esi, [edi].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI
        mov  ebp, [edi].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP
        mov  edi, [edi].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI
        ;; (We have to jump to the code; a "call" would push a return address
        ;; that doesn't exist in the exception tables.)
        jmp ?g_ThrowProcessUncaughtException@Class_Microsoft_Singularity_ProcessUncaughtException@@SIXXZ
noProcessUncaughtException:
endif ; SINGULARITY_KERNEL
else ; SINGULARITY
    push ecx
        push edx
        CurrentThreadIndex(ecx)      ; get current thread
        call ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SIPAUClass_System_Threading_Thread@@H@Z
    pop edx
        pop ecx
        ;; Unlink transition record
    lea  edi, [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)]
        mov  esi, [edi].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord
        mov  [eax].Class_System_Threading_Thread._asmStackMarker, esi
endif ; SINGULARITY
        ;; Restore callee-save registers
        mov  ebx, [edi].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX
        mov  esi, [edi].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI
        mov  ebp, [edi].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP
        mov  edi, [edi].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI
        ;; Restore caller-save registers and return
        pop eax
        ret
__popStackMark endp

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

.code
align 16
?g_CollectBodyTransition@Class_System_GC@@SIXPAUClass_System_Threading_Thread@@H@Z proc
; static void __fastcall GC.CollectBodyTransition(Thread, int)
        ;; Prologue
        push ebp
        mov ebp, esp
        sub esp, SIZE Struct_System_GCs_CallStack_TransitionRecord
        ;; Fill the new transition record
        mov  eax, dword ptr [ebp+4]   ; return address of this call
        mov  dword ptr [ebp-24], eax
        lea  eax, [ebp+8]             ; skip pushed PC and SP
        mov  dword ptr [ebp-20], eax  ; bottom of stack frame
        mov  dword ptr [ebp-16], ebx  ; callee-save registers
        mov  dword ptr [ebp-12], edi
        mov  dword ptr [ebp-08], esi
        mov  eax, dword ptr [ebp]
        mov  dword ptr [ebp-04], eax   ; old ebp value
        ;; Link in new transition record
        lea  edi, dword ptr [ebp-28]  ;  address of new transition record
ifdef SINGULARITY
ifdef SINGULARITY_KERNEL
        mov  eax, dword ptr [ecx].Class_System_Threading_Thread._context.Struct_Microsoft_Singularity_ThreadContext._stackMarkers
        mov  dword ptr [ecx].Class_System_Threading_Thread._context.Struct_Microsoft_Singularity_ThreadContext._stackMarkers, edi
else
        mov  esi, dword ptr [ecx].Class_System_Threading_Thread._context
        mov  eax, dword ptr [esi].Struct_Microsoft_Singularity_ThreadContext._stackMarkers
        mov  dword ptr [esi].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, edi
endif ; SINGULARITY_KERNEL
else ; SINGULARITY
        mov  eax, dword ptr [ecx].Class_System_Threading_Thread._asmStackMarker
        mov  dword ptr [ecx].Class_System_Threading_Thread._asmStackMarker, edi
endif ; SINGULARITY
        mov  dword ptr [edi], eax     ; add in old transition record chain
        ;; Call "Thread GC.CollectBody(Thread, int)"
        call ?g_CollectBody@Class_System_GC@@SIPAUClass_System_Threading_Thread@@PAU2@H@Z
        ;; Unlink transition record
        mov  edi, dword ptr [ebp-28]   ; get old transition record chain
ifdef SINGULARITY
ifdef SINGULARITY_KERNEL
        mov  dword ptr [eax].Class_System_Threading_Thread._context.Struct_Microsoft_Singularity_ThreadContext._stackMarkers, edi
else
        mov  esi, dword ptr [eax].Class_System_Threading_Thread._context
        mov  dword ptr [esi].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, edi
endif ; SINGULARITY_KERNEL
else ; SINGULARITY
        mov  dword ptr [eax].Class_System_Threading_Thread._asmStackMarker, edi
endif ; SINGULARITY
        ;; Restore callee-save registers
        mov ebx, [ebp-16]    ; restore callee-save regs
        mov edi, [ebp-12]
        mov esi, [ebp-8]
        mov ebp, [ebp-4]
        add esp, (SIZE Struct_System_GCs_CallStack_TransitionRecord)+4 ;  skip FP
        ret
?g_CollectBodyTransition@Class_System_GC@@SIXPAUClass_System_Threading_Thread@@H@Z endp


ifdef SINGULARITY_KERNEL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; void Processor.SwitchToThreadContext(ref X86_ThreadContext oldContext,
;                                      ref X86_ThreadContext newContext);
;
; precondition: Scheduler.dispatchLock held
;
align 16
?g_SwitchToThreadContext@Class_Microsoft_Singularity_Processor@@SIXPAUStruct_Microsoft_Singularity_ThreadContext@@0@Z proc
        ;; Prologue
        push ebp
        mov ebp, esp
        ;; TransitionRecord record;
        ;; <spill slot for oldContext>
        sub esp, SIZE Struct_System_GCs_CallStack_TransitionRecord + 4
        mov [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)-4], ecx
        ;; record.oldTransitionRecord = oldContext.stackMarkers
        mov eax, [ecx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers
        mov [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord, eax
        ;; oldContext.stackMarkers = &record
        lea eax, [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)]
        mov [ecx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, eax
        ;; record.callAddr = <PC from stack frame>
        mov ecx, dword ptr [ebp+4]
        mov [eax].Struct_System_GCs_CallStack_TransitionRecord._callAddr, ecx
        ;; record.stackBottom = <bottom of previous stack frame>
        lea ecx, [ebp+8]        ; Skip pushed PC and SP
        mov [eax].Struct_System_GCs_CallStack_TransitionRecord._stackBottom, ecx
        ;; <Save callee-save registers>
        mov [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX, ebx
        mov [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI, edi
        mov [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI, esi
        mov ecx, dword ptr [ebp]
        mov [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBP, ecx
        ;; Transitions.SuspendThread(oldContext)
        mov ecx, [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)-4]
        mov edi, edx            ; save newContext away in a callee-save reg
        call ?g_SuspendThread@Class_System_GCs_Transitions@@SIXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z
        ;; Processor.SwitchToThreadContextNoGC(newContext)
        mov ecx, edi
        call ?g_SwitchToThreadContextNoGC@Class_Microsoft_Singularity_Processor@@SIXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z
        ;; Transitions.ReviveThread(oldContext)
        mov ecx, [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)-4]
        call ?g_ReviveThread@Class_System_GCs_Transitions@@SIXPAUStruct_Microsoft_Singularity_ThreadContext@@@Z
        ;; <Restore callee-save registers>
        lea eax, [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)]
        mov ebx, [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EBX
        mov edi, [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._EDI
        mov esi, [eax].Struct_System_GCs_CallStack_TransitionRecord._calleeSaveRegisters._ESI
        ;; oldContext.stackMarkers = record.oldTransitionRecord
        mov ecx, [ebp-(SIZE Struct_System_GCs_CallStack_TransitionRecord)-4]
        mov edx, [eax].Struct_System_GCs_CallStack_TransitionRecord._oldTransitionRecord
        mov [ecx].Struct_Microsoft_Singularity_ThreadContext._stackMarkers, edx
        ;; Epilogue
        mov esp, ebp
        pop ebp
        ret
?g_SwitchToThreadContext@Class_Microsoft_Singularity_Processor@@SIXPAUStruct_Microsoft_Singularity_ThreadContext@@0@Z endp

endif ; SINGULARITY_KERNEL

end
