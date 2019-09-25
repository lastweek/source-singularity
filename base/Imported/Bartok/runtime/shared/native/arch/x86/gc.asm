;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

include core.inc

PAGE_BITS               EQU     12
MASK_OWNER              EQU     03h

;; Let's define some shorter names for commonly used structures
ifdef SINGULARITY        
ThreadContext TYPEDEF Struct_Microsoft_Singularity_X86_ThreadContext
endif                

Thread TYPEDEF Class_System_Threading_Thread
TransitionRecord TYPEDEF Struct_System_GCs_CallStack_TransitionRecord

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
        push eax                     ; save caller-save registers
        push ecx
        push edx
        lea  ecx, [ebp-(SIZE TransitionRecord)] ; calculate new stack marker address
ifdef SINGULARITY
        CurrentThreadContext(eax)           ; get current threadcontext
        mov  edx, [eax].ThreadContext._stackMarkers ;save old stack marker address
else
        CurrentThread(eax)           ; get current thread
        mov  edx, [eax].Thread._asmStackMarker ;save old stack marker address
endif
        mov  [ecx].TransitionRecord._oldTransitionRecord, edx
ifdef SINGULARITY
        mov  [eax].ThreadContext._stackMarkers, ecx ; update thread record field
else
        mov  [eax].Thread._asmStackMarker,ecx                 ; update thread record field
endif                
        mov  edx, [esp+12]  ; load return address of this call
        mov  [ecx].TransitionRecord._callAddr,edx
        lea  edx,[esp+16]
        mov  [ecx].TransitionRecord._stackBottom, edx    ; save bottom of stack frame
        mov  [ecx].TransitionRecord._calleeSaveRegisters._EBX, ebx            ; save callee-save registers
        mov  [ecx].TransitionRecord._calleeSaveRegisters._EDI, edi
        mov  [ecx].TransitionRecord._calleeSaveRegisters._ESI, esi
        mov  [ecx].TransitionRecord._calleeSaveRegisters._EBP, ebp
        mov  ecx, eax
ifdef SINGULARITY
;         call ?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SIXUStruct_Microsoft_Singularity_X86_ThreadContext@@@Z
else
        call ?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SIXPAUClass_System_Threading_Thread@@@Z
endif                
        pop  edx
        pop  ecx
        pop  eax
        ret
__pushStackMark endp

;
; popStackMark: pop the pointer before returning from the function
;
align 16
__popStackMark proc
        push eax                     ; save caller-save registers
        push ecx
        push edx
ifdef SINGULARITY
;         CurrentThreadContext(ecx)      ; get current thread
;         call ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SIPAUClass_System_Threading_Thread@@UStruct_Microsoft_Singularity_X86_ThreadContext@@@Z
        CurrentThreadContext(eax)      ; get current thread
else        
        CurrentThreadIndex(eax)      ; get current thread
        mov ecx, eax
        call ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SIPAUClass_System_Threading_Thread@@H@Z
endif        
        lea ecx, [ebp-(SIZE TransitionRecord)]
        mov edx, [ecx].TransitionRecord._oldTransitionRecord ; get old stack marker value
ifdef SINGULARITY
        mov [eax].ThreadContext._stackMarkers, edx ; update thread record field
else                
        mov [eax].Thread._asmStackMarker, edx ; update thread record field
endif        
        mov ebx, [ecx].TransitionRecord._calleeSaveRegisters._EBX   ; restore callee-save registers
        mov edi, [ecx].TransitionRecord._calleeSaveRegisters._EDI
        mov esi, [ecx].TransitionRecord._calleeSaveRegisters._ESI
        mov ebp, [ecx].TransitionRecord._calleeSaveRegisters._EBP
        pop edx                      ; restore caller-save registers
        pop ecx
        pop eax
        ret
__popStackMark endp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; void CollectBodyTransition(Thread thread, int generation):  
;   Save the callee-save registers in a transition record and then call
;   System.GC.CollectBody(thread, generation)
;
align 16
?g_CollectBodyTransition@Class_System_GC@@SIXPAUClass_System_Threading_Thread@@H@Z proc
; static void __fastcall GC.CollectBodyTransition(Thread, int)
        push ebp
        mov ebp, esp
        sub esp, (SIZE TransitionRecord)
        push edx
        lea edx, [ebp-(SIZE TransitionRecord)]
ifdef SINGULARITY        
        mov eax, [ecx].Thread._context._stackMarkers
else
        mov eax, [ecx].Thread._asmStackMarker     ; get old marker address
endif
        mov [edx].TransitionRecord._oldTransitionRecord, eax ; link from current record
        mov eax, dword ptr [ebp+4]                ; load return address
        mov [edx].TransitionRecord._callAddr, eax
        lea eax, [ebp+8]                          ; skip pushed PC and SP
        mov [edx].TransitionRecord._stackBottom, eax   ; (bottom of stack frame)
        mov [edx].TransitionRecord._calleeSaveRegisters._EBX, ebx ; save callee-save registers
        mov [edx].TransitionRecord._calleeSaveRegisters._EDI, edi
        mov [edx].TransitionRecord._calleeSaveRegisters._ESI, esi
        mov eax, dword ptr [ebp]
        mov [edx].TransitionRecord._calleeSaveRegisters._EBP, eax ; save old ebp value
ifdef SINGULARITY        
        mov [ecx].Thread._context._stackMarkers, edx ; update thread field
else
        mov [ecx].Thread._asmStackMarker, edx ; update thread field
endif
        pop edx
        call ?g_CollectBody@Class_System_GC@@SIPAUClass_System_Threading_Thread@@PAU2@H@Z
        ; static void __fastcall GC.CollectBody(Thread,int)
        lea edi, [ebp-(SIZE TransitionRecord)]
        mov esi, [edi].TransitionRecord._oldTransitionRecord ; get old marker address
ifdef SINGULARITY        
        mov [eax].Thread._context._stackMarkers, esi ; restore thread field
else
        mov [eax].Thread._asmStackMarker, esi     ; restore thread field
endif
        mov ebx, [edi].TransitionRecord._calleeSaveRegisters._EBX ; restore callee-save regs
        mov esi, [edi].TransitionRecord._calleeSaveRegisters._ESI
        mov ebp, [edi].TransitionRecord._calleeSaveRegisters._EBP
        mov edi, [edi].TransitionRecord._calleeSaveRegisters._EDI
        add esp, (SIZE TransitionRecord)+4 ;  skip FP
        ret
?g_CollectBodyTransition@Class_System_GC@@SIXPAUClass_System_Threading_Thread@@H@Z endp

ifdef NYI
ifdef SINGULARITY
;; __throwDispatcherUnwind depends on this only modifying eax
?g_ReturnToUnlinkStackMethod@Class_System_GCs_CallStack@@SI_NPAUuintPtr@@@Z proc
        mov eax, _UnlinkStackBegin
        cmp ecx, eax
        jl  return_false
        mov eax, _UnlinkStackLimit
        cmp ecx, eax
        jg  return_false
        mov eax, 1
        ret 0
return_false:
        mov eax, 0
        ret
?g_ReturnToUnlinkStackMethod@Class_System_GCs_CallStack@@SI_NPAUuintPtr@@@Z endp
endif
endif

; The assembly versions of Buffer.ZeroMemory have not been implemented for x86

align 16
?g_ZeroMemoryXMM@Class_System_Buffer@@SIXPAUUntracedPtr_uint8@@PAUuintPtr@@@Z proc
        int 3
?g_ZeroMemoryXMM@Class_System_Buffer@@SIXPAUUntracedPtr_uint8@@PAUuintPtr@@@Z endp
        
align 16
?g_ZeroMemoryMM0@Class_System_Buffer@@SIXPAUUntracedPtr_uint8@@PAUuintPtr@@@Z proc
        int 3
?g_ZeroMemoryMM0@Class_System_Buffer@@SIXPAUUntracedPtr_uint8@@PAUuintPtr@@@Z endp

align 16
?g_ZeroMemorySTOS@Class_System_Buffer@@SIXPAUUntracedPtr_uint8@@PAUuintPtr@@@Z proc
        int 3
?g_ZeroMemorySTOS@Class_System_Buffer@@SIXPAUUntracedPtr_uint8@@PAUuintPtr@@@Z endp

end
