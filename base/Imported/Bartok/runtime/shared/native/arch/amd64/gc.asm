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
        lea  rcx, [rbp-(SIZE TransitionRecord)] ; calculate new stack marker address
ifdef SINGULARITY
        CurrentThreadContext(rax)           ; get current threadcontext
        mov  rdx, [eax].ThreadContext._stackMarkers ;save old stack marker address
else
        CurrentThread rax,eax, rdx           ; get current thread
        mov  rdx, [rax].Thread._asmStackMarker ;save old stack marker address
endif
        mov  [rcx].TransitionRecord._oldTransitionRecord, rdx
ifdef SINGULARITY
        mov  [rax].ThreadContext._stackMarkers, ecx ; update thread record field
else
        mov  [rax].Thread._asmStackMarker,rcx                 ; update thread record field
endif                
    ;; REVIEWx64: x86=12, x64=56, symbolic value maybe?
        mov  rdx, [rsp+56]  ; load return address of this call
        mov  [rcx].TransitionRecord._callAddr,rdx
    ;; REVIEWx64: x86=16, x64=64, symbolic value maybe?
        lea  rdx, [rsp+64]
        mov  [rcx].TransitionRecord._stackBottom, rdx    ; save bottom of stack frame
        mov  [rcx].TransitionRecord._calleeSaveRegisters._EBX, rbx ; save callee-save registers
        mov  [rcx].TransitionRecord._calleeSaveRegisters._EDI, rdi
        mov  [rcx].TransitionRecord._calleeSaveRegisters._ESI, rsi
        mov  [rcx].TransitionRecord._calleeSaveRegisters._EBP, rbp
        mov  [rcx].TransitionRecord._calleeSaveRegisters._R12, r12
        mov  [rcx].TransitionRecord._calleeSaveRegisters._R13, r13
        mov  [rcx].TransitionRecord._calleeSaveRegisters._R14, r14
        mov  [rcx].TransitionRecord._calleeSaveRegisters._R15, r15
        mov  rcx, rax
ifdef SINGULARITY
;         call ?g_LeaveManagedSpace@Class_System_GCs_Transitions@@SAXUStruct_Microsoft_Singularity_X86_ThreadContext@@@Z
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
;         CurrentThreadContext(ecx)      ; get current thread
;         call ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SAPEAUClass_System_Threading_Thread@@UStruct_Microsoft_Singularity_X86_ThreadContext@@@Z
        CurrentThreadContext(rax)      ; get current thread
else        
        CurrentThreadIndex rax,eax, rcx     ; get current thread
        mov rcx, rax
        call ?g_ReturnToManagedSpace@Class_System_GCs_Transitions@@SAPEAUClass_System_Threading_Thread@@H@Z
endif        
        lea rcx, [rbp-(SIZE TransitionRecord)]
        mov rdx, [rcx].TransitionRecord._oldTransitionRecord ; get old stack marker value
ifdef SINGULARITY
        mov [rax].ThreadContext._stackMarkers, rdx; update thread record field
else                
        mov [rax].Thread._asmStackMarker, rdx; update thread record field
endif        
        mov rbx, [rcx].TransitionRecord._calleeSaveRegisters._EBX   ; restore callee-save registers
        mov rdi, [rcx].TransitionRecord._calleeSaveRegisters._EDI
        mov rsi, [rcx].TransitionRecord._calleeSaveRegisters._ESI
        mov rbp, [rcx].TransitionRecord._calleeSaveRegisters._EBP
        mov r12, [rcx].TransitionRecord._calleeSaveRegisters._R12
        mov r13, [rcx].TransitionRecord._calleeSaveRegisters._R13
        mov r14, [rcx].TransitionRecord._calleeSaveRegisters._R14
        mov r15, [rcx].TransitionRecord._calleeSaveRegisters._R15
        pop r11
        pop r10
        pop r9
        pop r8
        pop rdx                      ; restore caller-save registers
        pop rcx
        pop rax
        ret
__popStackMark endp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; void CollectBodyTransition(Thread thread, int generation):  
;   Save the callee-save registers in a transition record and then call
;   System.GC.CollectBody(thread, generation)
;
align 16
?g_CollectBodyTransition@Class_System_GC@@SAXPEAUClass_System_Threading_Thread@@H@Z proc frame
; static void __fastcall GC.CollectBodyTransition(Thread, int)
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        sub rsp, (SIZE TransitionRecord)+32 ; 32 is to shadow parameters to the call to CollectBody
        and rsp, NOT 0Fh        ; 16-byte align stack frame for call below
        push rdx
        lea rdx, [rbp-(SIZE TransitionRecord)]
ifdef SINGULARITY        
        mov rax, [rcx].Thread._context._stackMarkers
else
        mov rax, [rcx].Thread._asmStackMarker     ; get old marker address
endif
        mov [rdx].TransitionRecord._oldTransitionRecord, rax ; link from current record
        mov rax, qword ptr [rbp+8]                ; load return address
        mov [rdx].TransitionRecord._callAddr, rax
        lea rax, [rbp+16]                         ; skip pushed PC and SP
        mov [rdx].TransitionRecord._stackBottom, rax ; (bottom of stack frame)
        mov [rdx].TransitionRecord._calleeSaveRegisters._EBX, rbx ; save callee-save registers
        mov [rdx].TransitionRecord._calleeSaveRegisters._EDI, rdi
        mov [rdx].TransitionRecord._calleeSaveRegisters._ESI, rsi
        mov [rdx].TransitionRecord._calleeSaveRegisters._R12, r12
        mov [rdx].TransitionRecord._calleeSaveRegisters._R13, r13
        mov [rdx].TransitionRecord._calleeSaveRegisters._R14, r14
        mov [rdx].TransitionRecord._calleeSaveRegisters._R15, r15
        mov rax, qword ptr [rbp]                  ; get EBP value from stack
        mov [rdx].TransitionRecord._calleeSaveRegisters._EBP, rax
ifdef SINGULARITY        
        mov [rcx].Thread._context._stackMarkers, rdx ; update thread field
else
        mov [rcx].Thread._asmStackMarker, rdx     ; update thread field
endif
        pop rdx
        call ?g_CollectBody@Class_System_GC@@SAPEAUClass_System_Threading_Thread@@PEAU2@H@Z
        ; static void __fastcall GC.CollectBody(Thread,int)
        lea rdi, [rbp-(SIZE TransitionRecord)]
        mov rsi, [rdi].TransitionRecord._oldTransitionRecord ; get old marker address
ifdef SINGULARITY        
        mov [rax].Thread._context._stackMarkers, rsi ; restore thread field
else
        mov [rax].Thread._asmStackMarker, rsi     ; restore thread field
endif
        mov rbx, [rdi].TransitionRecord._calleeSaveRegisters._EBP
        mov qword ptr [rbp], rbx                  ; restore EBP value to stack
        mov rbx, [rdi].TransitionRecord._calleeSaveRegisters._EBX ; restore callee-save regs
        mov rsi, [rdi].TransitionRecord._calleeSaveRegisters._ESI
        mov r12, [rdi].TransitionRecord._calleeSaveRegisters._R12
        mov r13, [rdi].TransitionRecord._calleeSaveRegisters._R13
        mov r14, [rdi].TransitionRecord._calleeSaveRegisters._R14
        mov r15, [rdi].TransitionRecord._calleeSaveRegisters._R15
        mov rdi, [rdi].TransitionRecord._calleeSaveRegisters._EDI
        mov rsp, rbp
        pop rbp
        ret
?g_CollectBodyTransition@Class_System_GC@@SAXPEAUClass_System_Threading_Thread@@H@Z endp

ifdef NYI
ifdef SINGULARITY
;; __throwDispatcherUnwind depends on this only modifying eax
?g_ReturnToUnlinkStackMethod@Class_System_GCs_CallStack@@SA_NPEAUuintPtr@@@Z proc ;frame
        ;.endprolog
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
?g_ReturnToUnlinkStackMethod@Class_System_GCs_CallStack@@SA_NPEAUuintPtr@@@Z endp
endif
endif

; Below are 3 assembly implementations for the function: 
;          static void ZeroMemory(byte* dest, UIntPtr len). 
; Assumption: Len is in terms of bytes, and is multiple of 4 bytes (dword).
; TODO: reverse the direction of zeroing and compare the results
?g_ZeroMemorySTOS@Class_System_Buffer@@SAXPEAUUntracedPtr_uint8@@PEAUuintPtr@@@Z proc frame
        PrologPush  rdi
        .endprolog
        mov rdi, rcx ;dest
        mov rax, 0
        mov rcx, rdx
        shr rcx, 3    ; the number of qwords
        rep stos qword ptr [rdi]
        shr edx, 2    ; the number of dwords
        and edx, 1  ; the number of dwords remained to be moved
        mov ecx, edx
        rep stos dword ptr [edi]
        pop rdi
        ret
 ?g_ZeroMemorySTOS@Class_System_Buffer@@SAXPEAUUntracedPtr_uint8@@PEAUuintPtr@@@Z endp

?g_ZeroMemoryXMM@Class_System_Buffer@@SAXPEAUUntracedPtr_uint8@@PEAUuintPtr@@@Z proc 
       ; rcx: dist          rdx: len

       ; since dist is UIntPtr, whose value is multiple of 8, and we are going
       ; to use movntdq, which requires the address to be aligned to 16 bytes.
       ; Here align the dist to 16 bytes first.
       test rcx, 8
       jz init64Bytes
       mov qword ptr [rcx + 0], 0
       add rcx, 8
       sub rdx, 8
              
init64Bytes:
        pxor    xmm4, xmm4

        ; zero 64-bytes, if any
        cmp rdx, 64
        jl short init32Bytes

        mov rax, rdx
        shr rax, 6
        shl rax, 6
        
next:
        movntdq  [rcx + 0], xmm4
        movntdq  [rcx + 16], xmm4
        movntdq  [rcx + 32], xmm4
        movntdq  [rcx + 48], xmm4
        add     rcx, 64
        sub     rax, 64
        ja      next

        ; now zero remaining 32-bytes, if any
init32Bytes:
        test rdx, 32
        jz short  init16Bytes
        movntdq  [rcx + 0], xmm4
        movntdq  [rcx + 16], xmm4
        add rcx, 32

        ; now zero remaining 16-bytes, if any
init16Bytes:
        test rdx, 16
        jz short init8Bytes
        movntdq  [rcx + 0], xmm4
        add rcx, 16

        ; now zero remaining 8-bytes, if any
init8Bytes:
        test rdx, 8
        jz short init4Bytes
        mov qword ptr [rcx + 0], 0
        add rcx, 8

        ; now zero remaining 4-bytes, if any
init4Bytes:
        test rdx, 4
        jz short exitZeroMem                                                
        mov dword ptr [rcx + 0], 0
        add rcx, 4

exitZeroMem:        
        sfence
        ret
?g_ZeroMemoryXMM@Class_System_Buffer@@SAXPEAUUntracedPtr_uint8@@PEAUuintPtr@@@Z endp

?g_ZeroMemoryMM0@Class_System_Buffer@@SAXPEAUUntracedPtr_uint8@@PEAUuintPtr@@@Z proc 
       ; rcx: dist          rdx: len

       pxor    mm0, mm0

       ; since dist is UIntPtr, whose value is multiple of 8, and we are going
       ; to use movntdq, which requires the address to be aligned to 16 bytes.
       ; Here align the dist to 16 bytes first.
       test rcx, 8
       jz init64Bytes
       movntq  [rcx + 0], mm0
       add rcx, 8
       sub rdx, 8
              
init64Bytes:

        ; zero 64-bytes, if any
        cmp rdx, 64
        jl short init32Bytes

        mov rax, rdx
        shr rax, 6
        shl rax, 6
        
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
        sub     rax, 64
        ja      next

        ; now zero remaining 32-bytes, if any
init32Bytes:
        test rdx, 32
        jz short  init16Bytes
        movntq  [rcx + 0], mm0
        movntq  [rcx + 8], mm0
        movntq  [rcx + 16], mm0
        movntq  [rcx + 24], mm0
        add rcx, 32

        ; now zero remaining 16-bytes, if any
init16Bytes:
        test rdx, 16
        jz short init8Bytes
        movntq  [rcx + 0], mm0
        movntq  [rcx + 8], mm0
        add rcx, 16

        ; now zero remaining 8-bytes, if any
init8Bytes:
        test rdx, 8
        jz short init4Bytes
        movntq  [rcx + 0], mm0
        add rcx, 8

        ; now zero remaining 4-bytes, if any
init4Bytes:
        test rdx, 4
        jz short exitZeroMem                                                
        mov dword ptr [rcx + 0], 0
        add rcx, 4

exitZeroMem:        
        sfence
        emms
        ret
?g_ZeroMemoryMM0@Class_System_Buffer@@SAXPEAUUntracedPtr_uint8@@PEAUuintPtr@@@Z endp
end
