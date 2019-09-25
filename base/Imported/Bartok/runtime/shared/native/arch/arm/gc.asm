;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

    AREA |.text|, CODE, READONLY

PAGE_BITS   EQU     12
MASK_OWNER  EQU     0x3

    INCLUDE core.inc

    ;;;;
    ;; Placeholder stubs to satisfy the linker
    ;;;;


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
        ;; Thread *currentThread(r10) = Thread.CurrentThread()
        CurrentThread r10, r8
        ;; TransitionRecord *oldRecord(r8) = currentThread(r10)->asmStackMarker
        ldr r8, [r10, #|Class_System_Threading_Thread___asmStackMarker|]
        ;; newRecord(r9)->oldTransitionRecord = oldRecord(r8)
        str r8, [r9, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]
        ;; currentThread(r10)->asmStackMarker = newRecord(r9)
        str r9, [r10, #|Class_System_Threading_Thread___asmStackMarker|]
        ;; newRecord(r9)->callAddr = return address of this call (lr).
        str lr, [r10, #|Struct_System_GCs_CallStack_TransitionRecord___callAddr|]
        ;; newRecord(r9)->stackBottom = bottom of stack frame (sp)
        str sp, [r10, #|Struct_System_GCs_CallStack_TransitionRecord___stackBottom|]
        ;; Restore registers r9 and r10 (and the ummodified r11)
        ldmdb fp, {r8-r11}
        ;; return
        mov pc, lr

    ENTRY_END

    EXPORT __popStackMark
    NESTED_ENTRY __popStackMark
    PROLOG_END

        ;; From this point forward, we use r8, r9, and r10 as temps.
        ;; R12 may hold the address of the call
        ;; TransitionRecord *newRecord(r9) = FP - sizeof(TransitionRecord);
        sub r9, fp, #|Struct_System_GCs_CallStack_TransitionRecord___SIZE|
        ;; Thread *currentThread(r10) = Thread.CurrentThread()
        CurrentThread r10, r8
        ;; TransitionRecord *oldRecord(r8) = newRecord(r9)->oldTransitionRecord
        ldr r8, [r9, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]
        ;; currentThread(r10) = oldRecord(r8)
        str r8, [r10, #|Class_System_Threading_Thread___asmStackMarker|]
        ;; Restore callee-save registers from the transition record.
        ;; Since the transition record is located immediately below the FP,
        ;; we index off the FP rather than the pointer to the struct itself.
        ldmdb fp, {r4-r11}
        ;; return
        mov pc, lr

    ENTRY_END

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

        ;; TransitionRecord *oldRecord(r9) = currentThread(r10)->asmStackMarker
        ldr r9, [r0, #|Class_System_Threading_Thread___asmStackMarker|]
        ;; newRecord(sp)->oldTransitionRecord = oldRecord(r9)
        str r9, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]
        ;; currentThread(r10)->asmStackMarker = newRecord(sp)
        str sp, [r0, #|Class_System_Threading_Thread___asmStackMarker|]
        ;; newRecord(sp)->callAddr = return address of this call (lr).
        str lr, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___callAddr|]
        ;; newRecord(sp)->stackBottom = bottom of stack frame (r12)
        str r12, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___stackBottom|]
        ;; Thread *currentThread(r0) = System.GC.CollectBody(r0, r1)
        bl |?g_CollectBody@Class_System_GC@@SAPAUClass_System_Threading_Thread@@PAU2@H@Z|
        ;; TransitionRecord *newRecord(sp) = &transitionRecord
        ;; TransitionRecord *oldRecord(r9) = newRecord(sp)->oldTransitionRecord
        ldr r9, [sp, #|Struct_System_GCs_CallStack_TransitionRecord___oldTransitionRecord|]
        ;; currentThread(r0)->asmStackMarker = oldRecord(r9)
        str r9, [r0, #|Class_System_Threading_Thread___asmStackMarker|]

        ;; Restore permanents, FP, SP, and return
        ldmdb fp, {r4-r11, sp, pc}

    ENTRY_END


|?g_ZeroMemoryMM0@Class_System_Buffer@@SAXPAUUntracedPtr_uint8@@PAUuintPtr@@@Z|
    EXPORT |?g_ZeroMemoryMM0@Class_System_Buffer@@SAXPAUUntracedPtr_uint8@@PAUuintPtr@@@Z|
    
    mov r0, #0xde
    mov r0, r0 LSL #8
    orr r0, r0, #0xad
    mov r0, r0 LSL #16
    mov pc, lr

    LTORG

    END

;;;;;;;;;;;;;;;;;;;;;;;
;;;;;   TODO   ;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;

;; Let's define some shorter names for commonly used structures
ifdef SINGULARITY        
ThreadContext TYPEDEF Struct_Microsoft_Singularity_X86_ThreadContext
endif                

Thread TYPEDEF Class_System_Threading_Thread
TransitionRecord TYPEDEF Struct_System_GCs_CallStack_TransitionRecord

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
