;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains x86-specific assembly code handling dispatching of interrupts.

include hal.inc

;;; IdtDispatchers are the dispatch functions used for populating the Idt.  Each one
;;; pushes its interrupt id, along with a dummy error code if necessary to normalize
;;; the stack, and jumps to the central dispatch routine
    
DISPATCH_CLEAN MACRO num
        align   SIZEOF Struct_Microsoft_Singularity_Isal_IX_InterruptTable_Dispatcher
        push    0                                       ; No error
        push    num
        jmp     SYMFIX(?g_DispatchVector@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ)
ENDM

DISPATCH_ERR   MACRO num
        align   SIZEOF Struct_Microsoft_Singularity_Isal_IX_InterruptTable_Dispatcher
        push    num
        jmp     SYMFIX(?g_DispatchVector@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ)
ENDM    
        

_IdtDispatchers proc
    
        DISPATCH_CLEAN       000h                            ; #DE Divide-by-Zero
        DISPATCH_CLEAN       001h                            ; #DB Debug Exception
        DISPATCH_CLEAN       002h                            ; NMI Non-Maskable-Interrupt
        DISPATCH_CLEAN       003h                            ; #BP Breakpoint
        DISPATCH_CLEAN       004h                            ; #OF OVerflow
        DISPATCH_CLEAN       005h                            ; #BR Bound-Range
        DISPATCH_CLEAN       006h                            ; #UD Invalid Opcode
        DISPATCH_CLEAN       007h                            ; #NM Device Not Available
        DISPATCH_ERR         008h                            ; #DF Double Fault
        DISPATCH_CLEAN       009h                            ; Unused (was x87 segment except)
        DISPATCH_ERR         00ah                            ; #TS Invalid TSS
        DISPATCH_ERR         00bh                            ; #NP Sgement Not Present
        DISPATCH_ERR         00ch                            ; #SS Stack Exception
        DISPATCH_ERR         00dh                            ; #GP General Protection
        DISPATCH_ERR         00eh                            ; #PF Page Fault
        DISPATCH_CLEAN       00fh                            ; Reserved
        DISPATCH_CLEAN       010h                            ; #MF x87 Math Error
        DISPATCH_ERR         011h                            ; #AC Alignment Check
        DISPATCH_CLEAN       012h                            ; #MC Machine Check
        DISPATCH_CLEAN       013h                            ; #XF SIMD Exception
        DISPATCH_CLEAN       014h                            ; 014h exception
        DISPATCH_CLEAN       015h                            ; 015h exception
        DISPATCH_CLEAN       016h                            ; 016h exception
        DISPATCH_CLEAN       017h                            ; 017h exception
        DISPATCH_CLEAN       018h                            ; 018h exception
        DISPATCH_CLEAN       019h                            ; 019h exception
        DISPATCH_CLEAN       01ah                            ; 01ah exception
        DISPATCH_CLEAN       01bh                            ; 01bh exception
        DISPATCH_CLEAN       01ch                            ; 01ch exception
        DISPATCH_CLEAN       01dh                            ; 01dh exception
        DISPATCH_CLEAN       01eh                            ; 01eh exception
        DISPATCH_CLEAN       01fh                            ; 01fh exception
        DISPATCH_CLEAN       020h                            ; 021h: first interrupt
        _num = 021h                                          ; 021h to 0ffh
        WHILE _num LE 0ffh
                DISPATCH_CLEAN       _num
                _num = _num + 1
        ENDM
    
_IdtDispatchers endp

;;; GetDispatchers returns the address of the IdtDispatchers array.  This
;;; is necessary since we can't directly take the address of a function in managed code.
        
SYMFIX(?g_GetDispatchers@Struct_Microsoft_Singularity_Isal_IX_InterruptTable@@SIPAUStruct_Microsoft_Singularity_Isal_IX_InterruptTable_Dispatcher@@XZ) proc
        lea     eax, _IdtDispatchers       
        ret
SYMFIX(?g_GetDispatchers@Struct_Microsoft_Singularity_Isal_IX_InterruptTable@@SIPAUStruct_Microsoft_Singularity_Isal_IX_InterruptTable_Dispatcher@@XZ) endp

;;; LoadDispatchTable should be called on each processor to initialize its idt register to the
;;; shared dispatch table.
        
SYMFIX(?g_LoadIdt@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ) proc

        lidt        fword ptr _Idtr
        
        ret
    
SYMFIX(?g_LoadIdt@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ) endp

;;; DispatchVector implements the meat of the low level interrupt dispatching logic. Its goal
;;; is to implement the transition to high level code with minimal overhead.
;;;
;;; There are essentially two tasks: save the context (if appropriate), and switch to the 
;;; interrupt processing stack. 
;;;
;;; This function either returns via iretd, or else doesn't return at all (because the
;;; handler called RestoreContext.)
;;; 
;;; On entry to DispatchVector, the stack looks like this:  
;;;
;;; [TOP]                                       (after pushing regs)
;;; interrupt vector            [esp]           [esp+3P]
;;; interrupt err (parameter)   [esp+1P]        [esp+4P]
;;; interrupted eip             [esp+2P]        [esp+5P]
;;; interrupted cs              [esp+3P]        [esp+6P]
;;; interrupted efl             [esp+4P]        [esp+7P]
;;; [PAGING/X64]
;;; interrupted esp             [esp+5P]        [esp+8P]
;;; interrupted ss              [esp+6P]        [esp+9P]
;;; [NON-PAGING]
;;; previous stack continues    esp+5P          esp+8P
;;;
    
SYMFIX(?g_DispatchVector@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ) proc

ifdef PAGING
if ISA_IX86        
        ;; Fix up segment ds, es to point to valid values
        push    ss
        pop     ds
        push    ss
        pop     es
endif
            
        ;; If we've arrived from ring 3 FS will be invalid.
        push    Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt._pp - Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt._nul
        pop     fs
        
endif

        ;; Save regs in InterruptContext
        push    PAX
        push    PCX
        push    PDX

ifdef ISA_IX64
        push    r8
        push    r9
        push    r10
        push    r11
endif
        
        ;; Decide if/where to stash the context.   For now, we use hard-coded 
        ;; constants based on the vector to make the decision.  Eventually this could be
        ;; delegated to the HAL for more dynamic control of behaviors.
            
        ;; The lowest vectors are exceptions - context save into ProcessorRecord, where the 
        ;; cpu state will be visible to the debugger infrastructure.

        mov     PDX, [PSP].Struct_Microsoft_Singularity_Isal_InterruptContext._vector
        cmp     PDX, Struct_Microsoft_Singularity_Isal_InterruptContext_VectorExceptionMax
        jg      not_exception

        GET_PROCESSOR_CONTEXT PAX
        lea     PCX, [PAX].Struct_Microsoft_Singularity_Isal_CpuRecord._spill

        jmp     save_context

not_exception:  

        ;; The middle vectors are fast interrupts - no context save.  These interrupts may
        ;; be used for fast operations which do not interact with the scheduler; control will
        ;; always resume at the interrupted location.

        cmp     PDX, Struct_Microsoft_Singularity_Isal_InterruptContext_VectorSchedulerMin
        jl      skip_save  

        ;; The highest vectors are normal interrupts - context save into ThreadRecord.  Typically
        ;; control may be resumed on a different thread.

        GET_THREAD_CONTEXT PAX
        lea     PCX, [PAX].Struct_Microsoft_Singularity_Isal_ThreadRecord._spill

save_context:
    
        ;; Note PCX has the context buffer from above
        mov     PDX, PSP
        call    SYMFIX(?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SI_NPAU1@PAUStruct_Microsoft_Singularity_Isal_InterruptContext@@@Z)

skip_save:  

        ;; Save previous stack limit
        GET_THREAD_RECORD_FIELD PCX, _activeStackLimit
        push    PCX
        
        ;; See if we are on the interrupt stack
        GET_CPU_RECORD_FIELD PDX, _interruptStackLimit
        cmp     PDX, PCX
        mov     PCX, PSP        ; stash old stack ptr; doesn't change flags 
        je      no_switch

        ;; switch to interrupt stack
        GET_CPU_RECORD_FIELD PAX, _interruptStackBegin
        mov     PSP, PAX
        SET_THREAD_RECORD_FIELD _activeStackLimit, PDX

no_switch:

        ;; Save the old stack pointer
        push    PCX

        ;; InterruptContext is old PSP + 4
        add     PCX, SIZEOF PWORD
        
        ;; call the handler
        call    SYMFIX(?g_DispatchInterrupt@Class_Microsoft_Singularity_Isal_Isa@@SIXPAUStruct_Microsoft_Singularity_Isal_InterruptContext@@@Z)

        ;; Note that we may or may not get here, depending on whether the InterruptDispatch routine
        ;; returned or not (it may have restored a previous context.)  If we did get here, return
        ;; back to the interrupted context.

        ;; Restore the old stack pointer and limit
        pop     PSP
        pop     PAX
        SET_THREAD_RECORD_FIELD _activeStackLimit, PAX

    ;; Restore caller save regs, do normal interrupt resume
ifdef ISA_IX64
        pop     r11
        pop     r10
        pop     r9
        pop     r8
endif
        pop     PDX
        pop     PCX
        pop     PAX

    ;; Discard vector/err    
        add     PSP, SIZEOF PWORD * 2

    ;; Return
        jmp     [SYMFIX(?c_returnFromInterrupt@Class_Microsoft_Singularity_Isal_Isa@@2PAUvoid@@A)]
    
SYMFIX(?g_DispatchVector@Class_Microsoft_Singularity_Isal_Isa@@SIXXZ) endp

.data
        
;;; We have to manually declare this variable to get it properly aligned. This seems to be a bartok bug.
        align 16
?c_idt@Class_Microsoft_Singularity_Isal_Isa@@2?AUStruct_Microsoft_Singularity_Isal_IX_InterruptTable@@A   Struct_Microsoft_Singularity_Isal_IX_InterruptTable { }

;;; _Idtr is a global structure which is suitable for passing to the lidt instruction.

IDTR struct 2
        _limit          UINT16          ?
        _base           PWORD           ?
IDTR ends

        align 16
        ;; We want to align the PWORD after the offset, so add padding here.
        dw              ?
ifdef ISA_IX64        
        dw              ?
        dw              ?
endif
        
_Idtr   IDTR  { \
        (SIZEOF Struct_Microsoft_Singularity_Isal_IX_InterruptTable) - 1, \
        ?c_idt@Class_Microsoft_Singularity_Isal_Isa@@2?AUStruct_Microsoft_Singularity_Isal_IX_InterruptTable@@A }
        
END
