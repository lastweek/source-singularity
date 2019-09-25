;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains x86-specific assembly code related to context save and restore.
;;; The key goal here is to keep this set of code as small as possible, in favor
;;; of portable C++ or C# code.

include hal.inc

;;; Save takes one argument - a context record to save the context in. It saves all the
;;; nonvolatile state (it does not bother saving caller save regs.)
;;;
;;; This function returns true after saving the context. When the context is resumed, control
;;; resumption will occur at the point this function returned, but with a false
;;; return value.
;;; 
;;; Calling conventions are normal __fastcall.
    
;; __fastcall bool SaveContext(Context *context)
    
SYMFIX(?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SI_NPAU1@@Z) proc

        ;; Save integer registers - only need to record callee-save registers.

        ;; don't need exact flags, but we'll pick up the non-transient ones
        PUSHFP
        pop     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._fl

        ;; Interrupts are always disabled at this point. 
        ;; EFlags should reflect this for bookkeeping purposes (this will not be the case
        ;; on non-ring0 HALs.)

        and     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._fl, \
                        NOT Struct_Microsoft_Singularity_Isal_IX_EFlags_IF

        mov     PAX, cs
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cs, PAX

        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._bp, PBP
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._sp, PSP
        lea     PAX, resume_context                
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._ip, PAX

        ;; Save previous stack limit
        GET_THREAD_RECORD_FIELD PAX, _activeStackLimit
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._stackLimit, PAX
    
save_integer: 
    
        ;; Always save caller-saved registers.
    
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._bx, PBX
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._di, PDI
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._si, PSI

ifdef ISA_IX64
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r12, r12
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r13, r13
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r14, r14
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r15, r15
endif

        ;; Save floating point/mmx registers
    
        fxsave  [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._mmx

ifdef DEBUG
        ;; Garbage out callee-saved registers

        mov     PAX, 0deadbeefh
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._ax, PAX
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cx, PAX
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._dx, PAX

ifdef ISA_IX64
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r8, PAX
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r9, PAX
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r10, PAX
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r11, PAX
endif

endif
    
ifdef PAGING

        mov     PAX, cr3
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cr3, PAX
        
endif
        
        ;; Mark context as non-active
        or      [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._spillFlags, \
                    Struct_Microsoft_Singularity_Isal_SpillContext_ContentsSpilled

        ;; return true
        mov     PAX, 1
        ret

resume_context:

        ;; this is where non-interrupt control resume will happen
        ;; TBD: just stash the return address in the context...

        ;; return false
        xor     PAX, PAX
        ret

SYMFIX(?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SI_NPAU1@@Z) endp

;;; Save takes two arguments - a context record to save the context in, and
;;; an interrupt frame to describe an interruption location.
;;;
;;; Calling conventions are normal __fastcall.
    
;; __fastcall bool SaveContext(Context *context, InterruptContext *interrupt)

SYMFIX(?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SI_NPAU1@PAUStruct_Microsoft_Singularity_Isal_InterruptContext@@@Z) proc

        ;; Save control registers

        ;; Note: we don't bother to save ss since it can be derived either from cs or
        ;; from the current ss.
        
ifdef PAGING
        ;; Check if this was a cross-ring interrupt
        mov     PAX, cs
        xor     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._cs
        test    PAX, 3
        jz      save_same_ring

        ;; resume at the stack pointed to by the Interrupt Frame
        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._sp 
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._sp, PAX

        jmp     save_control_common
endif

save_same_ring: 

ifdef ISA_IX86
        ;; resume at the stack after popping the Interrupt Frame
        lea     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._sp
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._sp, PAX
else    
        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._sp 
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._sp, PAX
endif
        
save_control_common:
        
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._bp, PBP

        ;; Save previous stack limit
        GET_THREAD_RECORD_FIELD PAX, _activeStackLimit
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._stackLimit, PAX
    
        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._ip 
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._ip, PAX

        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._fl
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._fl, PAX
        
        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._cs 
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cs, PAX

save_integer: 
    
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._bx, PBX
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._di, PDI
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._si, PSI

ifdef ISA_IX64        
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r12, r12
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r13, r13
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r14, r14
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r15, r15
endif

        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._ax
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._ax, PAX
    
        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._cx
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cx, PAX
    
        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._dx
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._dx, PAX

ifdef ISA_IX64        
        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._r8
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r8, PAX

        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._r9
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r9, PAX

        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._r10
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r10, PAX

        mov     PAX, [PDX].Struct_Microsoft_Singularity_Isal_InterruptContext._r11
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r11, PAX
endif
        
save_fp:

        ;; Save floating point/mmx registers
    
        fxsave  [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._mmx
    
ifdef PAGING

        mov     PAX, cr3
        mov     [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cr3, PAX
        
endif
        
        ;; Mark context as non-active
        or      [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._spillFlags, \
                    Struct_Microsoft_Singularity_Isal_SpillContext_ContentsSpilled

        ret

SYMFIX(?m_Save@Struct_Microsoft_Singularity_Isal_SpillContext@@SI_NPAU1@PAUStruct_Microsoft_Singularity_Isal_InterruptContext@@@Z) endp



;;; Resume restores the processor state to the state described in the given
;;; context record.  If an interrupt context is provided, the portion of the context
;;; represented there is spilled to the interrupt context rather than the current context.
;;;
;;; 
;;; __fastcall void ResumeContext(Struct_Microsoft_Singularity_Isal_SpillContext *context,
;;;                             Struct_Microsoft_Singularity_Isal_InterruptContext *interrupt);
    
SYMFIX(?m_Resume@Struct_Microsoft_Singularity_Isal_SpillContext@@SIXPAU1@@Z) proc

ifdef PAGING
        
        ;; Restore cr3 if necessary, but avoid TLB flushes if possible
        mov     PDX, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cr3
        mov     PAX, cr3
        cmp     PAX, PDX
        je      skip_cr3
        mov     cr3, PDX
skip_cr3:
        
endif
        ;; Restore floating point/mmx registers
    
        fxrstor  [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._mmx

ifdef ISA_IX86
ifdef PAGING
        
        ;; Restore segment registers
    
        mov     eax, [ecx].Struct_Microsoft_Singularity_Isal_SpillContext._cs
        mov     ds, eax
        mov     es, eax
        
endif
endif
        ;; Restore integer registers

        ;; save PAX for scratch 
        mov     PBX, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._bx
        ;; skip PCX since that's our context; we'll pick it up last thing
        ;; save PDX for scratch
        mov     PDI, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._di
        mov     PSI, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._si

ifdef ISA_IX64
        mov     r12, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r12
        mov     r13, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r13
        mov     r14, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r14
        mov     r15, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r15
endif
        
        ;; Now restore control registers

ifdef PAGING        
        ;; See if we are transitioning across rings or not
        mov     PAX, cs
        xor     PAX, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cs
        test    PAX, 3

        jz      same_ring
        
        ;; iret will restore the stack for us.  Cs == ss when we control segments
        push    [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cs
        push    [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._sp

        jmp     restore_control
endif
        
same_ring:

        ;; Note: we use existing ss rather than saved cs (on windows, they may be different)
ifdef ISA_IX86
        ;; Restore sp directly 
        mov     PSP, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._sp
else
        ;; iret will restore the stack for us
        mov     PAX, ss
        push    PAX
        push    [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._sp
endif   


restore_control:

        ;; Restore previous stack limit
        mov     PAX, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._stackLimit
        SET_THREAD_RECORD_FIELD _activeStackLimit, PAX
    
        ;; push values for iret
        push    [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._fl
        push    [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cs
        push    [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._ip

        mov     PBP, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._bp

        ;; clear spilled flag
        and      [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._spillFlags, \
                NOT Struct_Microsoft_Singularity_Isal_SpillContext_ContentsSpilled

        ;; Restore regs & return
        ;; (Note that our integer flags may not be set; but these regs are
        ;; trashed by calling conventions anyway.)
ifdef ISA_IX64
        mov     r11, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r11
        mov     r10, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r10
        mov     r9, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r9
        mov     r8, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._r8
endif
        mov     PAX, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._ax
        mov     PDX, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._dx
        mov     PCX, [PCX].Struct_Microsoft_Singularity_Isal_SpillContext._cx
    
        jmp     [SYMFIX(?c_returnFromInterrupt@Class_Microsoft_Singularity_Isal_Isa@@2PAUvoid@@A)]
    
SYMFIX(?m_Resume@Struct_Microsoft_Singularity_Isal_SpillContext@@SIXPAU1@@Z) endp

;;; ResetContext resets the current context fp & debug register state to a canonical state
;;; for interrupt handler code.  This should only be used after saving the current context.
;;;
;;; Calling conventions are normal __fastcall.
;;; 
;;; __fastcall void ResetCurrent();
    
SYMFIX(?g_ResetCurrent@Struct_Microsoft_Singularity_Isal_SpillContext@@SIXXZ) proc

        push    PAX
    
        fninit
        mov     PAX, 37eh
        push    PAX
        fldcw   [PSP]
        pop     PAX

        pop     PAX

        ret

SYMFIX(?g_ResetCurrent@Struct_Microsoft_Singularity_Isal_SpillContext@@SIXXZ) endp

END

