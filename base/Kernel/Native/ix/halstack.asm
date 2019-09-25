;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;  Microsoft Research Singularity
;;
;;  Copyright (c) Microsoft Corporation.  All rights reserved.
;;
;;  File:   halstack.asm
;;
;;  Note:
;;


include hal.inc
        
;; The code in this file runs as part of the priveleged runtime.  It is responsible for
;; calling into the ABI to allocate and free new stack segments, and to do all the low
;; level mucking to stitch the stacks together.
        

;; LinkStack is a glue routine to extend the stack.  Its job is to:
;; 
;;  1 - preserve the calling registers of the function it is being called from
;;  2 - set up arguments and call the appropriate ABI call to grow the stack
;;  3 - copy args and stack frame and switch execution to the resulting new stack segment
;;  4 - tail patch the function return so that Free is called on return
;; 
;; Its entry point calling conventions are delicate; essentially
;;      - rax contains the amount of new stack needed
;;      - all argument registers must be preserved
;;      - two values - (# of bytes) and (Unlink) are passed on the stack (from the stubs below)
;;
;; BUGBUG: This code doesn't maintain the required 16 byte alignment when running on 64-bit platforms
;;         This is not being fixed at the moment, since we're expecting to deprecate this code.

LinkFrame       struct
ifdef ISA_IX64
        _r9              dp ?    ; saved in LinkStack prolog
        _r8              dp ?    ; saved in LinkStack prolog
endif
        _dx              dp ?    ; saved in LinkStack prolog
        _cx              dp ?    ; saved in LinkStack prolog
        _alloc           dp ?    ; saved in LinkStack prolog from ax (set by grower prolog)
        _UnlinkFn        dp ?    ; pushed by LinkStackN stub
        _argStack        dp ?    ; pushed by LinkStackN stub
        ;; Continue address
        _continue        dp ?    ; pushed by call of LinkStack function
        ;; EBP frame
        _oldBp           dp ?    ; pushed by grower prolog
        ;; Return address
        _return          dp ?    ; pushed by call of grower
        ;; Stack Arguments (argStack*sizeof PWORD)
LinkFrame       ends
        
;
;  __checkStackOverflow
;
;  This function takes the bottom of the current frame in eax.  If we
;  detect a stack overflow, we make ourselves a real stack frame (for
;  debugging convenience) and then break.
;
; BUGBUG: This code doesn't maintain the required 16 byte alignment when running on 64-bit platforms
;         This is not being fixed at the moment, since we're expecting to deprecate this code.

        align 16
__checkStackOverflow proc
        push    PDX
        GET_THREAD_RECORD_FIELD PDX, _activeStackLimit
        cmp     PAX, PDX
        jb      overflowHandler
        pop     PDX
        ret
overflowHandler:
        int     3
        pop     PDX
        ret
__checkStackOverflow endp


?c_LinkStackFunctionsBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA byte 0

?c_LinkStackBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA byte 0

;;; NOTE: If you change this function, please ensure that the necessary
;;; changes are made to CallStack.SkipLinkStackFrame

        align 16

LinkStack proc
        ;; Save allocation amount
        push    PAX
        
        ;; Save argument registers
        push    PCX
        push    PDX
ifdef ISA_IX64
        push    r8
        push    r9
endif

        ;; Call stack allocation ABI - this will update the current thread's stackBegin/Limit
        mov     PCX, [PSP].LinkFrame._alloc
        call    SYMFIX(?g_AllocateStackSegment@Struct_Microsoft_Singularity_V1_Services_StackService@@SIPAUuintPtr@@PAU2@@Z)

        ;; Switch over to new stack (keep old stack in PDX)
        mov     PDX, PSP
        mov     PSP, PAX

        GET_THREAD_CONTEXT_FIELD PAX, _stackLimit
        SET_THREAD_RECORD_FIELD _activeStackLimit, PAX

        ;; Now build up the copied/hijacked stack frame for the grower to continue on

        ;; Copy arguments to new stack
        mov     PCX, [PDX].LinkFrame._argStack
        jecxz   noargs
        lea     PAX, [PDX] + SIZEOF LinkFrame - SIZEOF PWORD
next:   
        push    [PAX+PCX*4]
        loop    next
noargs:
        
        ;; Push hijacked return address.  This will make the function return to our UnlinkStack routine
        ;; rather than its real return address.
        push    [PDX].LinkFrame._UnlinkFn

        ;; Push old ebp frame
        ;; Note that the exception unwind code expects this ebp frame to point to grower's original ebp frame.
        push    PBP

        ;; Reset ebp to the new stack segment.
        mov     PBP, PSP

        ;; Get continue address
        mov     PAX, [PDX].LinkFrame._continue

        ;; Restore arg registers
ifdef ISA_IX64
        mov     r8, [PDX].LinkFrame._r8
        mov     r9, [PDX].LinkFrame._r9
endif
        mov     PCX, [PDX].LinkFrame._cx
        mov     PDX, [PDX].LinkFrame._dx

        ;; Return.  This will resume execution in the prolog of the function which called us.  However
        ;; we are on the new stack segment, and the function has been tail patched so it will call back to
        ;; UnlinkStack when it returns.
        jmp     PAX
        
LinkStack endp

?c_LinkStackLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA byte 0

?c_UnlinkStackBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA byte 0

;; UnlinkStack is essentially a continuation of LinkStack; it is called from the hijacked return
;; pushed by LinkStack.  Because of the unlink stub, we are on the old stack; however we have
;; some cleanup to do.
;; 1. We must call Free on the stack we allocated before, and restore the thread's stack limits.
;; 2. We must update the activeStackLimit on the thread.

;; The stack state on entry to UnlinkStack is:
;; 1. We are back on the old stack
;; 2. Everything from the grower has been popped except its return address & args
;; 3. We have been called by the UnlinkStackN stub; it will execute the return for us

;;; NOTE: If you change this function, please ensure that the necessary
;;; changes are made to CallStack.SkipUnlinkStackFrame

        align 16

UnlinkStack proc

        ;; Save return value registers
        push    PDX
        push    PAX

        ;; HACK: set limit to zero to temporarily disable stack growth
        ;; We can get rid of this if we set activeStackLimit in asm code:
        ;;   ThreadContext *context = Isa.GetCurrentThread();
        ;;   StackHead *head = (StackHead *) (context->stackBegin - sizeof(StackHead));
        ;;   Isa.StackLimit = head->prevLimit;
        xor     PAX, PAX
        SET_THREAD_RECORD_FIELD _activeStackLimit, PAX
        
        ;; Call Free routine
        call    SYMFIX(?g_FreeStackSegment@Struct_Microsoft_Singularity_V1_Services_StackService@@SIXXZ)

        ;; Set active stack limit
        GET_THREAD_CONTEXT_FIELD PAX, _stackLimit
        SET_THREAD_RECORD_FIELD _activeStackLimit, PAX

        POP     PAX
        POP     PDX

        ;; Return to UnlinkStackN stub, which will execute ret N
        ret

UnlinkStack endp

?c_UnlinkStackLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA byte 0

LINKNAME MACRO SIZE:REQ
        EXITM SYMFIX(?g_LinkStack&SIZE&@Class_Microsoft_Singularity_Memory_Stacks@@SIXXZ)
        ENDM
        
UNLINKNAME MACRO SIZE:REQ
        EXITM SYMFIX(?g_UnlinkStack&SIZE&@Class_Microsoft_Singularity_Memory_Stacks@@SIXXZ)
        ENDM
        
;; Implementations of LinkStackNn: push the appropriate number
;; and call the general-purpose LinkStack.

ifdef ISA_IX64        

; x64 does not have a PUSH OFFSET64 instruction, so there are two possible solutions.
;
; (1) LEA into a register and then push it
; (2) Use PUSH reg/mem64 (i.e. FF /6)
;
; Since stack link routines cannot polute any registers, (1) would require save/restore
; overhead as well, making (2) the more desirable solution.

;;; NOTE: If you change these function, please ensure that the necessary
;;; changes are made to CallStack.SkipLinkStackStubFrame

LINKSTACKSTUB MACRO SLOTS:REQ
        LOCAL unlink, uaddr
        align 16
LINKNAME(%SLOTS*8):
        push    SLOTS
        push    [uaddr]
        jmp     LinkStack
uaddr   dq      unlink         
unlink:
        mov     rsp, rbp
        pop     rbp
        call    UnlinkStack
        ret     SLOTS*8
        ENDM
        
elseifdef ISA_IX86
        
LINKSTACKSTUB MACRO SLOTS:REQ
        LOCAL unlink
        align 8
LINKNAME(%SLOTS*4):
        push    SLOTS           
        push    unlink
        jmp     LinkStack
unlink:
        mov     esp, ebp
        pop     ebp
        call    UnlinkStack
        ret     SLOTS*4
        ENDM

endif        

?c_LinkStackStubsBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA byte 0

        LINKSTACKSTUB 0        
        LINKSTACKSTUB 1        
        LINKSTACKSTUB 2        
        LINKSTACKSTUB 3        
        LINKSTACKSTUB 4        
        LINKSTACKSTUB 5        
        LINKSTACKSTUB 6        
        LINKSTACKSTUB 7
        LINKSTACKSTUB 8     
        LINKSTACKSTUB 9        
        LINKSTACKSTUB 10        
        LINKSTACKSTUB 11        
        LINKSTACKSTUB 12        
        LINKSTACKSTUB 13        
        LINKSTACKSTUB 14        
        LINKSTACKSTUB 15        
        LINKSTACKSTUB 16
        LINKSTACKSTUB 17        
        LINKSTACKSTUB 18        
        LINKSTACKSTUB 19        
        LINKSTACKSTUB 20        
        LINKSTACKSTUB 21        
        LINKSTACKSTUB 22        
        LINKSTACKSTUB 23        
        LINKSTACKSTUB 24        
        LINKSTACKSTUB 25        
        LINKSTACKSTUB 26        
        LINKSTACKSTUB 27        
        LINKSTACKSTUB 28        
        LINKSTACKSTUB 29        
        LINKSTACKSTUB 30        
        LINKSTACKSTUB 31        
        LINKSTACKSTUB 32        

?c_LinkStackStubsLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA byte 0

;; CheckStackLimit is the routine that Bartok-generated code calls to check for
;; stack growth

align 16
PUBLIC  __checkStackLimit
__checkStackLimit       PROC
        ;; Note: expected stack growth limit is in PAX

        ;; Bartok doesn't allow quite enough overhead for the stack switch
        ;; now that it occurs in managed code.  So, we will pretend bartok
        ;; asked for more stack until it can be updated.  Note that this
        ;; is not quite sufficient; there are cases where bartok will not
        ;; even probe which we cannot alter.
        sub     eax, 32*sizeof(PWORD)
        
        ;; Free up a register
        push    PDX

ifdef PARANOID_CHECKS

        ;; Free up another register
        push    PCX
        
        ;; See if we are on the interrupt stack
        GET_THREAD_RECORD_FIELD PDX, _activeStackLimit
        GET_CPU_RECORD_FIELD PCX, _interruptStackLimit
        cmp     PCX, PDX
        jne     not_interrupt_stack

        ;; Check for stack underflow
        GET_CPU_RECORD_FIELD PCX, _interruptStackBegin
        cmp     PCX, 0          ; kernel startup?
        je      stack_ok
        cmp     PSP, PCX        ; underflow?
        jl      stack_ok
        int     3

        ;; (Note: we will check for overflow below in the normal code)

not_interrupt_stack:
        GET_THREAD_CONTEXT_FIELD PCX, _stackLimit
        cmp     PCX, PDX
        jne     not_thread_stack

        ;; Check for stack underflow
        GET_THREAD_CONTEXT_FIELD PCX, _stackBegin
        cmp     PCX, 0          ; kernel startup?
        je      stack_ok
        cmp     PSP, PCX        ; underflow?
        jl      stack_ok
        int     3
        
not_thread_stack:
        ;; Check for kernel startup case
        cmp     PCX, 0
        je      stack_ok
        ;; Check for disabled stack limit checks case
        cmp     PDX, 0
        je      stack_ok
        ;; activeStackLimit appears to be bogus
        int     3

stack_ok:

        pop     PCX

endif ; PARANOID_CHECKS

        GET_THREAD_RECORD_FIELD PDX, _activeStackLimit
        cmp     PAX, PDX
        jb      grow
        pop     PDX
        ret

grow:
        ;; Since this is a slow path, always do some extra checks here.

        ;; Check for stack overflow
        cmp     PSP, PDX
        jg      no_overflow
        int     3

no_overflow: 
        ;; Now check to see if we are on the interrupt stack; we shouldn't be growing.
        GET_CPU_RECORD_FIELD PAX, _interruptStackLimit
        cmp     PDX, PAX
        jne     not_interrupt
        int     3

not_interrupt:  
        pop     PDX
        ;; this sets the status bit checked by "jb" above; our caller will be checking this
        stc                     
        ret

    __checkStackLimit       ENDP

?c_LinkStackFunctionsLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA byte 0

end
