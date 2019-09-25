;
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

.code

ifdef SINGULARITY
SINGLE_THREADED equ 0
else ;; SINGULARITY
EXCLUDED equ 0
SINGLE_THREADED equ 0
endif ;; SINGULARITY

include hal.inc

externdef __throwDispatcher:NEAR
externdef __throwDispatcherExplicitAddrAfter:NEAR
; was externdef ?ExceptionTableLookup@@YI_KPEAUClass_System_Exception@@I@Z:NEAR
; don't understand the I -> _K change yet
;;externdef ?ExceptionTableLookup@@YA?AUPtrPair@@PEAUClass_System_Exception@@_K@Z:NEAR
externdef  ?ExceptionTableLookup@@YA?AUPtrPair@@PEAUClass_System_Exception@@_K@Z:NEAR
ifndef SINGULARITY
externdef ?ResetGuardPage@@YAXXZ:NEAR
endif ;; !SINGULARITY

ifdef SINGULARITY_KERNEL
externdef ?g_setStopContext@Class_System_Threading_Thread@@SAXPEAU1@PEAUClass_System_Exception@@@Z:NEAR
externdef __throwBeyondMarker:NEAR
endif ; SINGULARITY_KERNEL

externdef __throwDivideByZeroException:NEAR
externdef __throwNullPointerException:NEAR
externdef __throwOverflowException:NEAR
externdef __throwStackOverflowException:NEAR

ifndef SINGULARITY
externdef ?g_throwNewOverflowException@Class_System_VTable@@SAXXZ:NEAR
externdef ?c_CheckCount@Class_System_GCs_StackManager@@2HA:int32
externdef ?g_GetStackChunk@Class_System_GCs_StackManager@@SAPEAUuintPtr@@PEAU2@PEAUClass_System_Threading_Thread@@_N@Z:NEAR
externdef ?g_ReturnStackChunk@Class_System_GCs_StackManager@@SAXPEAUClass_System_Threading_Thread@@_N@Z:NEAR
;
; externals used to construct instances of machine-level exceptions
;

externdef ?g_AllocateObject@Class_System_GC@@SAPEAUClass_System_Object@@PEAUClass_System_VTable@@@Z:NEAR
externdef ?m__ctor@Class_System_ArithmeticException@@SAXPEAU1@@Z:NEAR
externdef ??_7System_ArithmeticException@@6B@:dword ; vtable
externdef ?m__ctor@Class_System_DivideByZeroException@@SAXPEAU1@@Z:NEAR
externdef ??_7System_DivideByZeroException@@6B@:dword ; vtable
externdef ?m__ctor@Class_System_NullReferenceException@@SAXPEAU1@@Z:NEAR
externdef ??_7System_NullReferenceException@@6B@:dword ;  vtable
externdef ?m__ctor@Class_System_OverflowException@@SAXPEAU1@@Z:NEAR
externdef ??_7System_OverflowException@@6B@:dword ; vtable
externdef ?m__ctor@Class_System_StackOverflowException@@SAXPEAU1@@Z:NEAR
externdef ??_7System_StackOverflowException@@6B@:PTR_Class_System_VTable

externdef ?c_allocationInhibitGC@Class_System_GC@@2_NA:dword

externdef ?g_doubleToInt@Class_System_VTable@@SAHN@Z:NEAR
externdef ?g_doubleToLong@Class_System_VTable@@SA_JN@Z:NEAR
externdef ?g_floatToInt@Class_System_VTable@@SAHM@Z:NEAR
externdef ?g_floatToLong@Class_System_VTable@@SA_JM@Z:NEAR
externdef ?g_checkedDoubleToInt@Class_System_VTable@@SAHN@Z:NEAR
externdef ?g_checkedDoubleToLong@Class_System_VTable@@SA_JN@Z:NEAR
externdef ?g_checkedFloatToInt@Class_System_VTable@@SAHM@Z:NEAR
externdef ?g_checkedFloatToLong@Class_System_VTable@@SA_JM@Z:NEAR

externdef ?g_Abs@Class_System_Math@@SAMM@Z:NEAR
externdef ?g_Abs@Class_System_Math@@SANN@Z:NEAR
externdef ?g_Atan@Class_System_Math@@SANN@Z:NEAR
externdef ?g_Ceiling@Class_System_Math@@SANN@Z:NEAR
externdef ?g_Cos@Class_System_Math@@SANN@Z:NEAR
externdef ?g_Floor@Class_System_Math@@SANN@Z:NEAR
externdef ?g_Log@Class_System_Math@@SANN@Z:NEAR
externdef ?g_Round@Class_System_Math@@SANN@Z:NEAR
externdef ?g_Sin@Class_System_Math@@SANN@Z:NEAR
externdef ?g_Tan@Class_System_Math@@SANN@Z:NEAR
externdef ?g_atan2@Class_System_Math@@SANNN@Z:NEAR
externdef ?g_exp@Class_System_Math@@SANN@Z:NEAR
endif ;; !SINGULARITY

if EXCLUDED
externdef __checkFPStackDepth0:NEAR
externdef __checkFPStackDepth1:NEAR
externdef __checkFPStackDepth2:NEAR
externdef __checkFPStackDepth3:NEAR
externdef __checkFPStackDepth4:NEAR
externdef __checkFPStackDepth5:NEAR
externdef __checkFPStackDepth6:NEAR
externdef __checkFPStackDepth7:NEAR
endif ;; EXCLUDED

        align       8
$DBLMAXINT  DQ      041dfffffffc00000r          ; 2.14747e+009
$DBLMININT  DQ      0c1e0000000000000r          ; -2.14748e+009
$MAXLONG    DQ      07fffffffffffffffh
$MINLONG    DQ      08000000000000000h

;
;  __throwDispatcher(ecx=exception)
;
; Description: this function is called to explicitly throw an exception.
; It assumes that the return address points to the instruction immediately
; after the one where the exception was thrown
;
; Arguments:
;    ecx = exception object
;    [esp] = the return address
; Effects:
;    1. Create ebp chain entry
;    2. Get return address and uses it to calculate the address of the
;       instruction that threw the exception.
;    3. Looks up the appropriate handler and jumps to code to process it.

align 16

__throwDispatcher proc frame
        PrologPush  rbp          ; create ebp chain entry
        SetFramePointer rbp      ; set new ebp
        .endprolog
        mov         rdx, [rbp+8] ; get return address
        push        rcx       ; save exception
        sub         rdx, 1    ; adjust to point to throw location
        ;;  set up parameter
        mov         r8,  rdx
        mov         rdx, rcx
        sub         rsp, 16
        mov         rcx, rsp
        ;;  set up the frame for parameter
        sub         rsp, 32
        call        ?ExceptionTableLookup@@YA?AUPtrPair@@PEAUClass_System_Exception@@_K@Z
        add         rsp, 32
        pop         rax
        pop         rdx
        pop         rcx  ; restore exception
        pop         rbp       ; remove ebp chain
        add         rsp, 8    ; remove eip from the stack
;        mov        rdx is already ok
        jmp         __throwDispatcherHandler
__throwDispatcher endp

;
;  __throwDispatcherExplicitAddr (ecx=exception, edx=throwAddress)
;
; Description:
; This is to be used when the address where the exception occurred
; is passed in as an extra argument
;
; Arguments:
;    ecx = exception object
;    edx = address where the exception was thrown
;


align 16
__throwDispatcherExplicitAddr proc frame
        PrologPush  rcx  ; save exception
        ;; set up paramter
        mov         r8,  rdx
        mov         rdx, rcx
        SubRsp      16
        mov         rcx, rsp
        SubRsp      32
        .endprolog
        call        ?ExceptionTableLookup@@YA?AUPtrPair@@PEAUClass_System_Exception@@_K@Z
        add         rsp, 32
        pop         rax
        pop         rdx
        pop         rcx  ; restore exception
;        mov         rdx is already ok
        jmp         __throwDispatcherHandler
__throwDispatcherExplicitAddr endp

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
__throwDispatcherExplicitAddrAfter proc frame
ifdef SINGULARITY
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
endif
        PrologPush  rcx  ; save exception
        dec         rdx
        ;;  set up paramter
        mov         r8, rdx
        mov         rdx, rcx
        SubRsp      16
        mov         rcx, rsp
        SubRsp      32
        .endprolog
        call        ?ExceptionTableLookup@@YA?AUPtrPair@@PEAUClass_System_Exception@@_K@Z
        add         rsp, 32
        pop         rax
        pop         rdx
        pop         rcx  ; restore exception
;        mov         edx is already ok
        jmp         __throwDispatcherHandler
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
endif ; SINGULARITY_KERNEL


;  __throwDispatcherHandler (eax=frameSetupInfo or exceptionType,
;                            ecx=exception,
;                            edx=spillSize,frameSetupSize, or handlerAddress
;
; Description:
;    After the exception table entry has been found, the values are passed here
;    for processing.  This method simply checks for the easy case of an explicit
;    handler (known if the exceptionType is given <-- low bit is zero).
;    In this case it simply jumps to the handler.  Otherwise it passes the
;    information along to __throwDispatcherUnwind.
;
; Arguments:
;    If low bit of eax is set:
;        eax = frame setup information
;        ecx = exception object
;        edx = spill size excluding callee-save register saves
;              or offset from ebp to end of callee-save register saves
;    Otherwise:
;        eax = exception type (unused)
;        ecx = exception object
;        edx = handler address

align 16
__throwDispatcherHandler proc ;frame
                ;.endprolog
        test        rax, 1
        jne         __throwDispatcherUnwind
        ;; ecx=exception, edx=handler
        jmp         rdx
__throwDispatcherHandler endp

;  __throwDispatcherUnwind (eax=frame setup info, ecx=exception, edx=spill size
;
; Description:
;    This is the global unwind handler.  It is used to unwind a single stack
;    frame if there are no explicit handlers that catch an exception in a given
;    function.
;
; Arguments:
;    eax = frame setup information, must have low bit set
;    ecx = exception object
;    edx = spill size excluding callee-save register saves
;          or offset from ebp to end of callee-save register saves
;
; See tables\ExceptionTable.cs for details on these values

align 16
__throwDispatcherUnwind proc ;frame
                ;.endprolog
        ;; eax=frame info
        ;; edx=spill size

        ;; obviously ebp isn't useful under frame pointer omission
        ;; but less obviously esp may be invalid if ebp is good
        ;; (e.g. under varargs we may not have known how many arguments to
        ;; pop; this is one reason why varargs turns off frame pointer omission)
        test        rax, 2h
        jne         esp_is_good
        ;; ebp_is_good
        add         rdx, rbp
        mov         rsp, rdx
        jmp         esp_is_setup
esp_is_good:
        ;; pop spill slots
        add         rsp, rdx

esp_is_setup:

        ;; restore callee-saves and pop values from stack
        ;; (excludes ebp if used as the frame pointer)

; restore float registers
        test        rax, 100000h
        je          skip_xmm15_restore
        ;; restore xmm15
        movdqa		xmm15, [rsp]
        add			rsp, 16
skip_xmm15_restore:
        test        rax, 80000h
        je          skip_xmm14_restore
        ;; restore xmm14
        movdqa		xmm14, [rsp]
        add			rsp, 16
skip_xmm14_restore:
        test        rax, 40000h
        je          skip_xmm13_restore
        ;; restore xmm13
        movdqa		xmm13, [rsp]
        add			rsp, 16
skip_xmm13_restore:
        test        rax, 20000h
        je          skip_xmm12_restore
        ;; restore xmm12
        movdqa		xmm12, [rsp]
        add			rsp, 16
skip_xmm12_restore:
        test        rax, 10000h
        je          skip_xmm11_restore
        ;; restore xmm11
        movdqa		xmm11, [rsp]
        add			rsp, 16
skip_xmm11_restore:
        test        rax, 8000h
        je          skip_xmm10_restore
        ;; restore xmm10
        movdqa		xmm10, [rsp]
        add			rsp, 16
skip_xmm10_restore:
        test        rax, 4000h
        je          skip_xmm9_restore
        ;; restore xmm9
        movdqa		xmm9, [rsp]
        add			rsp, 16
skip_xmm9_restore:
        test        rax, 2000h
        je          skip_xmm8_restore
        ;; restore xmm8
        movdqa		xmm8, [rsp]
        add			rsp, 16
skip_xmm8_restore:
        test        rax, 1000h
        je          skip_xmm7_restore
        ;; restore xmm7
        movdqa		xmm7, [rsp]
        add			rsp, 16
skip_xmm7_restore:
        test        rax, 800h
        je          skip_xmm6_restore
        ;; restore xmm6
        movdqa		xmm6, [rsp]
        add			rsp, 16
skip_xmm6_restore:

; account of alignment
        test        rax, 200000h
        je          skip_align_xmm
        ;; add 8 to rsp for alignment
        add			rsp, 8
skip_align_xmm:

; restore int registers
        test        rax, 400h
        je          skip_r15_restore
        ;; restore r15
        pop         r15
skip_r15_restore:
        test        rax, 200h
        je          skip_r14_restore
        ;; restore r14
        pop         r14
skip_r14_restore:
        test        rax, 100h
        je          skip_r13_restore
        ;; restore r13
        pop         r13
skip_r13_restore:
        test        rax, 80h
        je          skip_r12_restore
        ;; restore r12
        pop         r12
skip_r12_restore:
        test        rax, 4h
        je          skip_edi_restore
        ;; restore edi
        pop         rdi
skip_edi_restore:
        test        rax, 8h
        je          skip_esi_restore
        ;; restore esi
        pop         rsi
skip_esi_restore:
        test        rax, 10h
        je          skip_ebp_restore
        ;; restore ebp
        pop         rbp
skip_ebp_restore:
        test        rax, 20h
        je          skip_ebx_restore
        ;; restore ebx
        pop         rbx
skip_ebx_restore:

        test        rax, 40h
        je          skip_jump_transition_record
        ;; jump over transition record
        add         rsp, (SIZE Struct_System_GCs_CallStack_TransitionRecord)
skip_jump_transition_record:

        ;; restore ebp if it was used as the frame pointer
        test        rax, 2h
        jne         skip_frame_pointer_restore
        ;; restore frame pointer (esp == ebp already)
        pop         rbp
skip_frame_pointer_restore:

        ;; set edx=return address
        pop         rdx

        ;; no arguments to pop

        ;; At this point
        ;; ecx=exception, edx=return address
        ;; esi/edi/ebx/ebp/esp have been restored
        ;; eax is scratch

        ;; set up next handler search
        jmp         __throwDispatcherExplicitAddrAfter
__throwDispatcherUnwind endp

;
; __throwDivideByZeroException: instantiate an divide-by-zero exception
; and throw it.
;
; Assumes rdx points to the address after the one that threw.
;

align 16
__throwDivideByZeroException proc frame
        PrologPush rbx
        PrologPush rsi
        .endprolog
        mov rbx,rdx  ; save address
if SINGLE_THREADED
        inc ?c_allocationInhibitGC@Class_System_GC@@2_NA
else ; SINGLE_THREADED
        lock inc ?c_allocationInhibitGC@Class_System_GC@@2_NA
endif ; SINGLE_THREADED
        mov rcx,offset ??_7System_DivideByZeroException@@6B@
        call ?g_AllocateObject@Class_System_GC@@SAPEAUClass_System_Object@@PEAUClass_System_VTable@@@Z
        mov rsi,rax  ; save pointer to instance of exception
        mov rcx,rax  ; initialize instance
        call ?m__ctor@Class_System_DivideByZeroException@@SAXPEAU1@@Z
if SINGLE_THREADED
        dec ?c_allocationInhibitGC@Class_System_GC@@2_NA
else ; SINGLE_THREADED
        lock dec ?c_allocationInhibitGC@Class_System_GC@@2_NA
endif ; SINGLE_THREADED
        mov rcx,rsi
        mov rdx,rbx
        pop rsi
        pop rbx
        jmp __throwDispatcherExplicitAddr
__throwDivideByZeroException endp

;
; __throwStackOverflowException: instantiate an StackOverflow exception
; and throw it.
;
; Assumes edx points to the address of the instruction that faulted
;

align 16
__throwStackOverflowException proc frame
        PrologPush rbx
        PrologPush rsi
        .endprolog
        mov rbx,rdx  ; save address
if SINGLE_THREADED
        inc ?c_allocationInhibitGC@Class_System_GC@@2_NA
else ; SINGLE_THREADED
        lock inc ?c_allocationInhibitGC@Class_System_GC@@2_NA
endif ; MULTI_THREADED
        mov rcx,offset ??_7System_StackOverflowException@@6B@
        call ?g_AllocateObject@Class_System_GC@@SAPEAUClass_System_Object@@PEAUClass_System_VTable@@@Z
        mov rsi,rax  ; save pointer to instance of exception
        mov rcx,rax  ; initialize instance
        call ?m__ctor@Class_System_StackOverflowException@@SAXPEAU1@@Z
if SINGLE_THREADED
        dec ?c_allocationInhibitGC@Class_System_GC@@2_NA
else ; SINGLE_THREADED
        lock dec ?c_allocationInhibitGC@Class_System_GC@@2_NA
endif ; MULTI_THREADED
        ;; set up paramter
        mov rdx, rsi
        mov r8, rbx
        sub rsp, 16
        mov rcx, rsp
        sub rsp, 32
        call ?ExceptionTableLookup@@YA?AUPtrPair@@PEAUClass_System_Exception@@_K@Z
        add rsp, 32
        pop rax
        pop rdx
ifndef SINGULARITY
        push rsi
        push rdx
        call ?ResetGuardPage@@YAXXZ
        pop rdx
        pop rax
endif
        pop rsi
        pop rbx
        mov rcx,rax
;        mov rdx is already ok
        jmp rdx
__throwStackOverflowException endp

;
; __throwNullReferenceException: instantiate an NullReference exception
; and throw it.
;
; Assumes edx points to the address of the instruction that faulted
;

align 16
__throwNullReferenceException proc frame
        PrologPush rbx
        PrologPush rsi
        .endprolog
        mov rbx,rdx  ; save address
if SINGLE_THREADED
        inc ?c_allocationInhibitGC@Class_System_GC@@2_NA
else ; SINGLE_THREADED
        lock inc ?c_allocationInhibitGC@Class_System_GC@@2_NA
endif ; SINGLE_THREADED
        mov rcx,offset ??_7System_NullReferenceException@@6B@
        call ?g_AllocateObject@Class_System_GC@@SAPEAUClass_System_Object@@PEAUClass_System_VTable@@@Z
        mov rsi,rax  ; save pointer to instance of exception
        mov rcx,rax  ; initialize instance
        call ?m__ctor@Class_System_NullReferenceException@@SAXPEAU1@@Z
if SINGLE_THREADED
        dec ?c_allocationInhibitGC@Class_System_GC@@2_NA
else ; SINGLE_THREADED
        lock dec ?c_allocationInhibitGC@Class_System_GC@@2_NA
endif ; SINGLE_THREADED
        mov rcx,rsi
        mov rdx,rbx
        pop rsi
        pop rbx
        jmp __throwDispatcherExplicitAddr
__throwNullReferenceException endp

;
; __throwDivideByZeroException: instantiate an divide-by-zero exception
; and throw it.
;
; Assumes rdx points to the address of the instruction that faulted
;

align 16
__throwOverflowException proc frame
        PrologPush rbx
        PrologPush rsi
        .endprolog
        mov rbx,rdx  ; save address
if SINGLE_THREADED
        inc ?c_allocationInhibitGC@Class_System_GC@@2_NA
else ; SINGLE_THREADED
        lock inc ?c_allocationInhibitGC@Class_System_GC@@2_NA
endif ; SINGLE_THREADED
        mov rcx,offset ??_7System_OverflowException@@6B@
        call ?g_AllocateObject@Class_System_GC@@SAPEAUClass_System_Object@@PEAUClass_System_VTable@@@Z
        mov rsi,rax  ; save pointer to instance of exception
        mov rcx,rax  ; initialize instance
        call ?m__ctor@Class_System_OverflowException@@SAXPEAU1@@Z
if SINGLE_THREADED
        dec ?c_allocationInhibitGC@Class_System_GC@@2_NA
else ; SINGLE_THREADED
        lock dec ?c_allocationInhibitGC@Class_System_GC@@2_NA
endif ; SINGLE_THREADED
        mov rcx,rsi
        mov rdx,rbx
        pop rsi
        pop rbx
        jmp __throwDispatcherExplicitAddr
__throwOverflowException endp


ifdef SINGULARITY_KERNEL
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


ifdef SINGULARITY
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
endif

;
;  int System.VTable.doubleToInt(double)
;

align 16
?g_doubleToInt@Class_System_VTable@@SAHN@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        SubRsp      8
        .endprolog
        movsd       real8 ptr [rbp+16], xmm0
        fld         real8 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        mov         ax,word ptr [rbp-2]
        or          eax,0C00h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        fistp       dword ptr [rbp-8]
        fldcw       word ptr [rbp-2]
        mov         eax,dword ptr [rbp-8]

        cmp         eax,080000000h
        je          possible_overflow
return:
        mov         rsp,rbp
        pop         rbp
        ret

possible_overflow:
        fld         real8 ptr [rbp+16]
        fcomp       real8 ptr $DBLMAXINT
        fnstsw      ax
        test        ah,4
        jne         short return_zero
        test        ah,1
        jne         short return_MININT

return_MAXINT:
        mov         eax, 07fffffffh
        jmp         short return

return_zero:
        xor         eax, eax
        jmp         short return

return_MININT:
        mov         eax, 080000000h
        jmp         short return

?g_doubleToInt@Class_System_VTable@@SAHN@Z endp

;
;  long System.VTable.doubleToLong(double)
;

align 16
?g_doubleToLong@Class_System_VTable@@SA_JN@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        .endprolog
        add         rsp,-12
        movsd       real8 ptr [rbp+16], xmm0
        fld         real8 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        mov         ax,word ptr [rbp-2]
        or          eax,0C00h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        fistp       qword ptr [rbp-12]
        fldcw       word ptr [rbp-2]
        mov         rax,qword ptr [rbp-12]
        mov         rdx,08000000000000000h
        cmp         rax,rdx
        je          possible_overflow
return:
        mov         rsp,rbp
        pop         rbp
        ret

possible_overflow:
        mov         rdx,rax                    ; save lsw
        fld         real8 ptr [rbp+16]
        fild        qword ptr $MAXLONG
        fcompp
        fnstsw      ax
        test        ah,4
        jne         short return_zero
        test        ah,65
        je          short check_MINLONG

return_MAXLONG:
        mov         rax, 07fffffffffffffffh
        jmp         short return

return_zero:
        xor         rax, rax
        jmp         short return

check_MINLONG:
        fld         real8 ptr [rbp+16]
        fild        qword ptr $MINLONG
        fcompp
        fnstsw      ax
        test        ah,1
        jne         short return_original

return_MINLONG:
        mov         rax, 08000000000000000h
        jmp         short return

return_original:
        mov         rax, rdx                   ; restore lsw to eax
        mov         rdx, 08000000000000000h
        and         rax, rdx
        jmp         short return

?g_doubleToLong@Class_System_VTable@@SA_JN@Z endp

;
;  int System.VTable.floatToInt(float)
;

align 16
?g_floatToInt@Class_System_VTable@@SAHM@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        SubRsp      8
        .endprolog
        movss       real4 ptr [rbp+16], xmm0
        fld         real4 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        xor         eax,eax
        mov         ax,word ptr [rbp-2]
        or          eax,0C00h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        fistp       dword ptr [rbp-8]
        fldcw       word ptr [rbp-2]
        mov         eax,dword ptr [rbp-8]

        cmp         eax,080000000h
        je          possible_overflow
return:
        mov         rsp,rbp
        pop         rbp
        ret

possible_overflow:
        fld         real4 ptr [rbp+16]
        fcomp       real8 ptr $DBLMAXINT
        fnstsw      ax
        test        ah,4
        jne         short return_zero
        test        ah,1
        jne         short return_MININT
        mov         eax, 07fffffffh
        jmp         short return

return_zero:
        xor         eax, eax
        jmp         short return

return_MININT:
        mov         eax, 080000000h
        jmp         short return

?g_floatToInt@Class_System_VTable@@SAHM@Z endp

;
;  long System.VTable.floatToLong(float)
;

align 16
?g_floatToLong@Class_System_VTable@@SA_JM@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        .endprolog
        add         rsp,-12
        movss       real4 ptr [rbp+16], xmm0
        fld         real4 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        mov         ax,word ptr [rbp-2]
        or          eax,0C00h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        fistp       qword ptr [rbp-12]
        fldcw       word ptr [rbp-2]
        mov         rax,qword ptr [rbp-12]
        mov         rdx,08000000000000000h
        cmp         rax,rdx
        je          possible_overflow
return:
        mov         rsp,rbp
        pop         rbp
        ret

possible_overflow:
        mov         rdx,rax                    ; save lsw
        fld         real4 ptr [rbp+16]
        fild        qword ptr $MAXLONG
        fcompp
        fnstsw      ax
        test        ah,4
        jne         short return_zero
        test        ah,65
        je          short check_MINLONG

return_MAXLONG:
        mov         rax, 07fffffffffffffffh
        jmp         short return

return_zero:
        xor         rax, rax
        jmp         short return

check_MINLONG:
        fld         real4 ptr [rbp+16]
        fild        qword ptr $MINLONG
        fcompp
        fnstsw      ax
        test        ah,1
        jne         short return_original

return_MINLONG:
        mov         rax, 08000000000000000h
        jmp         short return

return_original:
        mov         rax, rdx                   ; restore lsw to eax
        mov         rdx, 08000000000000000h
        and         rax, rdx
        jmp         short return

?g_floatToLong@Class_System_VTable@@SA_JM@Z endp

;
;  int System.VTable.checkedDoubleToInt(double)
;

align 16
?g_checkedDoubleToInt@Class_System_VTable@@SAHN@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        SubRsp      8
        .endprolog
        movsd       real8 ptr [rbp+16], xmm0
        fld         real8 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        mov         ax,word ptr [rbp-2]
        or          eax,0C00h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        fistp       dword ptr [rbp-8]
        fldcw       word ptr [rbp-2]
        mov         eax,dword ptr [rbp-8]

        cmp         eax,080000000h
        je          possible_overflow
return:
        mov         rsp,rbp
        pop         rbp
        ret

possible_overflow:
        fld         real8 ptr [rbp+16]
        fcomp       real8 ptr $DBLMAXINT
        fnstsw      ax
        test        ah,4                    ; test for unordered
        jne         short throw_exception
        test        ah,1                    ; test for <$DBLMAXINT
        jne         short return_MININT
        ; src > $DBLMAXINT
        ; throw an overflow exception
        jmp         short throw_exception

return_MININT:
        ; check against $DBLMININT
        fld         real8 ptr [rbp+16]
        fcomp       real8 ptr $DBLMININT
        fnstsw      ax
        test        ah, 1                       ; test for < $DBLMININT
        jne         short throw_exception ; throw exception if true
        mov         eax, 080000000h
        jmp         short return

throw_exception:
        ; throw an overflow exception
        ; set up stack frame so that it looks like a call to throwNewOverflowException
        ; from the caller of this function.
        mov         rsp,rbp
        pop         rbp
;        pop         rax       ; grab return address
;        add         rsp, 8    ; move rsp pass the first parameter.
;        mov         [rsp],rax ; overwrite argument
        jmp         ?g_throwNewOverflowException@Class_System_VTable@@SAXXZ

?g_checkedDoubleToInt@Class_System_VTable@@SAHN@Z endp

;
;  long System.VTable.checkedDoubleToLong(double)
;

align 16
?g_checkedDoubleToLong@Class_System_VTable@@SA_JN@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        .endprolog
        add         rsp,-12
        movsd       real8 ptr [rbp+16], xmm0
        fld         real8 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        mov         ax,word ptr [rbp-2]
        or          eax,0C00h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        fistp       qword ptr [rbp-12]
        fldcw       word ptr [rbp-2]
        mov         rax,qword ptr [rbp-12]
        mov         rdx,08000000000000000h
        cmp         rax, rdx
        je          possible_overflow
return:
        mov         rsp,rbp
        pop         rbp
        ret

possible_overflow:
        mov         rdx,rax                    ; save lsw
        fld         real8 ptr [rbp+16]
        fild        qword ptr $MAXLONG
        fcompp
        fnstsw      ax
        test        ah,4                       ; test for unordered
        jne         short return_zero
        test        ah,65                      ; test for <= $MAXLONG
        je          short check_MINLONG

return_MAXLONG:
        ; src > $MAXLONG
        ; throw an exception
        jmp         short throw_exception

return_zero:
        jmp         short throw_exception

check_MINLONG:
        ; src <= $MINLONG
        fild        qword ptr $MINLONG
        fld         real8 ptr [rbp+16]
        fcompp                       ; real8 ptr [rbp+8] < $MINLONG
        fnstsw      ax
        test        ah,1
        jne         short throw_exception

return_MINLONG:
        mov         rax, rdx                   ; restore lsw to eax
        mov         rdx, 08000000000000000h
        and         rax, rdx
        jmp         short return


throw_exception:
        ; throw an overflow exception
        ; set up stack frame so that it looks like a call to throwNewOverflowException
        ; from the caller of this function.
        mov         rsp,rbp
        pop         rbp
        ;pop         rax       ; grab return address
        ;add         rsp, 8    ; move rsp pass the first parameter.
        ;mov         [rsp],eax ; overwrite argument
        jmp         ?g_throwNewOverflowException@Class_System_VTable@@SAXXZ

?g_checkedDoubleToLong@Class_System_VTable@@SA_JN@Z endp

;
;  int System.VTable.checkedFloatToInt(float)
;

align 16
?g_checkedFloatToInt@Class_System_VTable@@SAHM@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        SubRsp      8
        .endprolog
        movss       real4 ptr [rbp+16], xmm0
        fld         real4 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        xor         eax,eax
        mov         ax,word ptr [rbp-2]
        or          eax,0C00h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        fistp       dword ptr [rbp-8]
        fldcw       word ptr [rbp-2]
        mov         eax,dword ptr [rbp-8]

        cmp         eax,080000000h
        je          possible_overflow

return:
        mov         rsp,rbp
        pop         rbp
        ret

possible_overflow:
        fld         real4 ptr [rbp+16]
        fcomp       real8 ptr $DBLMAXINT
        fnstsw      ax
        test        ah,4                        ; test for unordered
        jne         short throw_exception
        test        ah,1                        ; test for src < $DBLMAXINT
        jne         short return_MININT
        ; src > $DBLMAXINT
        ; throw an overflow exception
        jmp         short throw_exception

return_MININT:
        ; need to check against $DBLMININT, if it is less than,
        ; then throw an overflow exception
        fld         real4 ptr [rbp+16]
        fcomp       real8 ptr $DBLMININT
        fnstsw      ax
        test        ah,1                        ; test for less than
        jne         short throw_exception
        mov         eax, 080000000h
        jmp         short return

throw_exception:
        ; throw an overflow exception
        ; set up stack frame so that it looks like a call to throwNewOverflowException
        ; from the caller of this function.
        mov         rsp,rbp
        pop         rbp
        ;pop         rax       ; grab return address
        ;mov         [rsp],eax ; overwrite argument
        jmp         ?g_throwNewOverflowException@Class_System_VTable@@SAXXZ

?g_checkedFloatToInt@Class_System_VTable@@SAHM@Z endp

;
;  long System.VTable.checkedFloatToLong(float)
;

align 16
?g_checkedFloatToLong@Class_System_VTable@@SA_JM@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        .endprolog
        add         rsp,-12
        movss       real4 ptr [rbp+16], xmm0
        fld         real4 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        mov         ax,word ptr [rbp-2]
        or          eax,0C00h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        fistp       qword ptr [rbp-12]
        fldcw       word ptr [rbp-2]
        mov         rax,qword ptr [rbp-12]
        mov         rdx,08000000000000000h
        cmp         rax,rdx
        je          possible_overflow
return:
        mov         rsp,rbp
        pop         rbp
        ret

possible_overflow:
        mov         rdx,rax                    ; save lsw
        fld         real4 ptr [rbp+16]
        fild        qword ptr $MAXLONG
        fcompp
        fnstsw      ax
        test        ah,4                        ; test for unordered
        jne         short return_zero
        test        ah,65                       ; test for <= $MAXLONG
        je          short check_MINLONG

return_MAXLONG:
        ; src > $MAXLONG
        ; throw an exception
        jmp         short throw_exception

return_zero:
        ; compare with $MAXLONG results in unordered
        ; throw an overflow exception
        jmp         short throw_exception

check_MINLONG:
        ; src <= $MINLONG
        fild        qword ptr $MINLONG
        fld         real4 ptr [rbp+16]
        fcompp                                  ; real8 ptr [rbp+8] < $MINLONG
        fnstsw      ax
        test        ah,1
        jne         short throw_exception ;  throw an overflow exception when src < $MINLONG
return_MINLONG:
        mov         rax, rdx        ;  restore lsw
        mov         rdx, 08000000000000000h
        and         rax, rdx
        jmp         short return

throw_exception:
        ; throw an overflow exception
        ; set up stack frame so that it looks like a call to throwNewOverflowException
        ; from the caller of this function.
        mov         rsp,rbp
        pop         rbp
        ;pop         rax       ; grab return address
        ;mov         [rsp],eax ; overwrite argument
        jmp         ?g_throwNewOverflowException@Class_System_VTable@@SAXXZ

?g_checkedFloatToLong@Class_System_VTable@@SA_JM@Z endp

;
;  double System.Math.Sin(double)
;

align 16
?g_Sin@Class_System_Math@@SANN@Z proc ;frame
                ;.endprolog
        add     rsp, -8
        movsd   real8 ptr [rsp+16], xmm0
        fld     real8 ptr [rsp+16]
        fsin
        fstp    real8 ptr [rsp]
        movsd   xmm0, real8 ptr [rsp]
        add     rsp, 8
        ret
?g_Sin@Class_System_Math@@SANN@Z endp

;
;  double System.Math.Cos(double)
;

align 16
?g_Cos@Class_System_Math@@SANN@Z proc ;frame
                ;.endprolog
        add     rsp, -8
        movsd   real8 ptr [rsp+16], xmm0
        fld     real8 ptr [rsp+16]
        fcos
        fstp    real8 ptr [rsp]
        movsd   xmm0, real8 ptr [rsp]
        add     rsp, 8
        ret
?g_Cos@Class_System_Math@@SANN@Z endp

;
;  double System.Math.Tan(double)
;

align 16
?g_Tan@Class_System_Math@@SANN@Z proc ;frame
                ;.endprolog
        add     rsp, -8
        movsd   real8 ptr [rsp+16], xmm0
        fld     real8 ptr [rsp+16]
        fptan
        fstp    real8 ptr [rsp]
        movsd   xmm0, real8 ptr [rsp]
        add     rsp, 8
        ret
?g_Tan@Class_System_Math@@SANN@Z endp

;
;
;  double System.Math.Atan(double)
;

align 16
?g_Atan@Class_System_Math@@SANN@Z proc ;frame
                ;.endprolog
        add     rsp, -8
        movsd   real8 ptr [rsp+16], xmm0
        fld     real8 ptr [rsp+16]
        fld1
        fpatan
        fstp    real8 ptr [rsp]
        movsd   xmm0, real8 ptr [rsp]
        add     rsp, 8
        ret
?g_Atan@Class_System_Math@@SANN@Z endp

;
;  double System.Math.atan2(double,double)
;

align 16
?g_atan2@Class_System_Math@@SANNN@Z proc ;frame
                ;.endprolog
        add     rsp, -8
        movsd   real8 ptr [rsp+16], xmm0
        movsd   real8 ptr [rsp+24], xmm1
        fld     real8 ptr [rsp+16]
        fld     real8 ptr [rsp+24]
        fpatan
        fstp    real8 ptr [rsp]
        movsd   xmm0, real8 ptr [rsp]
        add     rsp, 8
        ret
?g_atan2@Class_System_Math@@SANNN@Z endp

;
;  double System.Math.exp(double)
;

align 16
?g_exp@Class_System_Math@@SANN@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        SubRsp      8
        .endprolog

        fldl2e
        movsd       real8 ptr [rbp+16], xmm0
        fmul        real8 ptr [rbp+16]
        fld         st(0)
        frndint
        fxch        st(1)
        fsub        st(0), st(1)
        f2xm1
        fld1
        faddp       st(1), st(0)
        fscale
;isNaN??
        fstp        st(1)

        fstp        real8 ptr [rbp-8]
        movsd       xmm0, real8 ptr [rbp-8]
        mov         rsp,rbp
        pop         rbp
        ret
?g_exp@Class_System_Math@@SANN@Z endp

;
;  double System.Math.log(double)
;

align 16
?g_Log@Class_System_Math@@SANN@Z proc ;frame
                ;.endprolog
        add         rsp, -8
        fldln2
        movsd       real8 ptr [rsp+16], xmm0
        fld         real8 ptr [rsp+16]
        fyl2x
        fstp        real8 ptr [rsp]
        movsd       xmm0, real8 ptr [rsp]
        add         rsp, 8
        ret
?g_Log@Class_System_Math@@SANN@Z endp

;
;  double System.Math.Ceiling(double)
;

align 16
?g_Ceiling@Class_System_Math@@SANN@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        SubRsp      8
        .endprolog

        movsd       real8 ptr [rbp+16], xmm0
        fld         real8 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        mov         ax,word ptr [rbp-2]
        and         ah,0F3h
        or          ah,008h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        frndint
        fldcw       word ptr [rbp-2]

        fstp        real8 ptr [rbp-8]
        movsd       xmm0, real8 ptr [rbp-8]
        mov         rsp,rbp
        pop         rbp
        ret
?g_Ceiling@Class_System_Math@@SANN@Z endp

;
;  double System.Math.Floor(double)
;

align 16
?g_Floor@Class_System_Math@@SANN@Z proc frame
        PrologPush  rbp
        SetFramePointer rbp
        SubRsp      8
        .endprolog

        movsd       real8 ptr [rsp+16], xmm0
        fld         real8 ptr [rbp+16]
        wait
        fnstcw      word ptr [rbp-2]
        wait
        mov         ax,word ptr [rbp-2]
        and         ah,0F3h
        or          ah,004h
        mov         word ptr [rbp-4],ax
        fldcw       word ptr [rbp-4]
        frndint
        fldcw       word ptr [rbp-2]

        fstp        real8 ptr [rbp-8]
        movsd       xmm0, real8 ptr [rbp-8]
        mov         rsp,rbp
        pop         rbp
        ret
?g_Floor@Class_System_Math@@SANN@Z endp

;
;  double System.Math.Round(double)
;

align 16
?g_Round@Class_System_Math@@SANN@Z proc ;frame
                ;.endprolog
        add         rsp, -8
        movsd       real8 ptr [rsp+16], xmm0
        fld         real8 ptr [rsp+16]
        frndint
        fstp        real8 ptr [rsp]
        movsd       xmm0, real8 ptr [rsp]
        add         rsp, 8
        ret
?g_Round@Class_System_Math@@SANN@Z endp

;
;  float System.Math.Abs(float)
;

align 16
?g_abs@Class_System_Math@@SAMM@Z proc ;frame
                ;.endprolog
        add         rsp, -8
        movss       real4 ptr [rsp+16], xmm0
        fld         real4 ptr [rsp+16]
        fabs
        fstp        real4 ptr [rsp]
        movss       xmm0, real4 ptr [rsp]
        add         rsp, 8
        ret
?g_abs@Class_System_Math@@SAMM@Z endp

;
;  double System.Math.Abs(double)
;

align 16
?g_abs@Class_System_Math@@SANN@Z proc ;frame
                ;.endprolog
        add         rsp, -8
        movsd       real8 ptr [rsp+16], xmm0
        fld         real8 ptr [rsp+16]
        fabs
        fstp        real8 ptr [rsp]
        movsd       xmm0, real8 ptr [rsp]
        add         rsp, 8
        ret
?g_abs@Class_System_Math@@SANN@Z endp

align 16
?g_floatRem@Class_System_VTable@@SAMMM@Z proc ;frame
                ;.endprolog
        add     rsp, -8
        movss   real4 ptr [rsp+16], xmm0
        movss   real4 ptr [rsp+24], xmm1
        fld     real4 ptr [rsp+24]
        fld     real4 ptr [rsp+16]
fremloop:
        fprem
        fstsw   ax
        fwait
        sahf
        jp      fremloop    ; Continue while the FPU status bit C2 is set
        ffree st(1)
        fstp    real4 ptr [rsp]
        movss   xmm0, real4 ptr [rsp]
        add     rsp, 8
        ret
?g_floatRem@Class_System_VTable@@SAMMM@Z endp

align 16
?g_doubleRem@Class_System_VTable@@SANNN@Z proc ;frame
                ;.endprolog
        add     rsp, -8
        movsd   real8 ptr [rsp+16], xmm0
        movsd   real8 ptr [rsp+24], xmm1
        fld     real8 ptr [rsp+24]
        fld     real8 ptr [rsp+16]
fremloop:
        fprem
        fstsw   ax
        fwait
        sahf
        jp      fremloop    ; Continue while the FPU status bit C2 is set
        ffree st(1)
        fstp    real8 ptr [rsp]
        movsd   xmm0, real8 ptr [rsp]
        add     rsp, 8
        ret
?g_doubleRem@Class_System_VTable@@SANNN@Z endp

extern ?brtmain@@3P6AHPEAUClassVector_Class_System_String@@@ZEA:qword

align 16
?g_CallMain@Class_Microsoft_Singularity_AppRuntime@@SAHPEAUClassVector_Class_System_String@@@Z proc
        jmp     qword ptr [?brtmain@@3P6AHPEAUClassVector_Class_System_String@@@ZEA]
?g_CallMain@Class_Microsoft_Singularity_AppRuntime@@SAHPEAUClassVector_Class_System_String@@@Z endp

end

