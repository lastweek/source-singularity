; 
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

include core.inc

externdef __throwDispatcher:NEAR
externdef __throwDispatcherExplicitAddrAfter:NEAR
externdef __throwDispatcherExplicitAddrAfterCore:NEAR
externdef ?ExceptionTableLookup@@YI_KPAUClass_System_Exception@@I@Z:NEAR

externdef __throwDivideByZeroException:NEAR
externdef __throwNullPointerException:NEAR
externdef __throwOverflowException:NEAR
externdef __throwStackOverflowException:NEAR

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

__throwDispatcher proc
        push        ebp          ; create ebp chain entry
        mov         ebp, esp     ; set new ebp
        mov         edx, [ebp+4] ; get return address
        push        ecx       ; save exception
        sub         edx, 1    ; adjust to point to throw location
        call        ?ExceptionTableLookup@@YI_KPAUClass_System_Exception@@I@Z
        pop         ecx  ; restore exception
        pop         ebp       ; remove ebp chain
        add         esp, 4    ; remove eip from the stack
;        mov        edx is already ok
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
__throwDispatcherExplicitAddr proc
        push        ecx  ; save exception
        call        ?ExceptionTableLookup@@YI_KPAUClass_System_Exception@@I@Z
        pop         ecx  ; restore exception
;        mov         edx is already ok
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
__throwDispatcherExplicitAddrAfterCore proc
        push        ecx  ; save exception 
        dec         edx
        call        ?ExceptionTableLookup@@YI_KPAUClass_System_Exception@@I@Z
        pop         ecx  ; restore exception
;        mov         edx is already ok
        jmp         __throwDispatcherHandler
__throwDispatcherExplicitAddrAfterCore endp

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
__throwDispatcherHandler proc
        test        eax, 1
        jne         __throwDispatcherUnwind
        ;; ecx=exception, edx=handler
        jmp         edx
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
__throwDispatcherUnwind proc
        ;; eax=frame info
        ;; edx=spill size

        ;; obviously ebp isn't useful under frame pointer omission
        ;; but less obviously esp may be invalid if ebp is good
        ;; (e.g. under varargs we may not have known how many arguments to
        ;; pop; this is one reason why varargs turns off frame pointer omission)
        test        eax, 2h
        jne         esp_is_good
        ;; ebp_is_good
        add         edx, ebp
        mov         esp, edx
        jmp         esp_is_setup
esp_is_good:
        ;; pop spill slots
        add         esp, edx

esp_is_setup:

        ;; restore callee-saves and pop values from stack
        ;; (excludes ebp if used as the frame pointer)
        test        eax, 4h
        je          skip_edi_restore
        ;; restore edi
        pop         edi
skip_edi_restore:
        test        eax, 8h
        je          skip_esi_restore
        ;; restore esi
        pop         esi
skip_esi_restore:
        test        eax, 10h
        je          skip_ebp_restore
        ;; restore ebp
        pop         ebp
skip_ebp_restore:
        test        eax, 20h
        je          skip_ebx_restore
        ;; restore ebx
        pop         ebx
skip_ebx_restore:

        test        eax, 40h
        je          skip_jump_transition_record
        ;; jump over transition record
        add         esp, (SIZE Struct_System_GCs_CallStack_TransitionRecord)
skip_jump_transition_record:

        ;; restore ebp if it was used as the frame pointer
        test        eax, 2h
        jne         skip_frame_pointer_restore
        ;; restore frame pointer (esp == ebp already)
        pop         ebp
skip_frame_pointer_restore:

        ;; set edx=return address
        pop         edx

        ;; pop arguments
        shr         eax, 16
        add         esp, eax

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
; Assumes edx points to the address after the one that threw.
;

align 16
__throwDivideByZeroException proc
        push ebx
        push esi
        mov ebx,edx  ; save address
        lock inc ?c_allocationGCInhibitCount@Class_System_GC@@2HA
        mov ecx,offset ??_7System_DivideByZeroException@@6B@
        call ?g_AllocateObject@Class_System_GC@@SIPAUClass_System_Object@@PAUClass_System_VTable@@@Z
        mov esi,eax  ; save pointer to instance of exception
        mov ecx,eax  ; initialize instance
        call ?m__ctor@Class_System_DivideByZeroException@@SIXPAU1@@Z
        lock dec ?c_allocationGCInhibitCount@Class_System_GC@@2HA
        mov ecx,esi
        mov edx,ebx
        pop esi
        pop ebx
        jmp __throwDispatcherExplicitAddr
__throwDivideByZeroException endp

; 
; __throwStackOverflowException: instantiate an StackOverflow exception
; and throw it.
;
; Assumes edx points to the address of the instruction that faulted
;

align 16
__throwStackOverflowException proc
        push ebx
        push esi
        mov ebx,edx  ; save address
        lock inc ?c_allocationGCInhibitCount@Class_System_GC@@2HA
        mov ecx,offset ??_7System_StackOverflowException@@6B@
        call ?g_AllocateObject@Class_System_GC@@SIPAUClass_System_Object@@PAUClass_System_VTable@@@Z
        mov esi,eax  ; save pointer to instance of exception
        mov ecx,eax  ; initialize instance
        call ?m__ctor@Class_System_StackOverflowException@@SIXPAU1@@Z
        lock dec ?c_allocationGCInhibitCount@Class_System_GC@@2HA
        mov ecx,esi
        mov edx,ebx
        call ?ExceptionTableLookup@@YI_KPAUClass_System_Exception@@I@Z
        ResetGuardPageOnStackOverflow
        pop esi
        pop ebx
        mov ecx,eax
;        mov edx is already ok
        jmp edx
__throwStackOverflowException endp

; 
; __throwNullReferenceException: instantiate an NullReference exception
; and throw it.
;
; Assumes edx points to the address of the instruction that faulted
;

align 16
__throwNullReferenceException proc
        push ebx
        push esi
        mov ebx,edx  ; save address
        lock inc ?c_allocationGCInhibitCount@Class_System_GC@@2HA
        mov ecx,offset ??_7System_NullReferenceException@@6B@
        call ?g_AllocateObject@Class_System_GC@@SIPAUClass_System_Object@@PAUClass_System_VTable@@@Z
        mov esi,eax  ; save pointer to instance of exception
        mov ecx,eax  ; initialize instance
        call ?m__ctor@Class_System_NullReferenceException@@SIXPAU1@@Z
        lock dec ?c_allocationGCInhibitCount@Class_System_GC@@2HA
        mov ecx,esi
        mov edx,ebx
        pop esi
        pop ebx
        jmp __throwDispatcherExplicitAddr
__throwNullReferenceException endp

; 
; __throwDivideByZeroException: instantiate an divide-by-zero exception
; and throw it.
;
; Assumes edx points to the address of the instruction that faulted
;

align 16
__throwOverflowException proc
        push ebx
        push esi
        mov ebx,edx  ; save address
        lock inc ?c_allocationGCInhibitCount@Class_System_GC@@2HA
        mov ecx,offset ??_7System_OverflowException@@6B@
        call ?g_AllocateObject@Class_System_GC@@SIPAUClass_System_Object@@PAUClass_System_VTable@@@Z
        mov esi,eax  ; save pointer to instance of exception
        mov ecx,eax  ; initialize instance
        call ?m__ctor@Class_System_OverflowException@@SIXPAU1@@Z
        lock dec ?c_allocationGCInhibitCount@Class_System_GC@@2HA
        mov ecx,esi
        mov edx,ebx
        pop esi
        pop ebx
        jmp __throwDispatcherExplicitAddr
__throwOverflowException endp

;
;  int System.VTable.doubleToInt(double)
;

align 16
?g_doubleToInt@Class_System_VTable@@SIHN@Z proc
        push        ebp
        mov         ebp,esp
        add         esp,-8
        fld         real8 ptr [ebp+8]
        wait
        fnstcw      word ptr [ebp-2]
        wait
        mov         ax,word ptr [ebp-2]
        or          eax,0C00h
        mov         word ptr [ebp-4],ax
        fldcw       word ptr [ebp-4]
        fistp       dword ptr [ebp-8]
        fldcw       word ptr [ebp-2]
        mov         eax,dword ptr [ebp-8]

        cmp         eax,080000000h
        je          possible_overflow
return:
        mov         esp,ebp
        pop         ebp
        ret         8

possible_overflow:
        fld         real8 ptr [ebp+8]
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

?g_doubleToInt@Class_System_VTable@@SIHN@Z endp

;
;  long System.VTable.doubleToLong(double)
;

;*********************************************************************/
; copied from act\doc\resources\clr\src\jithelp.asm

;Purpose:
;   converts a double to a long truncating toward zero (C semantics)
;
;       uses stdcall calling conventions 
;
;   note that changing the rounding mode is very expensive.  This
;   routine basiclly does the truncation sematics without changing
;   the rounding mode, resulting in a win.
;
align 16
?g_doubleToLong@Class_System_VTable@@SI_JN@Z proc
        fld qword ptr[ESP+4]            ; fetch arg
        lea ecx,[esp-8]
        sub esp,16                      ; allocate frame
        and ecx,-8                      ; align pointer on boundary of 8
        fld st(0)                       ; duplciate top of stack
        fistp qword ptr[ecx]            ; leave arg on stack, also save in temp
        fild qword ptr[ecx]             ; arg, round(arg) now on stack
        mov edx,[ecx+4]                 ; high dword of integer
        mov eax,[ecx]                   ; low dword of integer
        test eax,eax
        je integer_QNaN_or_zero

arg_is_not_integer_QNaN:
        fsubp st(1),st                  ; TOS=d-round(d),
                                        ; { st(1)=st(1)-st & pop ST }
        test edx,edx                    ; what's sign of integer
        jns positive
                                        ; number is negative
                                        ; dead cycle
                                        ; dead cycle
        fstp dword ptr[ecx]             ; result of subtraction
        mov ecx,[ecx]                   ; dword of difference(single precision)
        add esp,16
        xor ecx,80000000h
        add ecx,7fffffffh               ; if difference>0 then increment integer
        adc eax,0                       ; inc eax (add CARRY flag)
        adc edx,0                       ; propagate carry flag to upper bits
        ret 8

positive:
        fstp dword ptr[ecx]             ;17-18 ; result of subtraction
        mov ecx,[ecx]                   ; dword of difference (single precision)
        add esp,16
        add ecx,7fffffffh               ; if difference<0 then decrement integer
        sbb eax,0                       ; dec eax (subtract CARRY flag)
        sbb edx,0                       ; propagate carry flag to upper bits
        ret 8

integer_QNaN_or_zero:
        test edx,7fffffffh
        jnz arg_is_not_integer_QNaN
        fstp st(0)                      ;; pop round(arg)
        fstp st(0)                      ;; arg
        add esp,16
        ret 8

?g_doubleToLong@Class_System_VTable@@SI_JN@Z endp

;
;  int System.VTable.floatToInt(float)
;

align 16
?g_floatToInt@Class_System_VTable@@SIHM@Z proc
        push        ebp
        mov         ebp,esp
        add         esp,-8
        fld         real4 ptr [ebp+8]
        wait
        fnstcw      word ptr [ebp-2]
        wait
        xor         eax,eax
        mov         ax,word ptr [ebp-2]
        or          eax,0C00h
        mov         word ptr [ebp-4],ax
        fldcw       word ptr [ebp-4]
        fistp       dword ptr [ebp-8]
        fldcw       word ptr [ebp-2]
        mov         eax,dword ptr [ebp-8]

        cmp         eax,080000000h
        je          possible_overflow
return:
        mov         esp,ebp
        pop         ebp
        ret         4

possible_overflow:
        fld         real4 ptr [ebp+8]
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

?g_floatToInt@Class_System_VTable@@SIHM@Z endp

;
;  long System.VTable.floatToLong(float)
;

align 16
?g_floatToLong@Class_System_VTable@@SI_JM@Z proc
        push        ebp
        mov         ebp,esp
        add         esp,-12
        fld         real4 ptr [ebp+8]
        wait
        fnstcw      word ptr [ebp-2]
        wait
        mov         ax,word ptr [ebp-2]
        or          eax,0C00h
        mov         word ptr [ebp-4],ax
        fldcw       word ptr [ebp-4]
        fistp       qword ptr [ebp-12]
        fldcw       word ptr [ebp-2]
        mov         eax,dword ptr [ebp-12]
        mov         edx,dword ptr [ebp-8]

        cmp         edx,080000000h
        je          possible_overflow
return:
        mov         esp,ebp
        pop         ebp
        ret         4

possible_overflow:
        mov         edx,eax                    ; save lsw
        fld         real4 ptr [ebp+8]
        fild        qword ptr $MAXLONG
        fcompp
        fnstsw      ax
        test        ah,4                                        
        jne         short return_zero
        test        ah,65
        je          short check_MINLONG

return_MAXLONG:
        mov         eax, 0ffffffffh
        mov         edx, 07fffffffh
        jmp         short return

return_zero:
        xor         eax, eax
        xor         edx, edx
        jmp         short return

check_MINLONG:
        fld         real4 ptr [ebp+8]
        fild        qword ptr $MINLONG
        fcompp
        fnstsw      ax
        test        ah,1
        jne         short return_original

return_MINLONG:
        xor         edx, edx                   ; zero lsw

return_original:
        mov         eax, edx                   ; restore lsw to eax
        mov         edx, 080000000h
        jmp         short return

?g_floatToLong@Class_System_VTable@@SI_JM@Z endp

;
;  int System.VTable.checkedDoubleToInt(double)
;

align 16
?g_checkedDoubleToInt@Class_System_VTable@@SIHN@Z proc
        push        ebp
        mov         ebp,esp
        add         esp,-8
        fld         real8 ptr [ebp+8]
        wait
        fnstcw      word ptr [ebp-2]
        wait
        mov         ax,word ptr [ebp-2]
        or          eax,0C00h
        mov         word ptr [ebp-4],ax
        fldcw       word ptr [ebp-4]
        fistp       dword ptr [ebp-8]
        fldcw       word ptr [ebp-2]
        mov         eax,dword ptr [ebp-8]

        cmp         eax,080000000h
        je          possible_overflow
return:
        mov         esp,ebp
        pop         ebp
        ret         8

possible_overflow:
        fld         real8 ptr [ebp+8]
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
        fld         real8 ptr [ebp+8]
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
        mov         esp,ebp
        pop         ebp
        pop         eax       ; grab return address
        add         esp, 4    ; move esp pass the first parameter.
        mov         [esp],eax ; overwrite argument
        jmp         ?g_throwNewOverflowException@Class_System_VTable@@SIXXZ    

?g_checkedDoubleToInt@Class_System_VTable@@SIHN@Z endp

;
;  long System.VTable.checkedDoubleToLong(double)
;

align 16
?g_checkedDoubleToLong@Class_System_VTable@@SI_JN@Z proc
        push        ebp
        mov         ebp,esp
        add         esp,-12
        fld         real8 ptr [ebp+8]
        wait
        fnstcw      word ptr [ebp-2]
        wait
        mov         ax,word ptr [ebp-2]
        or          eax,0C00h
        mov         word ptr [ebp-4],ax
        fldcw       word ptr [ebp-4]
        fistp       qword ptr [ebp-12]
        fldcw       word ptr [ebp-2]
        mov         eax,dword ptr [ebp-12]
        mov         edx,dword ptr [ebp-8]

        cmp         edx,080000000h
        je          possible_overflow
return:
        mov         esp,ebp
        pop         ebp
        ret         8

possible_overflow:
        mov         edx,eax                    ; save lsw
        fld         real8 ptr [ebp+8]
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
        fld         real8 ptr [ebp+8]
        fcompp                       ; real8 ptr [ebp+8] < $MINLONG
        fnstsw      ax
        test        ah,1
        jne         short throw_exception
        
return_MINLONG:
        mov         eax, edx                   ; restore lsw to eax
        mov         edx, 080000000h
        jmp         short return
        

throw_exception:
        ; throw an overflow exception
        ; set up stack frame so that it looks like a call to throwNewOverflowException
        ; from the caller of this function.
        mov         esp,ebp
        pop         ebp
        pop         eax       ; grab return address
        add         esp, 4    ; move esp pass the first parameter.
        mov         [esp],eax ; overwrite argument
        jmp         ?g_throwNewOverflowException@Class_System_VTable@@SIXXZ
       
?g_checkedDoubleToLong@Class_System_VTable@@SI_JN@Z endp

;
;  int System.VTable.checkedFloatToInt(float)
;

align 16
?g_checkedFloatToInt@Class_System_VTable@@SIHM@Z proc
        push        ebp
        mov         ebp,esp
        add         esp,-8
        fld         real4 ptr [ebp+8]
        wait
        fnstcw      word ptr [ebp-2]
        wait
        xor         eax,eax
        mov         ax,word ptr [ebp-2]
        or          eax,0C00h
        mov         word ptr [ebp-4],ax
        fldcw       word ptr [ebp-4]
        fistp       dword ptr [ebp-8]
        fldcw       word ptr [ebp-2]
        mov         eax,dword ptr [ebp-8]

        cmp         eax,080000000h
        je          possible_overflow

return:
        mov         esp,ebp
        pop         ebp
        ret         4

possible_overflow:
        fld         real4 ptr [ebp+8]
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
        fld         real4 ptr [ebp+8]
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
        mov         esp,ebp
        pop         ebp
        pop         eax       ; grab return address
        mov         [esp],eax ; overwrite argument
        jmp         ?g_throwNewOverflowException@Class_System_VTable@@SIXXZ

?g_checkedFloatToInt@Class_System_VTable@@SIHM@Z endp

;
;  long System.VTable.checkedFloatToLong(float)
;

align 16
?g_checkedFloatToLong@Class_System_VTable@@SI_JM@Z proc
        push        ebp
        mov         ebp,esp
        add         esp,-12
        fld         real4 ptr [ebp+8]
        wait
        fnstcw      word ptr [ebp-2]
        wait
        mov         ax,word ptr [ebp-2]
        or          eax,0C00h
        mov         word ptr [ebp-4],ax
        fldcw       word ptr [ebp-4]
        fistp       qword ptr [ebp-12]
        fldcw       word ptr [ebp-2]
        mov         eax,dword ptr [ebp-12]
        mov         edx,dword ptr [ebp-8]

        cmp         edx,080000000h
        je          possible_overflow
return:
        mov         esp,ebp
        pop         ebp
        ret         4

possible_overflow:
        mov         edx,eax                    ; save lsw
        fld         real4 ptr [ebp+8]
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
        fld         real4 ptr [ebp+8]
        fcompp                                  ; real8 ptr [ebp+8] < $MINLONG
        fnstsw      ax
        test        ah,1                        
        jne         short throw_exception ;  throw an overflow exception when src < $MINLONG  
return_MINLONG:
        mov         eax, edx        ;  restore lsw
        mov         edx, 080000000h
        jmp         short return

throw_exception:
        ; throw an overflow exception
        ; set up stack frame so that it looks like a call to throwNewOverflowException
        ; from the caller of this function.
        mov         esp,ebp
        pop         ebp
        pop         eax       ; grab return address
        mov         [esp],eax ; overwrite argument
        jmp         ?g_throwNewOverflowException@Class_System_VTable@@SIXXZ

?g_checkedFloatToLong@Class_System_VTable@@SI_JM@Z endp

;
;  double System.Math.Sin(double)
;

align 16
?g_Sin@Class_System_Math@@SINN@Z proc
        fld         real8 ptr [esp+4]
        fsin
        ret         8
?g_Sin@Class_System_Math@@SINN@Z endp

;
;  double System.Math.Cos(double)
;

align 16
?g_Cos@Class_System_Math@@SINN@Z proc
        fld         real8 ptr [esp+4]
        fcos
        ret         8
?g_Cos@Class_System_Math@@SINN@Z endp

;
;  double System.Math.Tan(double)
;

align 16
?g_Tan@Class_System_Math@@SINN@Z proc
        fld         real8 ptr [esp+4]
        fptan
        fstp        real8 ptr [esp+4]
        ret         8
?g_Tan@Class_System_Math@@SINN@Z endp

;
;
;  double System.Math.Atan(double)
;

align 16
?g_Atan@Class_System_Math@@SINN@Z proc
        fld         real8 ptr [esp+4]
        fld1
        fpatan
        ret         8
?g_Atan@Class_System_Math@@SINN@Z endp

;
;  double System.Math.atan2(double,double)
;

align 16
?g_atan2@Class_System_Math@@SINNN@Z proc
        fld         real8 ptr [esp+4]
        fld         real8 ptr [esp+12]
        fpatan
        ret         16
?g_atan2@Class_System_Math@@SINNN@Z endp

;
;  double System.Math.exp(double)
;

align 16
?g_exp@Class_System_Math@@SINN@Z proc
        push        ebp
        mov         ebp,esp

        fldl2e
        fmul        real8 ptr [ebp+8]
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

        mov         esp,ebp
        pop         ebp
        ret         8
?g_exp@Class_System_Math@@SINN@Z endp

;
;  double System.Math.log(double)
;

align 16
?g_Log@Class_System_Math@@SINN@Z proc
        fldln2
        fld         real8 ptr [esp+4]
        fyl2x
        ret         8
?g_Log@Class_System_Math@@SINN@Z endp

;
;  double System.Math.Ceiling(double)
;

align 16
?g_Ceiling@Class_System_Math@@SINN@Z proc
        push        ebp
        mov         ebp,esp
        add         esp,-4

        fld         real8 ptr [ebp+8]
        wait
        fnstcw      word ptr [ebp-2]
        wait
        mov         ax,word ptr [ebp-2]
        and         ah,0F3h
        or          ah,008h
        mov         word ptr [ebp-4],ax
        fldcw       word ptr [ebp-4]
        frndint
        fldcw       word ptr [ebp-2]

        mov         esp,ebp
        pop         ebp
        ret         8
?g_Ceiling@Class_System_Math@@SINN@Z endp

;
;  double System.Math.Floor(double)
;

align 16
?g_Floor@Class_System_Math@@SINN@Z proc
        push        ebp
        mov         ebp,esp
        add         esp,-4

        fld         real8 ptr [ebp+8]
        wait
        fnstcw      word ptr [ebp-2]
        wait
        mov         ax,word ptr [ebp-2]
        and         ah,0F3h
        or          ah,004h
        mov         word ptr [ebp-4],ax
        fldcw       word ptr [ebp-4]
        frndint
        fldcw       word ptr [ebp-2]

        mov         esp,ebp
        pop         ebp
        ret         8
?g_Floor@Class_System_Math@@SINN@Z endp

;
;  double System.Math.Round(double)
;

align 16
?g_Round@Class_System_Math@@SINN@Z proc
        fld QWORD PTR [ESP+4]
        frndint
        ret 8
?g_Round@Class_System_Math@@SINN@Z endp

;
;  float System.Math.Abs(float)
;

align 16
?g_abs@Class_System_Math@@SIMM@Z proc
        fld         real4 ptr [esp+4]
        fabs
        ret         4
?g_abs@Class_System_Math@@SIMM@Z endp

;
;  double System.Math.Abs(double)
;

align 16
?g_abs@Class_System_Math@@SINN@Z proc
        fld         real8 ptr [esp+4]
        fabs
        ret         8
?g_abs@Class_System_Math@@SINN@Z endp

align 16
?g_floatRem@Class_System_VTable@@SIMMM@Z proc                                
        fld     real4 ptr [esp+8]
        fld     real4 ptr [esp+4]
fremloop:        
        fprem
        fstsw   ax        
        fwait
        sahf
        jp      fremloop    ; Continue while the FPU status bit C2 is set
        ffree st(1)
        ret     8
?g_floatRem@Class_System_VTable@@SIMMM@Z endp

align 16
?g_doubleRem@Class_System_VTable@@SINNN@Z proc
        fld     real8 ptr [esp+12]
        fld     real8 ptr [esp+4]
fremloop:
        fprem
        fstsw   ax        
        fwait
        sahf
        jp      fremloop    ; Continue while the FPU status bit C2 is set
        ffree st(1)
        ret     16
?g_doubleRem@Class_System_VTable@@SINNN@Z endp


if EXCLUDED        
;
;  void __checkFPStackDepth0
;

align 16
__checkFPStackDepth0 proc
        push        ebp
        mov         ebp,esp

        push        eax
        pushfd
 
        xor         eax,eax

        wait
        fnstsw      ax
        wait

        shr         eax,11
        and         eax,7
        cmp         eax,0
        je          ok
oops:
        int         3
ok:

        popfd
        pop         eax

        pop         ebp
        ret         0
__checkFPStackDepth0 endp

;
;  void __checkFPStackDepth1
;

align 16
__checkFPStackDepth1 proc
        push        ebp
        mov         ebp,esp

        push        eax
        pushfd
 
        xor         eax,eax

        wait
        fnstsw      ax
        wait

        shr         eax,11
        and         eax,7
        cmp         eax,8-1
        je          ok
oops:
        int         3
ok:

        popfd
        pop         eax

        pop         ebp
        ret         0
__checkFPStackDepth1 endp

;
;  void __checkFPStackDepth2
;

align 16
__checkFPStackDepth2 proc
        push        ebp
        mov         ebp,esp

        push        eax
        pushfd
 
        xor         eax,eax

        wait
        fnstsw      ax
        wait

        shr         eax,11
        and         eax,7
        cmp         eax,8-2
        je          ok
oops:
        int         3
ok:

        popfd
        pop         eax

        pop         ebp
        ret         0
__checkFPStackDepth2 endp

;
;  void __checkFPStackDepth3
;

align 16
__checkFPStackDepth3 proc
        push        ebp
        mov         ebp,esp

        push        eax
        pushfd
 
        xor         eax,eax

        wait
        fnstsw      ax
        wait

        shr         eax,11
        and         eax,7
        cmp         eax,8-3
        je          ok
oops:
        int         3
ok:

        popfd
        pop         eax

        pop         ebp
        ret         0
__checkFPStackDepth3 endp

;
;  void __checkFPStackDepth4
;

align 16
__checkFPStackDepth4 proc
        push        ebp
        mov         ebp,esp

        push        eax
        pushfd
 
        xor         eax,eax

        wait
        fnstsw      ax
        wait

        shr         eax,11
        and         eax,7
        cmp         eax,8-4
        je          ok
oops:
        int         3
ok:

        popfd
        pop         eax

        pop         ebp
        ret         0
__checkFPStackDepth4 endp

;
;  void __checkFPStackDepth5
;

align 16
__checkFPStackDepth5 proc
        push        ebp
        mov         ebp,esp

        push        eax
        pushfd
 
        xor         eax,eax

        wait
        fnstsw      ax
        wait

        shr         eax,11
        and         eax,7
        cmp         eax,8-5
        je          ok
oops:
        int         3
ok:

        popfd
        pop         eax

        pop         ebp
        ret         0
__checkFPStackDepth5 endp

;
;  void __checkFPStackDepth6
;

align 16
__checkFPStackDepth6 proc
        push        ebp
        mov         ebp,esp

        push        eax
        pushfd
 
        xor         eax,eax

        wait
        fnstsw      ax
        wait

        shr         eax,11
        and         eax,7
        cmp         eax,8-6
        je          ok
oops:
        int         3
ok:

        popfd
        pop         eax

        pop         ebp
        ret         0
__checkFPStackDepth6 endp

;
;  void __checkFPStackDepth7
;

align 16
__checkFPStackDepth7 proc
        push        ebp
        mov         ebp,esp

        push        eax
        pushfd
 
        xor         eax,eax

        wait
        fnstsw      ax
        wait

        shr         eax,11
        and         eax,7
        cmp         eax,8-7
        je          ok
oops:
        int         3
ok:

        popfd
        pop         eax

        pop         ebp
        ret         0
__checkFPStackDepth7 endp
endif ; EXCLUDED

end
