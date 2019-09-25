; 
; Copyright (c) Microsoft Corporation.   All rights reserved.
;

    AREA |.text|, CODE, READONLY

    INCLUDE core.inc
    
    IMPORT |?ExceptionTableLookup@@YI_KPAUClass_System_Exception@@I@Z|
    IMPORT InterlockedIncrement
    IMPORT InterlockedDecrement

    IMPORT |?m__ctor@Class_System_DivideByZeroException@@SAXPAU1@@Z|
    IMPORT |??_7System_DivideByZeroException@@6B@|
    IMPORT |?m__ctor@Class_System_NullReferenceException@@SAXPAU1@@Z|
    IMPORT |??_7System_NullReferenceException@@6B@|
    IMPORT |?m__ctor@Class_System_OverflowException@@SAXPAU1@@Z|
    IMPORT |??_7System_OverflowException@@6B@|
    IMPORT |?m__ctor@Class_System_StackOverflowException@@SAXPAU1@@Z|
    IMPORT |??_7System_StackOverflowException@@6B@|

    ;;;;
    ;; Placeholder stubs to satisfy the linker
    ;;;;

    EXPORT __throwDispatcherUnwind

__throwDispatcherUnwind

    mov r0, #0xde
    mov r0, r0 LSL #8
    orr r0, r0, #0xad
    mov r0, r0 LSL #16
    mov pc, lr

;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;   ACTUAL   ;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;

    IMPORT |__stoi64|
    EXPORT |?g_floatToLong@Class_System_VTable@@SA_JM@Z|
|?g_floatToLong@Class_System_VTable@@SA_JM@Z|
    b __stoi64

    IMPORT |__stoi|
    EXPORT |?g_floatToInt@Class_System_VTable@@SAHM@Z|
|?g_floatToInt@Class_System_VTable@@SAHM@Z|
    b __stoi

    IMPORT |__dtoi64|
    EXPORT |?g_doubleToLong@Class_System_VTable@@SA_JN@Z|
|?g_doubleToLong@Class_System_VTable@@SA_JN@Z|
    b __dtoi64

    IMPORT |__dtoi|
    EXPORT |?g_doubleToInt@Class_System_VTable@@SAHN@Z|
|?g_doubleToInt@Class_System_VTable@@SAHN@Z|
    b __dtoi


;
;  __throwDispatcher(r0=exception)
; 
; Description: this function is called to explicitly throw an exception.
; It assumes that the return address points to the instruction immediately
; after the one where the exception was thrown
;
; Arguments:
;    R0 = exception object
;    LR = the return address
; Effects:
;    1. Create FP chain entry
;    2. Get return address and uses it to calculate the address of the 
;       instruction that threw the exception.
;    3. Looks up the appropriate handler and jumps to code to process it.

    EXPORT __throwDispatcher
    NESTED_ENTRY __throwDispatcher

        ; Save data we'll need later
        stmdb   sp!, {r4}
    PROLOG_END
        mov     r4, r0      ; Exception

        ; Lookup the handler
        mov     r1, lr      ; Return address
        sub     r1, r1, #4  ; Address of throw

        bl      |?ExceptionTableLookup@@YI_KPAUClass_System_Exception@@I@Z|

                            ; r0 - frame setup / exception type
                            ; r1 - spill size / frame setup offset / handler
        mov     r2, r4      ; r2 - exception

        ; Restore saved registers and branch to handler
        ldmia   sp!, {r4}
        b       __throwDispatcherHandler

    ENTRY_END

;  __throwDispatcherHandler (r0=frameSetupInfo or exceptionType,
;                            r1=spillSize,frameSetupSize, or handlerAddress,
;                            r2=exception
;
; Description:
;    After the exception table entry has been found, the values are passed here
;    for processing.  This method simply checks for the easy case of an explicit
;    handler (known if the exceptionType is given <-- low bit is zero).
;    In this case it simply jumps to the handler.  Otherwise it passes the
;    information along to __throwDispatcherUnwind.
;
; Arguments:
;    If low bit of r0 is set:
;        r0 = frame setup information 
;        r1 = spill size excluding callee-save register saves
;              or offset from ebp to end of callee-save register saves
;        r2 = exception object
;    Otherwise:
;        r0 = exception type (unused)
;        r1 = handler address
;        r2 = exception object

    LEAF_ENTRY __throwDispatcherHandler
        
        tst     r0, #1
        bne     __throwDispatcherUnwind

        ; r0 = exception type, r1 = handler, r2 = exception
        mov     pc, r1
    
    ENTRY_END

;
;  __throwDispatcherExplicitAddr (r0=exception, r1=throwAddress)
;
; Description:
; This is to be used when the address where the exception occurred
; is passed in as an extra argument
;
; Arguments:
;    r0 = exception object
;    r1 = address where the exception was thrown
;


    NESTED_ENTRY __throwDispatcherExplicitAddr

        stmdb       sp!, {r0}   ; save exception

    PROLOG_END

        bl          |?ExceptionTableLookup@@YI_KPAUClass_System_Exception@@I@Z|

                                ; r0 - frame setup / exception type
                                ; r1 - spill size / frame setup offset / handler
        ldmia       sp!, {r2}   ; r2 - exception

        b           __throwDispatcherHandler

    ENTRY_END

;
;  __throwDispatcherExplictAddrAfterCore (r0=exception, r1=throwAddress)
;
; Description:
;    This is to be used when the address of the instruction immediately after
;    the one that actually threw the exception is passed as an argument.
;
; Arguments:
;    r1 = address of the instruction following the one where
;         the exception was thrown
;    r2 = pointer to exception object being thrown
;
; This is used, for example, in stack unwinding, where R1 is the
; return address on the stack for the current procedure. 
;
; Stack unwinding occurs when the current procedure does not have a handler
; for the routine.   The idea is to pop the stack frame and treat the call
; instruction in the caller as though it threw.    We only have the return
; address, though, which points to the instruction *after* the call.   
;

    EXPORT __throwDispatcherExplicitAddrAfterCore
    NESTED_ENTRY __throwDispatcherExplicitAddrAfterCore

        stmdb       sp!, {r2}   ; save exception
    PROLOG_END

        mov         r0, r2      ; set exception
        sub         r1, r1, #4  ; set return address 

        bl          |?ExceptionTableLookup@@YI_KPAUClass_System_Exception@@I@Z|

                                ; r0 - frame setup / exception type
                                ; r1 - spill size / frame setup offset / handler
        ldmia       sp!, {r2}   ; r2 - exception

        b           __throwDispatcherHandler

    ENTRY_END
; 
; __throwNullReferenceException: instantiate an null reference exception
; and throw it.
;
; Assumes r1 points to the address of the instruction that faulted
;

nullRefSymbols
        dcd     |??_7System_NullReferenceException@@6B@|
nullRefConstructor
        dcd     |?m__ctor@Class_System_NullReferenceException@@SAXPAU1@@Z|

    EXPORT __throwNullReferenceException
    LEAF_ENTRY __throwNullReferenceException

        ldr     r2, nullRefSymbols
        ldr     r3, nullRefConstructor

        b       __throwExceptionHelper

    ENTRY_END

; 
; __throwStackOverflowException: instantiate an stack overflow exception
; and throw it.
;
; Assumes r1 points to the address of the instruction that faulted
;

stackVTable
        dcd     |??_7System_StackOverflowException@@6B@|
stackConstructor
        dcd     |?m__ctor@Class_System_StackOverflowException@@SAXPAU1@@Z|

    EXPORT __throwStackOverflowException
    LEAF_ENTRY __throwStackOverflowException

        ldr     r2, stackVTable
        ldr     r3, stackConstructor

        b       __throwExceptionHelper

    ENTRY_END

; 
; __throwOverflowException: instantiate an overflow exception
; and throw it.
;
; Assumes r1 points to the address of the instruction that faulted
;

overflowVTable
        dcd     |??_7System_OverflowException@@6B@|
overflowConstructor
        dcd     |?m__ctor@Class_System_OverflowException@@SAXPAU1@@Z|

    EXPORT __throwOverflowException
    LEAF_ENTRY __throwOverflowException

        ldr     r2, overflowVTable
        ldr     r3, overflowConstructor

        b       __throwExceptionHelper

    ENTRY_END

; 
; __throwDivideByZeroException: instantiate an divide-by-zero exception
; and throw it.
;
; Assumes r1 points to the address of the instruction that faulted
;

divZeroVTable
        dcd     |??_7System_DivideByZeroException@@6B@|
divZeroConstructor
        dcd     |?m__ctor@Class_System_DivideByZeroException@@SAXPAU1@@Z|

    EXPORT __throwDivideByZeroException
    LEAF_ENTRY __throwDivideByZeroException

        ldr     r2, divZeroVTable
        ldr     r3, divZeroConstructor

        b       __throwExceptionHelper

    ENTRY_END

; __throwExceptionHelper
;
; Description:
;    This method helps turn a system fault into an exception.  The various
;    different faults all do basically the same thing with the exception
;    of the type of exception they generate.
;
; Arguments:
;    r1 = address of instruction that faulted
;    r2 = address of exception type VTable
;    r3 = address of exception type constructor

allocationInhibit
        dcd     |?c_allocationGCInhibitCount@Class_System_GC@@2HA|

    NESTED_ENTRY __throwExceptionHelper

        stmdb   sp!, {r1, r4-r7}

    PROLOG_END

        mov     r6, r2
        mov     r7, r3

        ldr     r4, allocationInhibit

        mov     r0, r4
        bl      InterlockedIncrement

        mov     r0, r6
        bl      |?g_AllocateObject@Class_System_GC@@SAPAUClass_System_Object@@PAUClass_System_VTable@@@Z|
        mov     r5, r0  ; save pointer to instance of exception
        mov     lr, pc
        mov     pc, r7

        mov     r0, r4
        bl      InterlockedDecrement

        mov     r0, r5
        ldmia   sp!, {r1, r4-r7}

        b       __throwDispatcherExplicitAddr

    ENTRY_END

;  __throwDispatcherUnwind (r0=frame setup info, r1=spill size, r2=exception
;
; Description:
;    This is the global unwind handler.  It is used to unwind a single stack
;    frame if there are no explicit handlers that catch an exception in a given
;    function.
;
; Arguments:
;    r0 = frame setup information, must have low bit set
;    r1 = spill size excluding callee-save register saves
;          or offset from ebp to end of callee-save register saves
;    r2 = exception object
;
; See tables\ExceptionTable.cs for details on these values

;__throwDispatcherUnwind
    

    END

;;;;;;;;;;;;;;;;;;;;;;;
;;;;;   TEMP   ;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;


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

;;;;;;;;;;;;;;;;;;;;;;;
;;;;;   TODO   ;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;

    IF :DEF:SINGULARITY
    ELSE
        EXTERN ?ResetGuardPage@@YIXXZ:NEAR
    ENDIF ;; !SINGULARITY

    IF :DEF:SINGULARITY_KERNEL
        EXTERN ?g_setStopContext@Class_System_Threading_Thread@@SIXPAU1@PAUClass_System_Exception@@@Z:NEAR
        EXTERN __throwBeyondMarker:NEAR
    ENDIF ; SINGULARITY_KERNEL

    IF :DEF:SINGULARITY
    ELSE
        EXTERN ?g_throwNewOverflowException@Class_System_VTable@@SIXXZ:NEAR
        EXTERN ?c_CheckCount@Class_System_GCs_StackManager@@2HA:int32
        EXTERN ?g_GetStackChunk@Class_System_GCs_StackManager@@SIPAUuintPtr@@PAU2@PAUClass_System_Threading_Thread@@_N@Z:NEAR
        EXTERN ?g_ReturnStackChunk@Class_System_GCs_StackManager@@SIXPAUClass_System_Threading_Thread@@_N@Z:NEAR
;
; externals used to construct instances of machine-level exceptions
;

        EXTERN ?g_AllocateObject@Class_System_GC@@SIPAUClass_System_Object@@PAUClass_System_VTable@@@Z:NEAR
        EXTERN ?m__ctor@Class_System_ArithmeticException@@SIXPAU1@@Z:NEAR
        EXTERN ??_7System_ArithmeticException@@6B@:dword ; vtable
        EXTERN ?m__ctor@Class_System_DivideByZeroException@@SIXPAU1@@Z:NEAR
        EXTERN ??_7System_DivideByZeroException@@6B@:dword ; vtable
        EXTERN ?m__ctor@Class_System_NullReferenceException@@SIXPAU1@@Z:NEAR
        EXTERN ??_7System_NullReferenceException@@6B@:dword ;  vtable
        EXTERN ?m__ctor@Class_System_OverflowException@@SIXPAU1@@Z:NEAR
        EXTERN ??_7System_OverflowException@@6B@:dword ; vtable
        EXTERN ?m__ctor@Class_System_StackOverflowException@@SIXPAU1@@Z:NEAR
        EXTERN ??_7System_StackOverflowException@@6B@:PTR_Class_System_VTable

        EXTERN ?c_allocationInhibitGC@Class_System_GC@@2_NA:dword

        EXTERN ?g_doubleToInt@Class_System_VTable@@SIHN@Z:NEAR
        EXTERN ?g_doubleToLong@Class_System_VTable@@SI_JN@Z:NEAR
        EXTERN ?g_floatToInt@Class_System_VTable@@SIHM@Z:NEAR
        EXTERN ?g_floatToLong@Class_System_VTable@@SI_JM@Z:NEAR
        EXTERN ?g_checkedDoubleToInt@Class_System_VTable@@SIHN@Z:NEAR
        EXTERN ?g_checkedDoubleToLong@Class_System_VTable@@SI_JN@Z:NEAR
        EXTERN ?g_checkedFloatToInt@Class_System_VTable@@SIHM@Z:NEAR
        EXTERN ?g_checkedFloatToLong@Class_System_VTable@@SI_JM@Z:NEAR

        EXTERN ?g_Abs@Class_System_Math@@SIMM@Z:NEAR
        EXTERN ?g_Abs@Class_System_Math@@SINN@Z:NEAR
        EXTERN ?g_Atan@Class_System_Math@@SINN@Z:NEAR
        EXTERN ?g_Ceiling@Class_System_Math@@SINN@Z:NEAR
        EXTERN ?g_Cos@Class_System_Math@@SINN@Z:NEAR
        EXTERN ?g_Floor@Class_System_Math@@SINN@Z:NEAR
        EXTERN ?g_Log@Class_System_Math@@SINN@Z:NEAR
        EXTERN ?g_Round@Class_System_Math@@SINN@Z:NEAR
        EXTERN ?g_Sin@Class_System_Math@@SINN@Z:NEAR
        EXTERN ?g_Tan@Class_System_Math@@SINN@Z:NEAR
        EXTERN ?g_atan2@Class_System_Math@@SINNN@Z:NEAR
        EXTERN ?g_exp@Class_System_Math@@SINN@Z:NEAR
    ENDIF ;; !SINGULARITY

    IF EXCLUDED
        EXTERN __checkFPStackDepth0:NEAR
        EXTERN __checkFPStackDepth1:NEAR
        EXTERN __checkFPStackDepth2:NEAR
        EXTERN __checkFPStackDepth3:NEAR
        EXTERN __checkFPStackDepth4:NEAR
        EXTERN __checkFPStackDepth5:NEAR
        EXTERN __checkFPStackDepth6:NEAR
        EXTERN __checkFPStackDepth7:NEAR
    ENDIF ;; EXCLUDED

        align       8
$DBLMAXINT  DQ      041dfffffffc00000r          ; 2.14747e+009
$DBLMININT  DQ      0c1e0000000000000r          ; -2.14748e+009
$MAXLONG    DQ      07fffffffffffffffh
$MINLONG    DQ      08000000000000000h

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
