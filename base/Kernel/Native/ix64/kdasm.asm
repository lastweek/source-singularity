;; ----------------------------------------------------------------------------
;;
;;  Copyright (c) Microsoft Corporation.  All rights reserved.
;;
;; ----------------------------------------------------------------------------

include hal.inc

;public: static void __cdecl Class_Microsoft_Singularity_DebugStub::g_Break(void)"
?g_Break@Class_Microsoft_Singularity_DebugStub@@SAXXZ proc
    int     3
    ret;
?g_Break@Class_Microsoft_Singularity_DebugStub@@SAXXZ endp

;void __cdecl KdpPause(void)"
?KdpPause@@YAXXZ proc
    pause
    ret;
?KdpPause@@YAXXZ endp

; NB: Without these, we share routines with the mainline code and we get
; caught in a loop when the debugger inserts a break after the pushfd when
; someone tries to single step through Processor:g_DisableInterrupts!
;
;bool __cdecl KdpDisableInterruptsInline(void)"
?KdpDisableInterruptsInline@@YA_NXZ proc
    pushfq
    pop rax
    test rax, Struct_Microsoft_Singularity_Isal_IX_EFlags_IF
    setnz al
    nop;    // required so that the linker doesn't combine with g_Disable
    cli;
    ret;
?KdpDisableInterruptsInline@@YA_NXZ endp

;void __cdecl KdpRestoreInterruptsInline(bool)"
?KdpRestoreInterruptsInline@@YAX_N@Z proc
    nop;
    test cl, cl;
    je done;
    nop;    // required so that the linker doesn't combine with g_Restore
    sti;
  done:
    ret;
?KdpRestoreInterruptsInline@@YAX_N@Z endp

;void __cdecl KdpFlushInstCache(void)"
?KdpFlushInstCache@@YAXXZ proc
    wbinvd;   // privileged instruction
    ret;
?KdpFlushInstCache@@YAXXZ endp

; "unsigned __int64 __cdecl KdpX64ReadMsr(unsigned long)"
?KdpX64ReadMsr@@YA_KK@Z proc
    rdmsr;
    ret;
?KdpX64ReadMsr@@YA_KK@Z endp

; "void __cdecl KdpX64WriteMsr(unsigned long,unsigned __int64)"
?KdpX64WriteMsr@@YAXK_K@Z proc
    mov eax, edx;
    shr rdx, 32;
    wrmsr;
    ret;
?KdpX64WriteMsr@@YAXK_K@Z endp
;?KdpX64ReadMsr@@YA_KK@Z endp

; "void __cdecl KdpX64GetSegmentRegisters(struct Struct_Microsoft_Singularity_Kd_X64Context *)"
?KdpX64GetSegmentRegisters@@YAXPEAUStruct_Microsoft_Singularity_Kd_X64Context@@@Z proc
    mov ax,cs
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64Context._SegCs, ax
    mov ax,gs
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64Context._SegGs, ax
    mov ax,fs
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64Context._SegFs, ax
    mov ax,es
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64Context._SegEs, ax
    mov ax,ds
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64Context._SegDs, ax
    mov ax,ss
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64Context._SegSs, ax
    ret;    
?KdpX64GetSegmentRegisters@@YAXPEAUStruct_Microsoft_Singularity_Kd_X64Context@@@Z endp

; "void __cdecl KdpX64SetControlReport(struct Struct_Microsoft_Singularity_Kd_X64KdControlReport *)"
?KdpX64SetControlReport@@YAXPEAUStruct_Microsoft_Singularity_Kd_X64KdControlReport@@@Z proc
    mov rax, dr6;
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KdControlReport._Dr6, rax;
    mov rax, dr7;
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KdControlReport._Dr7, rax;
    mov ax, cs
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KdControlReport._SegCs, ax
    mov ax, es
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KdControlReport._SegEs, ax
    mov ax, ds
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KdControlReport._SegDs, ax
    mov ax, fs
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KdControlReport._SegFs, ax
    pushfq
    pop rax
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KdControlReport._EFlags, eax
    ret;
?KdpX64SetControlReport@@YAXPEAUStruct_Microsoft_Singularity_Kd_X64KdControlReport@@@Z endp

; "void __cdecl KdpX64SetControlSet(struct Struct_Microsoft_Singularity_Kd_X64KdControlSet *)"
?KdpX64SetControlSet@@YAXPEBUStruct_Microsoft_Singularity_Kd_X64KdControlSet@@@Z proc
    mov rax, [rcx].Struct_Microsoft_Singularity_Kd_X64KdControlSet._Dr7;
    mov dr7, rax;
    ret;
?KdpX64SetControlSet@@YAXPEBUStruct_Microsoft_Singularity_Kd_X64KdControlSet@@@Z endp

; "void __cdecl KdpX64WriteSpecialRegisters(struct Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters const *)"
?KdpX64ReadSpecialRegisters@@YAXPEAUStruct_Microsoft_Singularity_Kd_X64KSpecialRegisters@@@Z proc
    mov rax, dr0;
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr0, rax;
    mov rax, dr1;
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr1, rax;
    mov rax, dr2;
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr2, rax;
    mov rax, dr3;
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr3, rax;
    mov rax, dr6;
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr6, rax;
    mov rax, dr7;
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr7, rax;

    sidt [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._Idtr._Limit;
    sgdt [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._Gdtr._Limit;
        
    ;; Should we save the segment regs as well?
    str ax;
    mov [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._Tr, ax;
    ret;
?KdpX64ReadSpecialRegisters@@YAXPEAUStruct_Microsoft_Singularity_Kd_X64KSpecialRegisters@@@Z endp
        
; "void __cdecl KdpX64WriteSpecialRegisters(struct Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters const *)"
?KdpX64WriteSpecialRegisters@@YAXPEBUStruct_Microsoft_Singularity_Kd_X64KSpecialRegisters@@@Z proc
    mov rax, [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr0;
    mov dr0, rax;
    mov rax, [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr1;
    mov dr1, rax;
    mov rax, [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr2;
    mov dr2, rax;
    mov rax, [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr3;
    mov dr3, rax;
    mov rax, [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr6;
    mov dr6, rax;
    mov rax, [rcx].Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters._KernelDr7;
    mov dr7, rax;
    ret;
?KdpX64WriteSpecialRegisters@@YAXPEBUStruct_Microsoft_Singularity_Kd_X64KSpecialRegisters@@@Z endp


        
;static void KdWriteInt8(UINT16 port, UINT8 value)
?KdWriteInt8@@YAXGE@Z proc 
    mov     al,dl
    mov     dx,cx
    out     dx, al
    ret;
?KdWriteInt8@@YAXGE@Z ENDP

;static UINT8 KdReadInt8(UINT16 port)
?KdReadInt8@@YAEG@Z proc
    mov     eax, 0
    mov     dx, cx
    in      al, dx
    ret;
?KdReadInt8@@YAEG@Z endp

end
