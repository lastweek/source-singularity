;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;     bllegacy.asm
;
; Abstract:
;
;     This module implements legacy call support.
;
; Environment:
;
;     Boot loader.
;
;--

include bl.inc

.code

;
; Interrupt return frame.
;

InterruptReturnFrame    struct

        _rip            dq ?
        _cs             dq ?
        _rflags         dq ?
        _rsp            dq ?
        _ss             dq ?

InterruptReturnFrame    ends

;
; Legacy call frame.
;

LegacyCallFrame         struct

        _rax            dq ?
        _rbx            dq ?
        _rcx            dq ?
        _rdx            dq ?
        _rbp            dq ?
        _rsi            dq ?
        _rdi            dq ?
        _r8             dq ?
        _r9             dq ?
        _r10            dq ?
        _r11            dq ?
        _r12            dq ?
        _r13            dq ?
        _r14            dq ?
        _r15            dq ?

LegacyCallFrame         ends

BlLegacyReturn_RSP      dq      0

;++
;
; VOID
; BlReturnToLegacyMode(
;     VOID
;     )
;
; Routine Description:
;
;   This function returns to legacy mode to process a legacy request.
;
;--

?BlReturnToLegacyMode@@YAXXZ proc

;
; Save all registers.
;

        sub     rsp, (sizeof LegacyCallFrame)

        mov     qword ptr [rsp].LegacyCallFrame._rax, rax
        mov     qword ptr [rsp].LegacyCallFrame._rbx, rbx
        mov     qword ptr [rsp].LegacyCallFrame._rcx, rcx
        mov     qword ptr [rsp].LegacyCallFrame._rdx, rdx
        mov     qword ptr [rsp].LegacyCallFrame._rbp, rbp
        mov     qword ptr [rsp].LegacyCallFrame._rsi, rsi
        mov     qword ptr [rsp].LegacyCallFrame._rdi, rdi
        mov     qword ptr [rsp].LegacyCallFrame._r8, r8
        mov     qword ptr [rsp].LegacyCallFrame._r9, r9
        mov     qword ptr [rsp].LegacyCallFrame._r10, r10
        mov     qword ptr [rsp].LegacyCallFrame._r11, r11
        mov     qword ptr [rsp].LegacyCallFrame._r12, r12
        mov     qword ptr [rsp].LegacyCallFrame._r13, r13
        mov     qword ptr [rsp].LegacyCallFrame._r14, r14
        mov     qword ptr [rsp].LegacyCallFrame._r15, r15

;
; Save stack pointer.
;

        mov     BlLegacyReturn_RSP, rsp


;
; Set return address in BEB.
;

        mov     rax, BEB_BASE
        lea     rcx, @f
        mov     dword ptr [rax].BEB.LegacyReturnAddress, ecx

;
; Get legacy call stub address from BEB.
;

        xor     rcx, rcx
        mov     ecx, dword ptr [rax].BEB.LegacyCallAddress

;
; Construct interrupt return frame.
;

        sub     rsp, (sizeof InterruptReturnFrame)

        mov     qword ptr [rsp].InterruptReturnFrame._rip, rcx

        mov     qword ptr [rsp].InterruptReturnFrame._cs, PM_CODE_SELECTOR

        pushfq
        pop     rax
        mov     qword ptr [rsp].InterruptReturnFrame._rflags, rax

        mov     qword ptr [rsp].InterruptReturnFrame._rsp, rsp

        mov     rax, PM_DATA_SELECTOR
        mov     qword ptr [rsp].InterruptReturnFrame._ss, rax

        mov     ds, rax
        mov     es, rax
        mov     fs, rax
        mov     gs, rax

        iretq

@@:

;
; Restore stack pointer.
;

        mov     rsp, BlLegacyReturn_RSP

;
; Restore all registers.
;

        mov     rax, qword ptr [rsp].LegacyCallFrame._rax
        mov     rbx, qword ptr [rsp].LegacyCallFrame._rbx
        mov     rcx, qword ptr [rsp].LegacyCallFrame._rcx
        mov     rdx, qword ptr [rsp].LegacyCallFrame._rdx
        mov     rbp, qword ptr [rsp].LegacyCallFrame._rbp
        mov     rsi, qword ptr [rsp].LegacyCallFrame._rsi
        mov     rdi, qword ptr [rsp].LegacyCallFrame._rdi
        mov     r8, qword ptr [rsp].LegacyCallFrame._r8
        mov     r9, qword ptr [rsp].LegacyCallFrame._r9
        mov     r10, qword ptr [rsp].LegacyCallFrame._r10
        mov     r11, qword ptr [rsp].LegacyCallFrame._r11
        mov     r12, qword ptr [rsp].LegacyCallFrame._r12
        mov     r13, qword ptr [rsp].LegacyCallFrame._r13
        mov     r14, qword ptr [rsp].LegacyCallFrame._r14
        mov     r15, qword ptr [rsp].LegacyCallFrame._r15

        add     rsp, (sizeof LegacyCallFrame)
        ret

?BlReturnToLegacyMode@@YAXXZ endp

public ?BlReturnToLegacyMode@@YAXXZ

end
