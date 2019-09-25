;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;     bllrb0.asm
;
; Abstract:
;
;     This module implements utility functions for the boot reloader.
;
; Environment:
;
;     Boot reloader.
;
;--

.code

externdef main:NEAR
        
;++
;
; VOID
; BlLrbEnter(
;     uint pConfig, ulong pVars
;     )
;
; Routine Description:
;
;   This function adjusts the stack, then enters the C code.
;
;--

BlLrbEnter proc
        mov     edx, [rsp+8]
        mov     ecx, [rsp]
        mov     rsp, 07b00h
        jmp     main

BlLrbEnter endp


;++
;
; ULONG_PTR
; BlMmGetCr3(
;     VOID
;     )
;
; Routine Description:
;
;   This function queries the CR3 register.
;
; Return Value:
;
;   Value of the CR3 register.
;
;--

BlMmGetCr3 proc

        mov     rax, cr3
        ret

BlMmGetCr3 endp

;++
;
; VOID
; BlMmSetCr3(
;     ULONG_PTR Value
;     )
;
; Routine Description:
;
;   This function sets the CR3 register.
;
; Arguments:
;
;   Value       - Supplies the value to write to the CR3 register.
;
;--

BlMmSetCr3 proc

        mov     cr3, rcx
        ret

BlMmSetCr3 endp

;++
;
; VOID
; BlMmGetGdtr(
;     PGDTR Gdtr
;     )
;
; Routine Description:
;
;   This function queries the GDTR register.
;
; Arguments:
;
;   Gdtr        - Receives the contents of the GDTR register.
;
;--

BlMmGetGdtr proc

        sgdt    fword ptr [rcx]
        ret

BlMmGetGdtr endp


;++
;
; VOID
; BlMmSetGdtr(
;     PGDTR Gdtr
;     )
;
; Routine Description:
;
;   This function sets the GDTR register.
;
; Arguments:
;
;   Gdtr        - Supplies the data to write to the GDTR register.
;
;--

BlMmSetGdtr proc

        lgdt    fword ptr [rcx]
        ret

BlMmSetGdtr endp

;++
;
; ULONG_PTR
; BlMmGetRsp(
;     VOID
;     )
;
; Routine Description:
;
;   This function queries the RSP register.
;
; Return Value:
;
;   Value of the RSP register.
;
;--

BlMmGetRsp proc

        mov     rax, rsp
        ret

BlMmGetRsp endp

end
