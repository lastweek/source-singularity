;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;     blutilasm.asm
;
; Abstract:
;
;     This module implements utility functions for the boot loader.
;
; Environment:
;
;     Boot loader.
;
;--

include bl.inc

.code

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

?BlMmGetCr3@@YA_KXZ proc

        mov     rax, cr3
        ret

?BlMmGetCr3@@YA_KXZ endp

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

?BlMmSetCr3@@YAX_K@Z proc

        mov     cr3, rcx
        ret

?BlMmSetCr3@@YAX_K@Z endp

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

?BlMmGetGdtr@@YAXPEAU_GDTR@@@Z proc

        sgdt    fword ptr [rcx]
        ret

?BlMmGetGdtr@@YAXPEAU_GDTR@@@Z endp


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

?BlMmSetGdtr@@YAXPEAU_GDTR@@@Z proc

        lgdt    fword ptr [rcx]
        ret

?BlMmSetGdtr@@YAXPEAU_GDTR@@@Z endp

;++
;
; USHORT
; BlMmGetGs(
;     VOID
;     )
;
; Routine Description:
;
;   This function queries the GS register.
;
; Return Value:
;
;   Value of the GS register.
;
;--

BlMmGetGs proc

        mov     ax, gs
        ret

BlMmGetGs endp

;++
;
; VOID
; BlMmSetGs(
;     USHORT Value
;     )
;
; Routine Description:
;
;   This function sets the GS register.
;
; Arguments:
;
;   Value       - Supplies the value to write to the GS register.
;
;--

?BlMmSetGs@@YAXG@Z proc

        mov     gs, cx
        ret

?BlMmSetGs@@YAXG@Z endp

;++
;
; VOID
; BlMmSwitchStack(
;     PVOID Stack,
;     PVOID Function
;     )
;
; Routine Description:
;
;   This function switches the stack and calls the specified function.
;
; Arguments:
;
;   Stack       - Supplies the stack to switch to.
;
;   Function    - Supplies the function to call.
;
;--

?BlMmSwitchStack@@YAXPEAX0@Z proc

        mov     rsp, rcx
        call    rdx

@@:
        jmp     @b

?BlMmSwitchStack@@YAXPEAX0@Z endp

;++
;
; PVOID
; BlRtlGetRbp(
;     VOID
;     )
;
; Routine Description:
;
;   This function queries the value of the RBP register.
;
; Return Value:
;
;   Value of the RBP register.
;
;--

?BlRtlGetRbp@@YAPEAXXZ proc

        mov     rax, rbp
        ret

?BlRtlGetRbp@@YAPEAXXZ endp

;++
;
; UINT
; BlGetCpuidEax(
;     UINT reg
;     )
;
; Routine Description:
;
;   This function queries the CPUID.
;
; Return Value:
;
;   Value of the EAX register.
;
;--

?BlGetCpuidEax@@YAKK@Z proc

        mov     eax, ecx
        cpuid
        ret

?BlGetCpuidEax@@YAKK@Z endp

;++
;
; UINT
; BlGetCpuidEbx(
;     UINT reg
;     )
;
; Routine Description:
;
;   This function queries the CPUID.
;
; Return Value:
;
;   Value of the EBX register.
;
;--

?BlGetCpuidEbx@@YAKK@Z proc

        mov     eax, ecx
        cpuid
        mov     ebx, eax
        ret

?BlGetCpuidEbx@@YAKK@Z endp

;++
;
; UINT
; BlGetCpuidEcx(
;     UINT reg
;     )
;
; Routine Description:
;
;   This function queries the CPUID.
;
; Return Value:
;
;   Value of the ECX register.
;
;--

?BlGetCpuidEcx@@YAKK@Z proc

        mov     eax, ecx
        cpuid
        mov     eax, ecx
        ret
        
?BlGetCpuidEcx@@YAKK@Z endp

;++
;
; UINT
; BlGetCpuidEdx(
;     UINT reg
;     )
;
; Routine Description:
;
;   This function queries the CPUID.
;
; Return Value:
;
;   Value of the EDX register.
;
;--

?BlGetCpuidEdx@@YAKK@Z proc

        mov     eax, ecx
        cpuid
        mov     eax, edx
        ret

?BlGetCpuidEdx@@YAKK@Z endp

        
end
