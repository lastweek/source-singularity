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

.686p
.model flat
.code

assume ds:flat
assume es:flat
assume ss:flat
assume fs:flat

;++
;
; ULONG_PTR
; FASTCALL
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

?BlMmGetCr3@@YIKXZ proc

        mov     eax, cr3
        ret

?BlMmGetCr3@@YIKXZ endp

;++
;
; VOID
; FASTCALL
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

?BlMmSetCr3@@YIXK@Z proc

        mov     cr3, ecx
        ret

?BlMmSetCr3@@YIXK@Z endp

;++
;
; VOID
; FASTCALL
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

?BlMmGetGdtr@@YIXPAU_GDTR@@@Z proc

        sgdt    fword ptr [ecx]
        ret

?BlMmGetGdtr@@YIXPAU_GDTR@@@Z endp

;++
;
; VOID
; FASTCALL
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

?BlMmSetGdtr@@YIXPAU_GDTR@@@Z proc

        lgdt    fword ptr [ecx]
        ret

?BlMmSetGdtr@@YIXPAU_GDTR@@@Z endp

;++
;
; USHORT
; FASTCALL
; BlMmGetFs(
;     VOID
;     )
;
; Routine Description:
;
;   This function queries the FS register.
;
; Return Value:
;
;   Value of the FS register.
;
;--

@BlMmGetFs@0 proc

        mov     ax, fs
        ret

@BlMmGetFs@0 endp

;++
;
; VOID
; FASTCALL
; BlMmSetFs(
;     USHORT Value
;     )
;
; Routine Description:
;
;   This function sets the FS register.
;
; Arguments:
;
;   Value       - Supplies the value to write to the FS register.
;
;--

?BlMmSetFs@@YIXG@Z proc

        mov     fs, cx
        ret

?BlMmSetFs@@YIXG@Z endp

;++
;
; VOID
; FASTCALL
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

?BlMmSwitchStack@@YIXPAX0@Z proc

        mov     esp, ecx
        call    edx

@@:
        jmp     @b

?BlMmSwitchStack@@YIXPAX0@Z endp

;++
;
; PVOID
; FASTCALL
; BlRtlGetEbp(
;     VOID
;     )
;
; Routine Description:
;
;   This function queries the value of the EBP register.
;
; Return Value:
;
;   Value of the EBP register.
;
;--

?BlRtlGetEbp@@YIPAXXZ proc

        mov     eax, ebp
        ret

?BlRtlGetEbp@@YIPAXXZ endp
        
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

?BlGetCpuidEax@@YIKK@Z proc

        mov     eax, ecx
        cpuid
        ret

?BlGetCpuidEax@@YIKK@Z endp

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

?BlGetCpuidEbx@@YIKK@Z proc

        mov     eax, ecx
        cpuid
        mov     ebx, eax
        ret

?BlGetCpuidEbx@@YIKK@Z endp

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

?BlGetCpuidEcx@@YIKK@Z proc

        mov     eax, ecx
        cpuid
        mov     eax, ecx
        ret
        
?BlGetCpuidEcx@@YIKK@Z endp

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

?BlGetCpuidEdx@@YIKK@Z proc

        mov     eax, ecx
        cpuid
        mov     eax, edx
        ret

?BlGetCpuidEdx@@YIKK@Z endp

        
end
