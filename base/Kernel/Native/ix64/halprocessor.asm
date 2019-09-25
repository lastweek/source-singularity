;; ----------------------------------------------------------------------------
;;
;;  Copyright (c) Microsoft Corporation.  All rights reserved.
;;
;; ----------------------------------------------------------------------------

;*******************************************************************************
;*******************************************************************************

;public g_GetCurrentProcessor@Class_Microsoft_Singularity_Processor@@SAPEAU1@XZ
include hal.inc

.code

?g_InitFpu@Class_Microsoft_Singularity_Processor@@SAXXZ proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fninit;
        mov rax, 37eh;
        push rax;
        fldcw [esp];
        pop rax;
        ;; Epilogue
        mov rsp, rbp
        pop rbp;
        ret;
?g_InitFpu@Class_Microsoft_Singularity_Processor@@SAXXZ endp

?g_ClearFpuStatus@Class_Microsoft_Singularity_Processor@@SAXXZ proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        fnclex;
        ;; Epilogue
        mov rsp, rbp
        pop rbp;
        ret;

?g_ClearFpuStatus@Class_Microsoft_Singularity_Processor@@SAXXZ endp

?g_EnterRing3@Class_Microsoft_Singularity_Processor@@SAXXZ proc
;;//    int uc3 = SEGMENT_SELECTOR(GdtUC) + 3;
;;//    int ud3 = SEGMENT_SELECTOR(GdtUD) + 3;
;;//    int uf3 = SEGMENT_SELECTOR(GdtPF) + 3; // for the moment, share UF and PF
;;// TODO: get rid of hexadecimal constants below

        push rdx
        mov rcx, rsp
        mov rdx, ring3
        db   0fh;
        db   35h;  ;;//sysexit
ring3:
        pop rdx
        mov cx, ss
        mov ds, cx
        mov es, cx
        mov ecx, 38h + 3 ;;// SEGMENT_SELECTOR(GdtPF) + 3
        mov fs, cx
        ret
 ?g_EnterRing3@Class_Microsoft_Singularity_Processor@@SAXXZ endp

?g_ReadFpuStatus@Class_Microsoft_Singularity_Processor@@SAIXZ proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        xor rax,rax;
        push rax;
        fnstsw [rsp];
        pop rax;
        ;; Epilogue
        mov rsp, rbp
        pop rbp;
        ret;
?g_ReadFpuStatus@Class_Microsoft_Singularity_Processor@@SAIXZ endp

?g_GetCS proc
        mov rax, cs
?g_GetCS endp

?g_GetCr3@Class_Microsoft_Singularity_Processor@@SAIXZ proc
        mov      rax, cr3
        ret
?g_GetCr3@Class_Microsoft_Singularity_Processor@@SAIXZ endp


?g_GetCycleCount@Class_Microsoft_Singularity_Processor@@SA_KXZ proc frame
        PrologPush rbp
        SetFramePointer rbp
        .endprolog
        rdtsc;  reads counter into edx:ecx (32-bits each)
        shl rdx, 32
        or  rax,rdx  ;; make it a 64-bit result
        ;; Epilogue
        mov rsp, rbp
        pop rbp;
        ret;
?g_GetCycleCount@Class_Microsoft_Singularity_Processor@@SA_KXZ endp

?g_GetFramePointer@Class_Microsoft_Singularity_Processor@@SAPEAUuintPtr@@XZ proc
        mov rax, rbp
        ret
?g_GetFramePointer@Class_Microsoft_Singularity_Processor@@SAPEAUuintPtr@@XZ endp

?g_MpCallEntryPoint@Class_Microsoft_Singularity_Processor@@SAXPEAUuintPtr@@@Z proc
        mov rax, rcx;
        call rax;
        ret
?g_MpCallEntryPoint@Class_Microsoft_Singularity_Processor@@SAXPEAUuintPtr@@@Z endp

;__declspec(naked)
;UIntPtr Class_Microsoft_Singularity_Processor::g_GetStackPointer()
?g_GetStackPointer@Class_Microsoft_Singularity_Processor@@SAPEAUuintPtr@@XZ proc
    mov     rax, rsp;
    ret;
?g_GetStackPointer@Class_Microsoft_Singularity_Processor@@SAPEAUuintPtr@@XZ  endp


;
; void Class_Microsoft_Singularity_Processor::g_Out(uint16 port, int value)
;

?g_Out@Class_Microsoft_Singularity_Processor@@SAXGH@Z           proc

        mov     eax, edx
        mov     dx, cx
        out     dx, eax
        ret

?g_Out@Class_Microsoft_Singularity_Processor@@SAXGH@Z           endp

end
