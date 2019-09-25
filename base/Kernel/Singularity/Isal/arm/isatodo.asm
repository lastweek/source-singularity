;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; Unimplemented stub routines for Isal.Isa class

        CODE32

        AREA    |.text|, CODE, ARM

|defining ?g_ReadMsr@Class_Microsoft_Singularity_Isal_Isa@@SA_KI@Z| EQU 1
|defining ?g_WriteMsr@Class_Microsoft_Singularity_Isal_Isa@@SAXI_K@Z| EQU 1

|defining ?g_EnterUserMode@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ| EQU 1

|defining ?g_InitFpu@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ| EQU 1
|defining ?g_ClearFpuStatus@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ| EQU 1
|defining ?g_ReadFpuStatus@Class_Microsoft_Singularity_Isal_Isa@@SAIXZ| EQU 1

|defining ?g_GetPageTableRoot@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@XZ| EQU 1
|defining ?g_InvalidateTLBEntry@Class_Microsoft_Singularity_Isal_Isa@@SAXPAUuintPtr@@@Z| EQU 1
|defining ?g_ChangePageTableRoot@Class_Microsoft_Singularity_Isal_Isa@@SAXI@Z| EQU 1        
|defining ?g_EnablePaging@Class_Microsoft_Singularity_Isal_Isa@@SAXI@Z| EQU 1
|defining ?g_DisablePaging@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ| EQU 1

|defining ?g_ReadCpuid@Class_Microsoft_Singularity_Isal_Isa@@SAXIPAI000@Z| EQU 1
|defining ?g_ReadPmc@Class_Microsoft_Singularity_Isal_Isa@@SA_KI@Z| EQU 1
        
        include hal.inc
        
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        MACRO
        BREAKPOINT
        ;; bkpt    0xffff
        swi     0xffff03
        MEND

;;;
;;; "public: static unsigned __int64 __cdecl Class_Microsoft_Singularity_Isal_Isa::g_ReadMsr(unsigned int)"
;;;
        LEAF_ENTRY ?g_ReadMsr@Class_Microsoft_Singularity_Isal_Isa@@SA_KI@Z
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Isa::g_WriteMsr(unsigned int,unsigned __int64)"
;;;
        LEAF_ENTRY ?g_WriteMsr@Class_Microsoft_Singularity_Isal_Isa@@SAXI_K@Z
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Isa::g_InitFpu(void)"
;;;
        LEAF_ENTRY ?g_InitFpu@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ
;;;     BREAKPOINT
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_ClearFpuStatus@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ
        BREAKPOINT
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_ReadFpuStatus@Class_Microsoft_Singularity_Isal_Isa@@SAIXZ
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static UIntPtr __cdecl Class_Microsoft_Singularity_Isal_Isa::g_GetPageTableRoot(void)"
;;;
        LEAF_ENTRY ?g_GetPageTableRoot@Class_Microsoft_Singularity_Isal_Isa@@SAPAUuintPtr@@XZ
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Isa::g_ChangePageTableRoot(unsigned int)"
;;;
        LEAF_ENTRY ?g_ChangePageTableRoot@Class_Microsoft_Singularity_Isal_Isa@@SAXI@Z
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Isa::g_EnablePaging(unsigned int)"
;;;
        
        LEAF_ENTRY ?g_EnablePaging@Class_Microsoft_Singularity_Isal_Isa@@SAXI@Z
        BREAKPOINT
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_DisablePaging@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ
        BREAKPOINT
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_EnterUserMode@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Isa::g_InvalidateTLBEntry(struct uintPtr *)"
;;;
        LEAF_ENTRY ?g_InvalidateTLBEntry@Class_Microsoft_Singularity_Isal_Isa@@SAXPAUuintPtr@@@Z
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Isa::g_ReadCpuid(unsigned int,unsigned int *,unsigned int *,unsigned int *,unsigned int *)"
;;;
        LEAF_ENTRY ?g_ReadCpuid@Class_Microsoft_Singularity_Isal_Isa@@SAXIPAI000@Z
        BREAKPOINT
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_ReadPmc@Class_Microsoft_Singularity_Isal_Isa@@SA_KI@Z
        BREAKPOINT
        bx      lr
        LEAF_END

        END

