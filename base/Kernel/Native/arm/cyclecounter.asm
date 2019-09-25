;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity ARM Bootstrap
;;;
;;;

|defining ?g_GetCycleCount@Class_Microsoft_Singularity_Isal_Isa@@SA_KXZ| EQU 1
|defining ?g_EnableCycleCounter@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ| EQU 1
                
        include hal.inc

        TEXTAREA
        
;;;
;;; Reset cycle counter
;;;
;;; "void __cdecl ResetCycleCounter(void)"
;;;
        LEAF_ENTRY ?ResetCycleCounter@@YAXXZ
        mrc     p15, 0, r1, c9, c12, 0  ; read PMCR
        orr     r1, r1, #8              ; set C
        mcr     p15, 0, r1, c9, c12, 0  ; set PMCR

;       bkpt    0xffff
        bx      lr
        LEAF_END

;;;
;;; Check for cycle counter wrap
;;;
;;; "bool __cdecl CycleCounterWrapped(void)"
;;;
        LEAF_ENTRY ?CycleCounterWrapped@@YA_NXZ
        mrc     p15, 0, r1, c9, c12, 3  ; read overflow status
        mov     r1, r1, lsr #31         ; move CC overflow to bit 0
        and     r0, r1, #1              ; check bit 0

;       bkpt    0xffff
        bx      lr
        LEAF_END

;;;
;;; Clear cycle counter wrap flag
;;;
;;; "void __cdecl ClearCycleCounterWrap(void)"
;;;
        LEAF_ENTRY ?ClearCycleCounterWrap@@YAXXZ
        mrc     p15, 0, r1, c9, c12, 3  ; read overflow status
        bic     r1, r1, #0x80000000     ; clear CC overflow bit
        mcr     p15, 0, r1, c9, c12, 3  ; set overflow status

;       bkpt    0xffff
        bx      lr
        LEAF_END        

;;;
;;; Enable cycle counter
;;;
;;; "void __cdecl EnableCycleCounter(void)"
;;;
        LEAF_ENTRY  ?g_EnableCycleCounter@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ
        mrc     p15, 0, r1, c9, c12, 0  ; read PMCR
        orr     r1, r1, #1              ; set E (enable) bit
        mcr     p15, 0, r1, c9, c12, 0  ; write PMCR

        mrc     p15, 0, r1, c9, c12, 1  ; read PM count enable set register
        orr     r1, r1, #0x80000000     ; set C (CC enable) bit
        mcr     p15, 0, r1, c9, c12, 1  ; write PM count enable set register

;       bkpt    0xffff
        bx      lr
        LEAF_END

;;;
;;; Disable cycle counter
;;;
;;; "void __cdecl DisableCycleCounter(void)"
;;;
        LEAF_ENTRY ?DisableCycleCounter@@YAXXZ
        mrc     p15, 0, r1, c9, c12, 1  ; read PM count enable set register
        bic     r1, r1, #0x80000000     ; clear C (CC enable) bit
        mcr     p15, 0, r1, c9, c12, 1  ; write PM count enable set register

        mrc     p15, 0, r1, c9, c12, 0  ; read PMCR
        bic     r1, r1, #1              ; clear E (enable) bit
        mcr     p15, 0, r1, c9, c12, 0  ; write PMCR

;       bkpt    0xffff
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned __int64 __cdecl Class_Microsoft_Singularity_Isal_Isa::g_GetCycleCount(void)"
;;;
        LEAF_ENTRY ?g_GetCycleCount@Class_Microsoft_Singularity_Isal_Isa@@SA_KXZ
        mrc     p15, 0, r0, c9, c13, 0  
        mov     r1, #0

;       bkpt    0xffff
        bx      lr
        LEAF_END

;;;
;;; "unsigned __int64 __cdecl RDTSC(void)"
;;;
        LEAF_ENTRY ?RDTSC@@YA_KXZ
        mrc     p15, 0, r0, c9, c13, 0  
        mov     r1, #0

;       bkpt    0xffff
        bx      lr
        LEAF_END
        
        END
