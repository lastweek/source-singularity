;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity ARM Bootstrap
;;;
;;; Xscale varient of the cycle counter routines
;;;

|defining ?g_GetCycleCount@Class_Microsoft_Singularity_Isal_Isa@@SA_KXZ| EQU 1
|defining ?g_EnableCycleCounter@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ| EQU 1

        include hal.inc

        IMPORT |?g_EnableInterrupts@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ|
        IMPORT |?g_DisableInterrupts@Class_Microsoft_Singularity_Isal_Isa@@SA_NXZ|

        TEXTAREA

CycleCountHi DCD 0 ; storage for upper 32--bits of cycle counter (extended)

;;;
;;; Reset cycle counter
;;;
;;; "void __cdecl ResetCycleCounter(void)"
;;;
        LEAF_ENTRY ?ResetCycleCounter@@YAXXZ
        mov     r1, #0
        mrc     p14, 0, r1, c0, c0, 0   ; read PMCR
        orr     r1, r1, #4              ; set C
        mcr     p14, 0, r1, c0, c0, 0   ; set PMCR
        bx      lr
        LEAF_END

;;;
;;; Check for cycle counter wrap and clean
;;;
;;; "bool __cdecl CycleCounterWrapped(void)"
;;;
        LEAF_ENTRY ?CycleCounterWrapped@@YA_NXZ
        mov     r1, #0
        bx      lr
        LEAF_END

;;;
;;; Enable cycle counter
;;;
;;; "void __cdecl EnableCycleCounter(void)"
;;;
        LEAF_ENTRY ?g_EnableCycleCounter@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ
        mov     r1, #0
        mrc     p14, 0, r1, c0, c1, 0   ; read PMCR
        orr     r1, r1, #1              ; set E (enable) bit, disable interrupts
        mcr     p14, 0, r1, c0, c1, 0   ; write PMCR
        bx      lr
        LEAF_END

;;;
;;; Disable cycle counter
;;;
;;; "void __cdecl DisableCycleCounter(void)"
;;;
        LEAF_ENTRY ?DisableCycleCounter@@YAXXZ
        mov     r1, #0
        mrc     p14, 0, r1, c0, c1, 0   ; read PMCR
        bic     r1, r1, #1              ; clear E (enable) bit
        mcr     p14, 0, r1, c0, c1, 0   ; write PMCR
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned __int64 __cdecl Class_Microsoft_Singularity_Processor::g_GetCycleCount(void)"
;;;
        NESTED_ENTRY ?g_GetCycleCount@Class_Microsoft_Singularity_Isal_Isa@@SA_KXZ

        stmfd   sp!, {r4,lr}

        PROLOG_END

        ;; Disable interrupts, r0 becomes do_restore
        bl      |?g_DisableInterrupts@Class_Microsoft_Singularity_Isal_Isa@@SA_NXZ|
        mov     r2, r0                                  ; r2 becomes do_restore

        ;; Increment high bits if wrap has occurred
        adr     r3, CycleCountHi                        ; r3 is pointer to hi
        ldr     r0, [r3]                                ; r0 is cycle count hi

        mrc     p14, 0, r1, c5, c1, 0                   ; r1 is FLAG
        ands    r1, r1, #1                              ; r1 is CCNT wrapped

        mcrne   p14, 0, r1, c5, c1, 0                   ; clear bit if set
        addne   r0, r0, r1                              ; increment count hi
        strne   r0, [r3]                                ; store count hi
        mov     r3, r0                                  ; r3 is cycle count hi
        mrc     p14, 0, r4, c1, c1, 0                   ; r4 becomes cycle cnt

        ;; Restore interrupts
        cmp     r2, #0
        blne    |?g_EnableInterrupts@Class_Microsoft_Singularity_Isal_Isa@@SAXXZ|

        mov     r0, r4                                  ; r0 is cycle count lo
        mov     r1, r3                                  ; r1 is cycle count hi
        ldmfd   sp!, {r4,lr}

        bx      lr
        NESTED_END

        END
