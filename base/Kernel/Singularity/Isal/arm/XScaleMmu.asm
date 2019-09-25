;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;;
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; Assembly code for Isal.XScale.Mmu class

        CODE32

        AREA    |.text|, CODE, ARM
;;;
;;; Generic utilities
;;;
|defining ?g_GetTTB@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAPAUuintPtr@@XZ| EQU 1
|defining ?g_MemoryFence@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1
|defining ?g_FlushPrefetch@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1

;;;
;;; TLB management
;;;
|defining ?g_InvalidateIAndDTlb@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1
|defining ?g_InvalidateITlb@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1
|defining ?g_InvalidateDTlb@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1
|defining ?g_InvalidateITlbEntry@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z| EQU 1
|defining ?g_InvalidateDTlbEntry@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z| EQU 1

;;;
;;; Cache Management (public)
;;;

;;; L1D Whole Cache Ops
|defining ?g_CleanL1DCache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1
|defining ?g_CleanInvalidateL1DCache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1
|defining ?g_InvalidateL1DCache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1

;;; L1I Whole Cache Ops
|defining ?g_InvalidateL1ICache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1
|defining ?g_CleanInvalidateL1ICache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1

;;; L1D Cache Range Ops
|defining ?g_CleanL1DCacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z| EQU 1
|defining ?g_CleanInvalidateL1DCacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z| EQU 1
|defining ?g_InvalidateL1DCacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z| EQU 1

;;; L1I Cache Range Ops
|defining ?g_InvalidateL1ICacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z|

;;; L2 Whole Cache Ops
|defining ?g_CleanL2Cache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1
|defining ?g_CleanInvalidateL2Cache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ| EQU 1

;;; L2 Cache Range Ops
|defining ?g_CleanInvalidateL2CacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z| EQU 1
|defining ?g_CleanL2CacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z| EQU 1
|defining ?g_InvalidateL2CacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z| EQU 1

;;; Misc
|defining ?g_CleanDCacheLine@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z| EQU 1
|defining ?g_InvalidateICacheLine@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z| EQU 1
|defining ?g_CleanInvalidateDCacheLine@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z| EQU 1

        include hal.inc

        MACRO
        CPWAIT $scratch
        mrc     p15, 0, $scratch, c2, c0, 0             ; arbtrary read of p15
        mov     $scratch, $scratch                      ; wait for it
        sub     pc, pc, #4                              ; branch next instrct
        MEND

        MACRO
        DMB     $scratch
        mov     $scratch, #0
        mcr     p15, 0, $scratch, c7, c10, 5            ; Memory Barrier
        MEND

        MACRO
        DWB     $scratch
        mov     $scratch, #0
        mcr     p15, 0, $scratch, c7, c10, 4            ; Write Barrier
        MEND

        MACRO
        PF      $scratch
        mov     $scratch, #0
        mcr     p15, 0, $scratch, c7, c5, 4
        MEND

        MACRO
        INVALIDATE_L1_ICACHE_BTB $scratch
        mov     $scratch, #0
        mcr     p15, 0, $scratch, c7, c5, 0
        MEND

        MACRO
        CLEAN_L1_DCACHE_LINE $mva_register
        mcr     p15, 0, $mva_register, c7, c10, 1
        MEND

        MACRO
        INVALIDATE_L1_DCACHE_LINE $mva_register
        mcr     p15, 0, $mva_register, c7, c6, 1
        MEND

        MACRO
        INVALIDATE_L1_ICACHE_LINE $mva_register
        mcr     p15, 0, $mva_register, c7, c5, 1
        MEND

        MACRO
        CLEAN_INVALIDATE_L1_DCACHE_LINE $mva_register
        mcr     p15, 0, $mva_register, c7, c14, 1
        MEND

        MACRO
        CLEAN_INVALIDATE_L1_DCACHE_SETWAY $setway_register
        mcr     p15, 0, $setway_register, c7, c14, 2
        MEND

        MACRO
        CLEAN_L1_DCACHE_SETWAY $setway_register
        mcr     p15, 0, $setway_register, c7, c10, 2
        MEND

        MACRO
        INVALIDATE_L1_DCACHE $scratch
        mov     $scratch, #0
        mcr     p15, 0, $scratch, c7, c6, 0
        MEND

        MACRO
        CLEAN_L2_CACHE_LINE $mva_register
        mcr     p15, 1, $mva_register, c7, c11, 1
        MEND

        MACRO
        INVALIDATE_L2_CACHE_LINE $mva_register
        mcr     p15, 1, $mva_register, c7, c7, 1
        MEND

        MACRO
        CLEAN_INVALIDATE_L2_CACHE_SETWAY $setway
        mcr     p15, 1, $setway, c7, c15, 2
        MEND

        MACRO
        CLEAN_L2_CACHE_SETWAY $setway
        mcr     p15, 1, $setway, c7, c11, 2
        MEND

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; General utilities
;;;

;;;
;;; "public: static struct uintPtr * __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_GetTTB(void)"
;;;
        LEAF_ENTRY ?g_GetTTB@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAPAUuintPtr@@XZ
        mrc     p15, 0, r0, c2, c0, 0
        CPWAIT  r0
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_FlushPrefetch(void)"
;;;
        LEAF_ENTRY ?g_FlushPrefetch@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ
        PF      r0
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_MemoryFence(void)"
;;;
        LEAF_ENTRY ?g_MemoryFence@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ
        DMB     r0
        bx      lr
        LEAF_END

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; TLB management
;;;

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateIAndDTlb(void)"
;;;
        LEAF_ENTRY ?g_InvalidateIAndDTlb@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ
        mov     r0, #0
        mcr     p15, 0, r0, c8, c7, 0
        DWB     r0
        CPWAIT  r0
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateITlb(void)"
;;;
        LEAF_ENTRY ?g_InvalidateITlb@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ
        mov     r0, #0
        mcr     p15, 0, r0, c8, c5, 0
        CPWAIT  r0
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateDTlb(void)"
;;;
        LEAF_ENTRY ?g_InvalidateDTlb@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ
        mov     r0, #0
        mcr     p15, 0, r0, c8, c6, 0
        CPWAIT  r0
        bx      lr
        LEAF_END

;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateITlbEntry(struct uintPtr *)"
        LEAF_ENTRY ?g_InvalidateITlbEntry@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z
        mcr     p15, 0, r0, c8, c5, 1
        CPWAIT  r0
        bx      lr
        LEAF_END

;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateDTlbEntry(struct uintPtr *)"
        LEAF_ENTRY ?g_InvalidateDTlbEntry@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z
        mcr     p15, 0, r0, c8, c6, 1
        CPWAIT  r0
        bx      lr
        LEAF_END

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Cache management (rivate to XScaleMmu.cs)
;;;

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanInvalidateL1DCacheLines(struct uintptr* addr, struct uintptr* length)
;;;
        LEAF_ENTRY ?g_CleanInvalidateL1DCacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z

        cmp     r1, #0
        bxeq    lr

        PF      r2
        DMB     r2

        add     r1, r0, r1
        add     r1, r1, #31
        bic     r1, r1, #31
        bic     r0, r0, #31

|CleanInvalidateL1DLines|
        CLEAN_INVALIDATE_L1_DCACHE_LINE r0
        add     r0, r0, #32
        cmp     r0, r1
        bcc     |CleanInvalidateL1DLines|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanL1DCacheLines(struct uintptr* addr, struct uintptr* length)
;;;
        LEAF_ENTRY ?g_CleanL1DCacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z

        cmp     r1, #0
        bxeq    lr

        PF      r2
        DMB     r2

        add     r1, r0, r1
        add     r1, r1, #31
        bic     r1, r1, #31
        bic     r0, r0, #31

|CleanL1DLines|
        CLEAN_L1_DCACHE_LINE r0
        add     r0, r0, #32
        cmp     r0, r1
        bcc     |CleanL1DLines|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;"public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanInvalidateL2CacheLines(struct uintPtr *,struct uintPtr *)"
;;;
        LEAF_ENTRY ?g_CleanInvalidateL2CacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z

        cmp     r1, #0
        bxeq    lr

        PF      r2
        DMB     r2

        add     r1, r0, r1
        add     r1, r1, #31
        bic     r1, r1, #31
        bic     r0, r0, #31

|InvL2Loop|
        CLEAN_L2_CACHE_LINE             r0
        INVALIDATE_L2_CACHE_LINE        r0
        add     r0, r0, #32
        cmp     r0, r1
        bcc     |InvL2Loop|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;"public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanL2CacheLines(struct uintPtr *,struct uintPtr *)"
;;;
        LEAF_ENTRY ?g_CleanL2CacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z

        cmp     r1, #0
        bxeq    lr

        PF      r2
        DMB     r2

        add     r1, r0, r1
        add     r1, r1, #31
        bic     r1, r1, #31
        bic     r0, r0, #31

|CleanL2LinesLoop|
        CLEAN_L2_CACHE_LINE r0
        add     r0, r0, #32
        cmp     r0, r1
        bcc     |CleanL2LinesLoop|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateL1DCacheLines(struct uintPtr *,struct uintPtr *)"
;;;
        LEAF_ENTRY ?g_InvalidateL1DCacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z

        cmp     r1, #0
        bxeq    lr

        PF      r2
        DMB     r2

        add     r1, r0, r1
        add     r1, r1, #31
        bic     r1, r1, #31
        bic     r0, r0, #31

|InvalidateL1DLines|
        INVALIDATE_L1_DCACHE_LINE r0
        add     r0, r0, #32
        cmp     r0, r1
        bcc     |InvalidateL1DLines|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateL1ICacheLines(struct uintPtr *,struct uintPtr *)"
;;;
        LEAF_ENTRY ?g_InvalidateL1ICacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z

        cmp     r1, #0
        bxeq    lr

        PF      r2
        DMB     r2

        add     r1, r0, r1
        add     r1, r1, #31
        bic     r1, r1, #31
        bic     r0, r0, #31

|InvL1ILoop|
        INVALIDATE_L1_ICACHE_LINE  r0
        add     r0, r0, #32
        cmp     r0, r1
        bcc     |InvL1ILoop|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateL2CacheLines(struct uintPtr * addr,struct uintPtr * length)"
;;;
        LEAF_ENTRY ?g_InvalidateL2CacheLines@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@0@Z

        cmp     r1, #0
        bxeq    lr

        PF      r2
        DMB     r2

        add     r1, r0, r1
        add     r1, r1, #31
        bic     r1, r1, #31
        bic     r0, r0, #31

|InvalidateL2Lines|
        INVALIDATE_L2_CACHE_LINE r0
        add     r0, r0, #32
        cmp     r0, r1
        bcc     |InvalidateL2Lines|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateICacheLine(struct uintPtr*)"
;;;
        LEAF_ENTRY ?g_InvalidateICacheLine@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z
        INVALIDATE_L1_ICACHE_LINE r0
        INVALIDATE_L2_CACHE_LINE  r0
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateL1DCache(void)"
;;;
        LEAF_ENTRY ?g_InvalidateL1DCache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ
        INVALIDATE_L1_DCACHE r0
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanInvalidateL1DCache(void)" (?g_CleanInvalidateL1DCache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ)
;;;
        LEAF_ENTRY ?g_CleanInvalidateL1DCache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ

        PF      r0
        DMB     r0

        mov     r0, #0x1f00
        orr     r0, r0, #0xe0         ; 0x1fe = Way 0, Set 255
|CleanInvL1DLoop|
        CLEAN_INVALIDATE_L1_DCACHE_SETWAY       r0
        adds    r0, r0, #0x40000000
        bcc     |CleanInvL1DLoop|
        subs    r0, r0, #0x20
        bpl     |CleanInvL1DLoop|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanL1DCache(void)"
;;;
        LEAF_ENTRY ?g_CleanL1DCache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ

        PF      r0
        DMB     r0

        mov     r0, #0x1f00
        orr     r0, r0, #0xe0         ; 0x1fe = Way 0, Set 255
|CleanL1DLoop|
        CLEAN_L1_DCACHE_SETWAY       r0
        adds    r0, r0, #0x40000000
        bcc     |CleanL1DLoop|
        subs    r0, r0, #0x20
        bpl     |CleanL1DLoop|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanInvalidateL2Cache(void)"
;;;
        LEAF_ENTRY ?g_CleanInvalidateL2Cache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ

        PF      r0
        DMB     r0

        mov     r0, #0xff00
        orr     r0, r0, #0xe0         ; 0xffe0 = Way 0, Set 2047
|CleanInvL2Loop|
        CLEAN_INVALIDATE_L2_CACHE_SETWAY r0
        adds    r0, r0, #0x20000000
        bcc     |CleanInvL2Loop|
        subs    r0, r0, #0x00000020
        bpl     |CleanInvL2Loop|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanL2Cache(void)"
;;;
        LEAF_ENTRY ?g_CleanL2Cache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ

        PF      r0
        DMB     r0

        mov     r0, #0xff00
        orr     r0, r0, #0xe0         ; 0xffe0 = Way 0, Set 2047
|CleanL2Loop|
        CLEAN_L2_CACHE_SETWAY r0
        adds    r0, r0, #0x20000000
        bcc     |CleanL2Loop|
        subs    r0, r0, #0x00000020
        bpl     |CleanL2Loop|

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanInvalidateDCacheLine(uintptr*)"
;;;
        LEAF_ENTRY ?g_CleanInvalidateDCacheLine@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z

        PF      r1
        DMB     r1
        CLEAN_INVALIDATE_L1_DCACHE_LINE    r0
        CLEAN_L2_CACHE_LINE     r0
        INVALIDATE_L2_CACHE_LINE r0

        PF      r1
        DMB     r1
        CPWAIT  r1

        bx      lr
        LEAF_END
;;;
;;; public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_CleanDCacheLine(struct uintPtr *)"
;;;
        LEAF_ENTRY ?g_CleanDCacheLine@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXPAUuintPtr@@@Z
        PF      r1
        DMB     r1
        CLEAN_L1_DCACHE_LINE r0
        CLEAN_L2_CACHE_LINE  r0

        PF      r1
        DMB     r1
        CPWAIT  r1

        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu::g_InvalidateL1ICache(void)"
;;;
        LEAF_ENTRY ?g_InvalidateL1ICache@Class_Microsoft_Singularity_Isal_Arm_XScale_Mmu@@SAXXZ

        PF      r0
        DMB     r0
        INVALIDATE_L1_ICACHE_BTB r0

        PF      r0
        DMB     r0
        CPWAIT  r0

        bx      lr
        LEAF_END

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;
        END
