;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;;
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SA?AUStruct_System_Threading_ThreadState@@PAU2@U2@1@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SAHPAHHH@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SAIPAIII@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SAMPAMMM@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUClass_System_Object@@PAPAU2@PAU2@1@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUStruct_Microsoft_Singularity_Memory_HandleTable_HandleEntry@@PAPAU2@PAU2@1@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUStruct_Microsoft_Singularity_Memory_HandleTable_HandlePage@@PAPAU2@PAU2@1@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUuintPtr@@PAPAU2@PAU2@1@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUvoid@@PAPAU2@PAU2@1@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SA_JPA_J_J1@Z| EQU 1
|defining ?g_CompareExchange@Class_System_Threading_Interlocked@@SA_KPA_K_K1@Z| EQU 1
|defining ?g_Decrement@Class_System_Threading_Interlocked@@SAHPAH@Z| EQU 1
|defining ?g_Exchange@Class_System_Threading_Interlocked@@SAHPAHH@Z| EQU 1
|defining ?g_Exchange@Class_System_Threading_Interlocked@@SAIPAII@Z| EQU 1
|defining ?g_Exchange@Class_System_Threading_Interlocked@@SAMPAMM@Z| EQU 1
|defining ?g_Exchange@Class_System_Threading_Interlocked@@SAPAUClass_System_Object@@PAPAU2@PAU2@@Z| EQU 1
|defining ?g_Exchange@Class_System_Threading_Interlocked@@SAPAUuintPtr@@PAPAU2@PAU2@@Z| EQU 1
|defining ?g_Increment@Class_System_Threading_Interlocked@@SAHPAH@Z| EQU 1
        
        include hal.inc

        MACRO
        BREAKPOINT
        bkpt    0xffff
        swi     0xffff03
        MEND

        MACRO
        DISABLE_INTERRUPTS $savereg, $tempreg
        mrs     $savereg, cpsr
        orr     $tempreg, $savereg, #Struct_Microsoft_Singularity_Isal_Arm_Psr_DisableIrq
        msr     cpsr_c, $tempreg
        MEND

        MACRO
        RESTORE_INTERRUPTS $savereg
        msr     cpsr_c, $savereg
        MEND

        TEXTAREA
        
;;; uint32 InterlockedCompareExchange(uint32 * dst, uint32 exc, uint32 cmp)
        LEAF_ENTRY InterlockedCompareExchange
        DISABLE_INTERRUPTS r3, r12
        ldr     r12, [r0]
        cmp     r12, r2
        bne     %F1
        str     r1, [r0]
1       mov     r0, r12        
        RESTORE_INTERRUPTS r3
        bx      lr
        LEAF_END

;;; uint32 InterlockedExchange(uint32 * dst, uint32 exc, uint32 cmp)
        LEAF_ENTRY InterlockedExchange
        DISABLE_INTERRUPTS r3, r12
        ldr     r12, [r0]
        str     r1, [r0]
        mov     r0, r12
        RESTORE_INTERRUPTS r3
        bx      lr
        LEAF_END

;;; uint32 InterlockedExchangeAdd(uint32 * dst, uint32 val)
        LEAF_ENTRY InterlockedExchangeAdd
        DISABLE_INTERRUPTS r3, r12
        ldr     r12, [r0]
        add     r1, r12, r1
        str     r1, [r0]
        mov     r0, r12        
        RESTORE_INTERRUPTS r3
        bx      lr
        LEAF_END

;;; uint32 InterlockedIncrement(uint32 * dst)
        LEAF_ENTRY InterlockedIncrement
        DISABLE_INTERRUPTS r3, r12
        ldr     r1, [r0]
        add     r1, r1, #1
        str     r1, [r0]
        mov     r0, r1
        RESTORE_INTERRUPTS r3
        bx      lr
        LEAF_END

;;; uint32 InterlockedDecrement(uint32 * dst)
        LEAF_ENTRY InterlockedDecrement
        DISABLE_INTERRUPTS r3, r12
        ldr     r1, [r0]
        sub     r1, r1, #1
        str     r1, [r0]
        mov     r0, r1
        RESTORE_INTERRUPTS r3
        bx      lr
        LEAF_END

;;; 
;;; uint64 InterlockedCompareExchange64(
;;;     r0 = uint64 *dst, 
;;;     r1/r2 = uint64 exc, 
;;;     r3/[sp] = uint64 cmp)
;;; 
        NESTED_ENTRY InterlockedCompareExchange64
        stmdb   sp!, {r4-r7, lr}
        PROLOG_END
        DISABLE_INTERRUPTS r5, r12      ; save cpsr to r5
        ldr     r4, [sp, #0x14]         ; load r4 with Comperand.HighPart

        ldr     r6, [r0, #0]            ; load r6 with *dst.LowPart
        ldr     r7, [r0, #4]            ; load r7 with *dst.HighPart
        
        cmp     r6, r3                  ; compare orginal with cmp
        bne     %F1
        cmp     r7, r4
        bne     %F1

        str     r1, [r0, #0]            ; store exc.LowPart
        str     r2, [r0, #4]            ; store exc.HighPart

1       mov     r0, r6                  ; prepare to return original
        mov     r1, r7                  ;

        RESTORE_INTERRUPTS r5
        ldmia   sp!, {r4-r7, pc}
        NESTED_END
        
;;;
;;; int Class_System_Threading_Interlocked::g_CompareExchange(
;;;     int * dst,
;;;     int exc,
;;;     int cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SAHPAHHH@Z
        b       InterlockedCompareExchange
        nop
        LEAF_END
        
;;;
;;; unsigned int Class_System_Threading_Interlocked::g_CompareExchange(
;;;     unsigned int *dst,
;;;     unsigned int exc,
;;;     unsigned int cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SAIPAIII@Z
        b       InterlockedCompareExchange
        nop
        LEAF_END
        
;;;
;;; float Class_System_Threading_Interlocked::g_CompareExchange(
;;;     float *dst,
;;;     float exc,
;;;     float cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SAMPAMMM@Z
        b       InterlockedCompareExchange
        nop
        LEAF_END

;;;
;;; struct Class_System_Object * Class_System_Threading_Interlocked::g_CompareExchange(
;;;     struct Class_System_Object ** dst,
;;;     struct Class_System_Object * exc,
;;;     struct Class_System_Object * cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUClass_System_Object@@PAPAU2@PAU2@1@Z
        b       InterlockedCompareExchange
        nop
        LEAF_END

;;;
;;; struct Class_System_Threading_ThreadState Class_System_Threading_Interlocked::g_CompareExchange(
;;;     struct Class_System_Threading_ThreadState *dst,
;;;     struct Class_System_Threading_ThreadState exc,
;;;     struct Class_System_Threading_ThreadState cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SA?AUStruct_System_Threading_ThreadState@@PAU2@U2@1@Z
        b       InterlockedCompareExchange
        nop
        LEAF_END

;;;
;;; struct Struct_Microsoft_Singularity_Memory_HandleTable_HandleEntry * Class_System_Threading_Interlocked::g_CompareExchange(
;;;     struct Struct_Microsoft_Singularity_Memory_HandleTable_HandleEntry ** dst,
;;;     struct Struct_Microsoft_Singularity_Memory_HandleTable_HandleEntry * exc,
;;;     struct Struct_Microsoft_Singularity_Memory_HandleTable_HandleEntry * cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUStruct_Microsoft_Singularity_Memory_HandleTable_HandleEntry@@PAPAU2@PAU2@1@Z
        b       InterlockedCompareExchange
        nop
        LEAF_END

;;;
;;; struct Struct_Microsoft_Singularity_Memory_HandleTable_HandlePage * Class_System_Threading_Interlocked::g_CompareExchange(
;;;     struct Struct_Microsoft_Singularity_Memory_HandleTable_HandlePage ** dst,
;;;     struct Struct_Microsoft_Singularity_Memory_HandleTable_HandlePage * exc,
;;;     struct Struct_Microsoft_Singularity_Memory_HandleTable_HandlePage * cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUStruct_Microsoft_Singularity_Memory_HandleTable_HandlePage@@PAPAU2@PAU2@1@Z
        b       InterlockedCompareExchange
        nop
        LEAF_END

;;;
;;; struct uintPtr * Class_System_Threading_Interlocked::g_CompareExchange(
;;;     struct uintPtr ** dst,
;;;     struct uintPtr * exc,
;;;     struct uintPtr * cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUuintPtr@@PAPAU2@PAU2@1@Z
        b       InterlockedCompareExchange
        nop
        LEAF_END

;;;
;;; struct void * Class_System_Threading_Interlocked::g_CompareExchange(
;;;     struct void ** dst,
;;;     struct void * exc,
;;;     struct void * cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SAPAUvoid@@PAPAU2@PAU2@1@Z
        b       InterlockedCompareExchange
        nop
        LEAF_END

;;;
;;; __int64 Class_System_Threading_Interlocked::g_CompareExchange(
;;;     __int64 *dst,
;;;     __int64 exc,
;;;     __int64 cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SA_JPA_J_J1@Z
        b       InterlockedCompareExchange64
        nop
        LEAF_END

;;;
;;; unsigned __int64 Class_System_Threading_Interlocked::g_CompareExchange(
;;;     unsigned __int64 *dst,
;;;     unsigned __int64 exc,
;;;     unsigned __int64 cmp)
;;;
        LEAF_ENTRY ?g_CompareExchange@Class_System_Threading_Interlocked@@SA_KPA_K_K1@Z
        b       InterlockedCompareExchange64
        nop
        LEAF_END

;;;
;;; int Class_System_Threading_Interlocked::g_Decrement(int * dst)
;;;
        LEAF_ENTRY ?g_Decrement@Class_System_Threading_Interlocked@@SAHPAH@Z
        b       InterlockedDecrement
        nop
        LEAF_END

;;;
;;;- int Class_System_Threading_Interlocked::g_Exchange(int * dst,
;;;     int exc)
;;;
        LEAF_ENTRY ?g_Exchange@Class_System_Threading_Interlocked@@SAHPAHH@Z
        b       InterlockedExchange
        nop
        LEAF_END

;;;
;;;- unsigned int Class_System_Threading_Interlocked::g_Exchange(unsigned int * dst,
;;;     unsigned int exc)
;;;
        LEAF_ENTRY ?g_Exchange@Class_System_Threading_Interlocked@@SAIPAII@Z
        b       InterlockedExchange
        nop
        LEAF_END

;;;
;;; float Class_System_Threading_Interlocked::g_Exchange(float * dst,
;;;     float exc)
;;;
        LEAF_ENTRY ?g_Exchange@Class_System_Threading_Interlocked@@SAMPAMM@Z
        b       InterlockedExchange
        nop
        LEAF_END

;;;
;;;- struct Class_System_Object * Class_System_Threading_Interlocked::g_Exchange(
;;;     struct Class_System_Object ** dst,
;;;     struct Class_System_Object * exc)
;;;
        LEAF_ENTRY ?g_Exchange@Class_System_Threading_Interlocked@@SAPAUClass_System_Object@@PAPAU2@PAU2@@Z
        b       InterlockedExchange
        nop
        LEAF_END

;;;
;;; struct uintPtr * Class_System_Threading_Interlocked::g_Exchange(struct uintPtr ** dst,
;;;     struct uintPtr * exc)
;;;
        LEAF_ENTRY ?g_Exchange@Class_System_Threading_Interlocked@@SAPAUuintPtr@@PAPAU2@PAU2@@Z
        b       InterlockedExchange
        nop
        LEAF_END

;;;
;;; int Class_System_Threading_Interlocked::g_Increment(int * dst)
;;;
        LEAF_ENTRY ?g_Increment@Class_System_Threading_Interlocked@@SAHPAH@Z
        b       InterlockedIncrement
        nop
        LEAF_END
        
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        END
