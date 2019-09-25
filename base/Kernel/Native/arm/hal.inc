;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;;
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; Include file for ARM assembly files.
;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

OMAP3430_CPU_ARGS_ADDR  equ     0x8000fff0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;

        include halclass.armfix.inc
        include kxarm.inc

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Macros for accessing fields inside ProcessorContext
;;;
;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; TPIDRURW ([OMAP3430_CPU_ARGS_ADDR] on older processors) points to the "fs/gs" page.
;;; The CurrentThread and CurrentCpu pointers are stored at offsets on that page.
;;;
        MACRO
        GET_TPIDRURW $reg

        ldr     $reg, =OMAP3430_CPU_ARGS_ADDR
        ldr     $reg, [$reg]

        MEND

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Get the address of the CurrentThread variable.
;;;
        MACRO
        GET_THREAD_ADDR $reg, $scratch

        ;; Workaround assembler bug with ldr $reg, =foo
        ldr     $scratch, [pc]
        mov     pc, pc  ;; skip over dcd value.
        dcd     |?c_currentThreadOffset@Class_Microsoft_Singularity_Isal_Isa@@2HA|
        ldr     $scratch, [$scratch]

        GET_TPIDRURW $reg
        add     $reg, $reg, $scratch

        MEND

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Get the address of the CurrentCpu variable.
;;;
        MACRO
        GET_CPU_ADDR $reg, $scratch

        ;; Workaround assembler bug with ldr $reg, =foo
        ldr     $scratch, [pc]
        mov     pc, pc
        dcd     |?c_currentCpuOffset@Class_Microsoft_Singularity_Isal_Isa@@2HA|
        ldr     $scratch, [$scratch]

        GET_TPIDRURW $reg
        add     $reg, $reg, $scratch

        MEND

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Get the address of a field in the CurrentThread record.
;;;
        MACRO
        GET_THREAD_FIELD_ADDR $reg, $scratch, $offset

        GET_THREAD_ADDR $reg, $scratch
        ldr     $reg, [$reg]
        add     $reg, $reg, $offset

        MEND

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Get the address of a field in the CurrentCpu record.
;;;
        MACRO
        GET_CPU_FIELD_ADDR $reg, $scratch, $offset

        GET_CPU_ADDR $reg, $scratch
        ldr     $reg, [$reg]
        add     $reg, $reg, $offset

        MEND


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Push a register onto the stack.
;;;
        MACRO
        PUSH $reg
        str     $reg, [sp, #-4]!
        MEND

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Pop a register from the stack.
;;;
        MACRO
        POP $reg
        ldr     $reg, [sp], #4
        MEND


        MACRO
        CurrentThreadIndex $reg, $tmpReg
        mov $reg, sp, LSR #PAGE_BITS
        mov $reg, $reg, LSL #2
        ldr $tmpReg, pageTable
        add $reg, $reg, $tmpReg
        ldr $reg, [$reg]
        ldr $tmpReg, =0xFFF
        and $reg, $tmpReg, $reg, LSR #4
        MEND

    EXTERN |?c_halPageDescriptor@Class_System_GCs_PageTable@@2PAIA|
    EXTERN |?c_threadTable@Class_System_Threading_Thread@@2PAUClassVector_Class_System_Threading_Thread@@A|
;    EXTERN |?c_initialThread@Class_System_Threading_Thread@@2PAU1@A|

pageTable
    DCD |?c_halPageDescriptor@Class_System_GCs_PageTable@@2PAIA|
threadTable
    DCD |?c_threadTable@Class_System_Threading_Thread@@2PAUClassVector_Class_System_Threading_Thread@@A|

    MACRO
    ThreadFromIndex $reg, $tmpReg
            mov $reg, $reg, LSL #2
            add $reg, $reg, #8
            ldr $tmpReg, threadTable
            ldr $tmpReg, [$tmpReg]
            add $reg, $reg, $tmpReg
            ldr $reg, [$reg]
    MEND

    MACRO
    CurrentThread $reg, $tmpReg
    CurrentThreadIndex $reg, $tmpReg
    ThreadFromIndex $reg, $tmpReg
    MEND

    END
