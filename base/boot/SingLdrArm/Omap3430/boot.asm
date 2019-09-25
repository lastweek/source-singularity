;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; Singularity ARM bootstrap entry point.
;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

SINGLE_CPU      equ {TRUE}

OMAP3430_CPU_ARGS_ADDR  equ     0x8000fff0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
        
        CODE32

        AREA    |.text|, CODE, ARM

        EXPORT  |BootEntry|
        IMPORT  |?BootPhase1@@YAHXZ|

|BootEntry| PROC
        str     lr, [sp, #-4]!
        sub     sp, sp, #8

        ;; Put the processor in System mode.
        mov     r6, sp
        mrs     r4, cpsr
        bic     r5, r4, #0x1F
        orr     r5, r5, #0x1F
        msr     cpsr_c, r5
        mov     sp, r6
        
        bl      |?BootPhase1@@YAHXZ|
        str     r0, [sp, #4]
        ldr     r3, [sp, #4]
        str     r3, [sp]

        ldr     r0, [sp]
        add     sp, sp, #8
        ldr     pc, [sp], #4
        
        ENDP

        EXPORT |?GetStack@@YAIXZ|
|?GetStack@@YAIXZ| PROC
        mov     r0, sp
        bx      lr
        ENDP
        
        EXPORT |?GetCode@@YAIXZ|
|?GetCode@@YAIXZ| PROC
        mov     r0, lr
        bx      lr
        ENDP
        
        EXPORT |?DebugBreak@@YAXXZ|
|?DebugBreak@@YAXXZ| PROC
        bkpt    0xffff
        bx      lr
        ENDP

;;; "uint32 GetMidr(void)"
        
        EXPORT |?GetMidr@@YAIXZ|    
|?GetMidr@@YAIXZ| PROC
        mrc     p15,0,r0,c0,c0,0    
        bx      lr
        ENDP
        
;;; "uint32 GetPfr0(void)"
        
        EXPORT |?GetPfr0@@YAIXZ|    
|?GetPfr0@@YAIXZ| PROC
        mrc     p15,0,r0,c0,c1,0    
        bx      lr
        ENDP
        
;;; "uint32 GetPfr1(void)"
        
        EXPORT |?GetPfr1@@YAIXZ|    
|?GetPfr1@@YAIXZ| PROC
        mrc     p15,0,r0,c0,c1,1    
        bx      lr
        ENDP

;;; "uintptr GetVbar(void)"
        
        EXPORT |?GetVbar@@YAIXZ|
|?GetVbar@@YAIXZ| PROC
        mrc     p15,0,r0,c12,c0,0
        bx      lr
        ENDP
        
;;; "void SetVbar(uintptr)"
        
        EXPORT |?SetVbar@@YAXI@Z|
|?SetVbar@@YAXI@Z| PROC
        mcr     p15,0,r0,c12,c0,0
        bx      lr
        ENDP
        
;;; void SetTpidrurw(uintptr)
        EXPORT |?SetTpidrurw@@YAXI@Z|
|?SetTpidrurw@@YAXI@Z| PROC

 IF SINGLE_CPU
        ldr     r1, =OMAP3430_CPU_ARGS_ADDR
        str     r0, [r1]
 ELSE
        mcr     p15,0,r0,c13,c0,2 ;; Write ARMv7 CP15 User R/W Thread ID Register (TPIDRURW)
 ENDIF
        bx      lr
        ENDP
        
        END
