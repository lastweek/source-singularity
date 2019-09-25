;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

;
;div64.s - perform __int64 right shift operation
;
        OPT     2       ; disable listing
        INCLUDE kxarm.inc
        OPT     1       ; reenable listing

        IMPORT      __rt_div0

        TEXTAREA


;******************************************************************************

    NESTED_ENTRY __rt_udivrem64by64

        stmdb     sp!, {r4 - r6, r10, r11, lr}

    PROLOG_END

        orrs      r11, r2, r3   ;  check to see if y is 0
        bne       |YIsNotZero|  
;
;   Divide by zero has occurred. Raise an exception
;   call RaiseException(STATUS_INTEGER_DIVIDE_BY_ZERO, 0, 0, NULL)
;
        bl        __rt_div0  ; __rt_div0 just calls RaiseException with above args.
        mvn       r0, #0
        mvn       r1, #0
        mvn       r2, #0
        mvn       r3, #0
        b         |ReturnQAndMod|
|YIsNotZero|
        mov       r5, #0        ; r5 and r6 hold __int64 q;
        mov       r6, #0
        cmp       r3, r1        ; Is y>x ?
        bhi       |ReturnQAndMod|
        bcc       |YLTEQX_A|  
        cmp       r2, r0      
        bhi       |ReturnQAndMod|
|YLTEQX_A|
        
        ands      r11, r3, #2, 2        ; check if y's high bit is set 
        bpl       |HighBitNotSetForY|  
        mov       r5, #1        ;  r6 already stores 0, q=1
        subs      r0, r0, r2    ;  subcract y from x, x = x % y
        sbc       r1, r1, r3    ;       
        b         |ReturnQAndMod|
|HighBitNotSetForY|
        mov       r10, #1       ; r10 and r4 hold __int64 mod;
        mov       r4, #0
|YLTEQX_B|
        mov       r3, r3, lsl #1           ; y <<= 1;
        mov       r11, r4, lsl #1          ; mask <<= 1;
        orr       r3, r3, r2, lsr #31
        orr       r4, r11, r10, lsr #31
        mov       r10, r10, lsl #1
        mov       r2, r2, lsl #1
        movs      r11, r3, lsr #31
        bne       |HighBitYisSet|             ;y is as big as possible 
        cmp       r3, r1  
        bcc       |YLTEQX_B|   ;  loop if yhi-xhi < 0
        bhi       |ShiftYAndMask|;  break if yhi-xhi > 0 
        cmp       r2, r0             
        bls       |YLTEQX_B|    ; loop ylo - xlo <= 0
        b         |ShiftYAndMask|    
|YGTX_A|
        adds      r5, r10, r5  ; q+=mask
        adc       r6, r4, r6
        subs      r0, r0, r2  ; x-=y
        sbc       r1, r1, r3
|ShiftYAndMask|
        mov       r11, r3, lsl #31        ;  y>>=1 mask>>=1
        orr       r2, r11, r2, lsr #1
        mov       r11, r4, lsl #31
        orr       r10, r11, r10, lsr #1
        mov       r4, r4, lsr #1
        mov       r3, r3, lsr #1
|HighBitYisSet|
        orrs      r11, r10, r4            ;  Is mask 0?
        beq       |ReturnQAndMod|
        cmp       r3, r1  
        bcc       |YGTX_A|   ;  loop if r1 > r3 or x >= y
        bhi       |ShiftYAndMask|  
        cmp       r2, r0             
        bls       |YGTX_A|      ; loop y <= x   
        b         |ShiftYAndMask|  
|ReturnQAndMod|
        mov       r2, r0        ;  move the remainder to r2 and r3
        mov       r3, r1
        mov       r0, r5        ;  put the quotient in r0, r1
        mov       r1, r6
        ldmia     sp!, {r4 - r6, r10, r11, lr}  ; ldmfd
        
      IF Interworking
        BX        lr
      ELSE
        MOV       pc, lr
      ENDIF

    ENTRY_END
        
        
;******************************************************************************

    NESTED_ENTRY __rt_divrem64by64

        stmdb     sp!, {r10, r11, lr} 

    PROLOG_END

        ands      r10, r1, #2, 2        ; check if x's sign bit is set 
        bpl       |CompareY|  
        rsbs      r0, r0, #0    ; x=-x;
        rsc       r1, r1, #0
|CompareY|
        ands      r11, r3, #2, 2        ; check if y's sign bit is set 
        bpl       |DoUDiv|
        rsbs      r2, r2, #0    ; y=-y;
        rsc       r3, r3, #0
|DoUDiv|
        bl        |__rt_udivrem64by64|;
        cmp       r10, #0
        beq       |NumeratorPos|
        rsbs      r2, r2, #0    ; modulus has same sign as numerator
        rsc       r3, r3, #0
|NumeratorPos|  
        cmp       r10, r11
        beq       |QPos|
        rsbs      r0, r0, #0    ; Quotient sign reveral
        rsc       r1, r1, #0
|QPos|
        ldmia     sp!, {r10, r11, lr}
        
      IF Interworking
        BX        lr
      ELSE
        MOV       pc, lr
      ENDIF
        
    ENTRY_END



;******************************************************************************

    NESTED_ENTRY __rt_udiv64by64

        stmdb sp!, {lr}

    PROLOG_END

        bl __rt_udivrem64by64
        ldmia  sp!, {lr}

      IF Interworking
        BX        lr
      ELSE
        MOV       pc, lr
      ENDIF
        
    ENTRY_END


;******************************************************************************

    NESTED_ENTRY __rt_urem64by64
      
        stmdb sp!, {lr}

    PROLOG_END

        bl __rt_udivrem64by64
        mov    r0,r2
        mov    r1,r3
        ldmia  sp!, {lr}
            
      IF Interworking
        BX        lr
      ELSE
        MOV       pc, lr
      ENDIF
        
    ENTRY_END


;******************************************************************************

    NESTED_ENTRY __rt_sdiv64by64
        
        stmdb sp!, {lr}

    PROLOG_END

        bl __rt_divrem64by64
        ldmia  sp!, {lr}

      IF Interworking
        BX        lr
      ELSE
        MOV       pc, lr
      ENDIF
        
    ENTRY_END


;******************************************************************************
            
    NESTED_ENTRY __rt_srem64by64
    
        stmdb sp!, {lr}

    PROLOG_END

        bl __rt_divrem64by64
        mov    r0,r2
        mov    r1,r3
        ldmia  sp!, {lr}
        
      IF Interworking
        BX        lr
      ELSE
        MOV       pc, lr
      ENDIF

    ENTRY_END

        
        END
        


