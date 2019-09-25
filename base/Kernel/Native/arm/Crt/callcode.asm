;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; **************************************************************************

; Stolen from armtrap.s

  IF Thumbing

    MACRO
    CALL $Fn
    ldr     r12, =$Fn
    mov     lr, pc
    bx      r12
    MEND
    
    MACRO
    CALLEQ $Fn
    ldreq   r12, =$Fn
    moveq   lr, pc
    bxeq    r12
    MEND

    MACRO
    RETURN
    bx      lr
    MEND

    MACRO
    RETURN_EQ
    bxeq    lr
    MEND

    MACRO
    RETURN_NE
    bxne    lr
    MEND

  ELSE

    MACRO
    CALL $Fn
    bl      $Fn
    MEND

    MACRO
    CALLEQ $Fn
    bleq    $Fn
    MEND

    MACRO
    RETURN
    mov     pc, lr
    MEND

    MACRO
    RETURN_EQ
    moveq   pc, lr
    MEND

    MACRO
    RETURN_NE
    movne   pc, lr
    MEND

  ENDIF
    
	MACRO
	mfc15	$cpureg, $cp15reg
	mrc	p15,0,$cpureg,$cp15reg,c0,0
	MEND

; End of stuff stolen from armtrap.s

; **************************************************************************
	END
	
