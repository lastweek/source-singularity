;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

;
; void *
; memset( void *dest, int c, size_t count );
;
;       The memset function sets the first count bytes of 
;       dest to the character c (value).
;

	OPT	2	; disable listing
	INCLUDE kxarm.inc
	OPT	1	; reenable listing

value   RN  R1                  ; int c
count   RN  R2
dest    RN  R3
temp    RN  R12

  IF Thumbing
    THUMBAREA
  ENDIF

    NESTED_ENTRY memset
    PROLOG_END

  IF Thumbing
    ; Switch from Thumb mode to ARM mode
    DCW     0x4778              ; bx pc
    DCW     0x46C0              ; nop
  ENDIF

    SUBS    count, count, #4
    MOV     dest, R0            ;Save R0 for return
    BLT     BYTESET

    AND     value, value, #&FF
    ORR     value, value, value, LSL #8
CHECKALIGN                                          ; 2-3 cycles
    ANDS    temp, dest, #3      ;Check alignment and fix if possible
    BNE     ALIGN

BLOCKSET                                            ; 6-7 cycles
    ORR     value, value, value, LSL #16
    SUBS    count, count, #12
    MOV     temp, value
    BLT     BLKSET8

BLKSET16                                            ; 7 cycles/16 bytes
    STMIA   dest!, {value, temp}
    SUBS    count, count, #16
    STMIA   dest!, {value, temp}
    BGE     BLKSET16

BLKSET8                                             ; 4 cycles/8 bytes
    ADDS    count, count, #8
    STMGEIA dest!, {value, temp}
    SUBGE   count, count, #8

BLKSET4
    ADDS    count, count, #4                        ; 4 cycles/4 bytes
    STRGE   value, [dest], #4

BYTESET
    ADDLTS  count, count, #4
    BEQ     EXIT

    STRB    value, [dest],   #1                     ; 5 cycles/1-3bytes
    CMP     count, #2
    STRGEB  value, [dest],   #1
    STRGTB  value, [dest],   #1

EXIT

  IF Interworking :LOR: Thumbing
    BX      lr
  ELSE
    MOV     pc, lr
  ENDIF

ALIGN                                               ; 8 cycles/1-3 bytes
    TST     dest, #1            ;Check byte alignment
    SUBNE   count, count, #1
    STRNEB  value, [dest], #1
    TST     dest, #2            ;Check Half-word alignment
    SUBNE   count, count, #2
    STRNEH  value, [dest], #2
    B       BLOCKSET

    ENTRY_END
    END
