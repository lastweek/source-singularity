;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; except.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

;==============================================================================
;Error generation - from ANSI library

        GET     fpe.asm
        GET     h_errors.asm

        [ :DEF: liberror_s

	AREA   |.text|, CODE, READONLY

        Export_32  __fp_edom
        Export_32  __fp_erange

;  __fp_edom(ulong sign_bit, boolean huge_val);
;  __fp_erange(ulong sign_bit, boolean huge_val);
;
; set errno to EDOM/ERANGE and return sign_bit | (huge_val ? HUGE_VAL : 0)

__fp_edom EnterWithLR
        MOV     a3, #EDOM
        B       skip
__fp_erange EnterWithLR
        MOV     a3, #ERANGE
skip
        AND     a4, a1, #Sign_bit
    [ :DEF:EMBEDDED_CLIB
        IMPORT  __rt_errno_addr
        LDR     a1, =__rt_errno_addr
        CMP     a1, #0
        BEQ     %FT1
        STMDB   sp!, {a2-a4, lr}
        BL      __rt_errno_addr
        LDMIA   sp!, {a2-a4, lr}
        STR     a3, [a1]
1
    |
        LDR     a1, errno
        STR     a3, [a1]
    ]
        TEQ     a2, #0
        MOVEQ   a1, #0          ; generate +/- 0.0 in a1/a2
        LDRNE   a1, huge_val
        LDMNEIA a1, {a1, a2}    ; load HUGE_VAL into a1/a2
        ORR     a1, a1, a4      ; add in sign bit
        ReturnToLR

    [ :LNOT::DEF:EMBEDDED_CLIB
errno
        IMPORT  __errno
        DCD     __errno
    ]
 
huge_val
        IMPORT  __huge_val
        DCD     __huge_val

        ]

;==============================================================================
;Setting/returning status flags.

        [ :DEF: status_s

	AREA   |.text|, CODE, READONLY

        EXPORT  __fp_status

; extern unsigned int __fp_status(unsigned int mask,unsigned int flags)

__fp_status

        [ :DEF: thumb

        CODE16
        ; mask "mask" to an acceptable value
        MOV     a4,#&e0
        LSL     a3,a1,#32-FPExceptE_pos-Except_len
        LSR     a3,a3,#32-FPExceptE_pos-Except_len
        BIC     a3,a4
        LSR     a4,#8
        BIC     a3,a4
        AND     a4,a1
        ORR     a3,a1
        AND     a2,a3
        ; mask in a3, masked flags in a2
        LDR     a4,status_ptr
        LDR     a1,[a4]
        ; **** *WARNING* is ip spare under the TPCS ????? ****
        MOV     ip,a1           ; store value
        BIC     a1,a3
        EOR     a1,a2
        STR     a1,[a4]
        MOV     a1,ip           ; restore value
        BX      lr
        ALIGN

        |

        ; mask "mask" to an acceptable value
        MOV     a3,a1,LSL #32-FPExceptE_pos-Except_len
        BIC     a3,a3,#&e0:SHL:(32-FPExceptE_pos-Except_len)
        BIC     a3,a3,#&e0:SHL:(32-FPExceptE_pos-Except_len+8)
        AND     a2,a2,a3,LSR #32-FPExceptE_pos-Except_len
        ; mask in a3, masked flags in a2.
        LDR     a4,status_ptr
        LDR     a1,[a4]          ; load old flags
        BIC     a3,a1,a3,LSR #32-FPExceptE_pos-Except_len
        EOR     a3,a3,a2         ; clear/set/toggle flags and
        STR     a3,[a4]          ; write back.
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc,lr            ; return 
  ENDIF

        ]

status_ptr
        IMPORT  __fp_status_flags
        DCD     __fp_status_flags

        ]

;==============================================================================
;Error checking - from fplib code

        [ :DEF: fcheck_s

	AREA   |.text|, CODE, READONLY

        [ :DEF: thumb
        CODE32
        ]

        EXPORT __fp_fcheck_NaN2
        EXPORT __fp_dcheck_NaN2
        EXPORT __fp_return_NaN
        EXPORT __fp_return_Inf
        IMPORT __fp_exception


; Check fOP1 and fOP2 for signalling NaN, IP contains exception flags.

__fp_fcheck_NaN2    
        MOV     a4, #0x01000000
        CMN     a4, fOP1, LSL #1
        BLS     fcheck_opnd2_NaN
fcheck_opnd1_NaN
        TST     fOP1, #fSignalBit
        BEQ     __fp_exception
        CMN     a4, fOP2, LSL #1
        BLS     __fp_return_NaN
fcheck_opnd2_NaN
        MOV     fOP1, fOP2
        TST     fOP1, #fSignalBit
        BNE     __fp_return_NaN                ;; RDCFix: Do we really want to do this?
;	BEQ	__fp_return_NaN	
        B       __fp_exception

; Check dOP1 and dOP2 for signalling NaN, IP contains exception flags.

__fp_dcheck_NaN2
        STMFD   sp!, {ip}
        MOV     tmp, #0x00200000
        CMN     tmp, dOP1h, LSL #1
        CMPEQ   dOP1l, #0
        BLS     dcheck_opnd2_NaN
dcheck_opnd1_NaN
        TST     dOP1h, #dSignalBit
        LDMEQFD sp!, {ip}
        BEQ     __fp_exception
        CMN     tmp, dOP2h, LSL #1
        CMPEQ   dOP2l, #0
        LDMLSFD sp!, {ip}
        BLS     __fp_return_NaN
dcheck_opnd2_NaN
        LDMFD   sp!, {ip}
        MOV     dOP1h, dOP2h
        MOV     dOP1l, dOP2l
        TST     dOP1h, #dSignalBit
        BNE     __fp_return_NaN               ;; RDCFix: Do we really want to do this?
;	BEQ	__fp_return_NaN
        B       __fp_exception

; Return NaN in fOP / dOP, except for non-float returning functions. 
; IP contains exception flags.

__fp_return_NaN 
        ; test for special cases

;;
;; RDCFix: Will need to fix this once new defines are in.  May want to
;;         do some performance enhancements to keep from needing to check
;;         each _Fp* operation code.  Maybe a jump table.  Maybe forget
;;         this garbage and make the core emulation routines pack up
;;         their proper results instead of hacking them up here.
;;
;        AND     a4, ip, #Fn_mask
;        CMP     a4, #CompareFalseFn
;        CMPNE   a4, #FixZeroFn
;        BEQ     return_zero
;        CMP     a4, #CompareTrueFn
;        BEQ     return_one
;        CMP     a4, #CmpLessFn
;        BEQ     return_HI
;        CMP     a4, #CmpGreaterFn
;        BEQ     return_LO
;        CMP     a4, #CmpEqualFn
;        BEQ     return_NE
;        CMP     a4, #FixFn
;        BEQ     return_smaxint
;        CMP     a4, #FixuFn
;        BEQ     return_umaxint
        ReturnToLR

return_HI
        MOV     a1, #1
        CMP     a1, #0
        ReturnToLR_flg
       
return_LO             
        MOV     a1, #0
        CMP     a1, #1
        ReturnToLR_flg

return_NE             
        MOVS    a1, #1
        ReturnToLR_flg

return_one
        MOV     a1, #1
        ReturnToLR

return_zero
        MOV     a1, #0
        MOV     a2, #0
        ReturnToLR

return_smaxint
        MOV     a3, a1
        TST     ip, #LongLong_bit
        MOVEQ   a1, #0x7fffffff
        MOVNE   a1, #0xffffffff
        MOVNE   a2, #0x7fffffff
        TST     a3, #Sign_bit
        MVNNE   a1, a1
        MVNNE   a2, a2        
        ReturnToLR

return_umaxint
        MOV     a1, #0xffffffff
        MOV     a2, #0xffffffff
        ReturnToLR

__fp_return_Inf
        ; no special cases
        ReturnToLR

        ]

;==============================================================================
;Error generation - from fplib code

        [ :DEF: except_s

	AREA   |.text|, CODE, READONLY

; SWI Names

        [ :DEF: thumb
        CODE32
        ]

        EXPORT  __fp_veneer_error
        EXPORT  __fp_nonveneer_error
        EXPORT  __fp_exception
        IMPORT  __fp_return_NaN
        IMPORT  __fp_return_Inf

__fp_veneer_error           ; a4 contains the exception flags

__fp_nonveneer_error        ; a4 contains the exception flags OBSOLETE
        MOV     ip, a4
        ; fallthrough

; fp_exception is called when an IEEE exception has occurred 

; a1 contains the sign of the NaN to be returned if the exception is disabled
; ip contains the exception flags (see fpe.s for a list)

__fp_exception

	IMPORT	FPE_Raise

    STMDB   sp!,{lr}

    TST     ip,#OVF_bit
    BNE     overflow
    TST     ip,#UNF_bit
    BNE     underflow
    TST     ip,#DVZ_bit
    BNE     divide_by_zero
    TST     ip,#INX_bit
    BNE     divide_by_zero

invalid_operation
    BL  return_NaN
    B   callraise

overflow
    BL  return_Inf
    B   callraise

underflow
    MOV a1, #0
    MOV a2, #0
    B   callraise

inexact
    B   callraise

divide_by_zero
    BL  return_Inf

callraise

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {lr}
    BX      lr
  ELSE
    LDMIA   sp!, {pc}
  ENDIF

;GenerateError
;	IMPORT 	RaiseException
;    [ :DEF:EMBEDDED_CLIB
;        STMDB   sp!, {r0-r15}
;        SUB     lr, lr, #4
;        STR     lr, [sp, #15*4]
;        MOV     r1, sp
;    |
;        LDR     r1,ErrBlock
;        SUB     lr,lr,#4
;        STR     lr,[r1,#15*4]
;        MOV     lr,#&de00
;        ORR     lr,lr,#&00ad
;        ORR     lr,lr,lr,LSL #16
;        STMIA   r1,{r0-r14}

;        B       RaiseException

status_ptr
        IMPORT  __fp_status_flags
        DCD     __fp_status_flags

ErrBlock
        IMPORT  __fp_errblock
        DCD     __fp_errblock

trap
;    ]

        IMPORT  __rt_trap
        LDR     ip, =__rt_trap
        CMP     ip, #0
    [ Interworking :LOR:(:DEF:thumb)
        BXNE    ip
    |
        MOVNE   pc, ip
    ]
        DCD     0xe6000010

        ErrorBlock FP_IVO, "Floating Point Exception: Invalid Operation"
        ErrorBlock FP_OFL, "Floating Point Exception: Overflow"
        ErrorBlock FP_DVZ, "Floating Point Exception: Divide By Zero"

return_Inf
        AND     a3,a1,#Sign_bit
        TST     ip,#Double_bit
        ADRNE   a1,prototype_double_Inf
        LDMNEIA a1,{a1,a2}
        LDREQ   a1,prototype_single_Inf
        ORR     a1,a1,a3
        B       __fp_return_Inf

return_NaN
        AND     a3, a1, #Sign_bit
        TST     ip, #Double_bit
        ADRNE   a1,prototype_double_NaN
        LDMNEIA a1,{a1,a2}
        LDREQ   a1,prototype_single_NaN
        ORR     a1, a1, a3
        B       __fp_return_NaN

prototype_double_Inf
        DCD     &7ff00000,&00000000
prototype_single_Inf
        DCD     &7f800000
prototype_double_NaN
        DCD     &7ff00000,&00000001
prototype_single_NaN
        DCD     &7f800001

        ]

;------------------------------------------------------------------------------

        [ :DEF: fpdata_s

	AREA   |.data|, DATA

        EXPORT  __fp_status_flags
__fp_status_flags
        ; default - all flags enabled.
        DCD     (&40:SHL:SysID_pos):OR:(((1:SHL:Except_len)-1):SHL:FPExceptE_pos)

        EXPORT  __fp_errblock
__fp_errblock
        DCD     0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0, 0

        EXPORT __rt_trap
__rt_trap
        DCD     0
        ]

;==============================================================================

        END
