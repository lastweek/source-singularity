;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; format_f.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

        GET     fpe.asm
        GET     kxarm.inc

        CodeArea |FPL$$Format|

        IMPORT  __fp_norm_op1
        IMPORT  __fp_nonveneer_error

SNaNInf EQU     NaNInfExp_Single - EIExp_bias + SExp_bias
SExp_max * 255

exp     RN 3

;==============================================================================

        [ :DEF: f2e_s

        [ :DEF: thumb
        CODE32
        ]

        EXPORT  _f2e            ; Not needed, but is an example

_f2e    EnterWithLR
        MOVS    tmp,fOP,LSL #1          ;C:=sign; Z:=exp & frac.top zero
        MOV     OP1mhi,tmp,LSL #7       ;Frac.top in bits 30:11 of mhi
        MOV     fOP,tmp,LSR #20         ;Exponent in bits 11:1
        ADDNE   fOP,fOP,#(EIExp_bias - SExp_bias):SHL:1
        MOV     OP1sue,fOP,RRX         ;Recombine sign and exponent
        ORRNE   OP1mhi,OP1mhi,#EIUnits_bit
        MOV     OP1mlo,#0

        ; Single precision exponent<<1+SExp_pos is in tmp.
        ; If 0 then this is a denormalised number.
        ; If 1fe then this is an uncommon number.
        MOVS    tmp,tmp,LSR #1+SExp_pos
        ADDEQ   lr,pc,#8        ;Skip two instructions past normalise call
        BEQ     __fp_norm_op1
        TEQ     tmp,#&ff
        ORREQ   OP1sue,OP1sue,#Uncommon_bit
        ReturnToLR

        ]

;---------------------------------------------------------------------------

        [ :DEF: e2f_s

; Called from ARM code (no INTERWORK hacks needed).

        [ :DEF: thumb
        CODE32
        ]

        EXPORT  __fp_e2f

__fp_e2f
        
;Passed in the result of an operation. That is the uncommon/sign are in
;OP1sue, the exponent in RNDexp, the fraction in OP1mlo/OP1mhi. Return with
;a result in dOPh/dOPl and possibly some error flags in a4

        ASSERT  Uncommon_bit = 1:SHL:(31-1)
        ASSERT  EIUnits_bit = 1:SHL:31
        BICS    tmp, OP1mhi, OP1sue, LSL #1
        BPL     _e2f_SpecialCase

        SUBS    RNDexp, RNDexp, #(EIExp_bias-SExp_bias)
        BMI     _e2f_ExpUnderflow

        ASSERT  tmp <> RNDexp
        ADDNE   tmp, RNDexp, #1
        CMPNE   tmp, #SNaNInf+1
        BGE     _e2f_ExpOverflow

        MOVS    tmp, OP1mhi, LSR #32-SFrc_len-1
;If rounding is needed then a one will have dropped out.
        BCS     _e2f_NeedsRounding

; Simple case - just merge in the exponent and sign

        BIC     tmp, tmp, #1<<SFrc_len  ; clear out the J-bit
        ORR     fOP, OP1sue, RNDexp, LSL #SExp_pos
        ORR     fOP, fOP, tmp
        MOV     a4, #0
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

;...........................................................................

_e2f_SpecialCase

        TST     OP1sue, #Uncommon_bit
        BNE     _e2f_Uncommon

_e2f_UnitsBit

;Sign is in OP1sue's top bit. The units bit of OP1mhi is clear indicating a
;zero value (since the denorm case is handled by the uncommon bit).

        AND     dOPh, OP1sue, #Sign_bit
        MOV     a4, #0
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

;...........................................................................

_e2f_ExpOverflow

;Sign is in OP1sue's sign bit. May still need rounding. The exponent (RNDexp)
;is out of range for a double precision number, and wasn't signalled as a NaN.

;The exponent has been re-biased.

;Might just be the "just underflowing case" (because of a quirk above). In
;that case RNDexp = 0

        TEQ     RNDexp, #0
        MOVNE   a4, #OVF_bits
  IF Interworking :LOR: Thumbing
        BXNE    lr
  ELSE
        MOVNE   pc, lr
  ENDIF

;...........................................................................

_e2f_ExpUnderflow


;Underflow. If the value can be represented as a denorm in the target
;precision, then it should be. For this to be the case the exponent needs
;to lie in range. Otherwise the result is a suitably
;signed zero. (A zero is, however, a denorm with zero mantissa.)

;The exponent (RNDexp) has been rebiased (by (EIExp_bias-SExp_bias))

        ADDS    RNDexp, RNDexp, #SFrc_len

;If the result is zero then we round according to the top bit of the
;fraction. Branch out of line to do this.

        BEQ     _e2f_ExpJustUnderflow

;If this result is negative, nothing can be done, so return a signed zero.

        ANDMI   dOPh, OP1sue, #Sign_bit
        MOVMI   dOPl, #0
        MOVMI   a4, #0
  IF Interworking :LOR: Thumbing
        BXMI    lr
  ELSE
        MOVMI   pc, lr
  ENDIF

;We now have in OP1mhi 1MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
;and in OP1mlo         MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
;These need to be converted into a denormalised number. We want the N
;left most bits (N<=23) from this 64-bit value. So we are throwing
;away all the bits from the low word, and some from the high word.
;RNDexp contains the value ([1..23]) 

        MOVS    tmp, OP1mhi, LSL RNDexp
        BMI     _e2f_UnderflowNeedsRounding

        RSB     tmp, RNDexp, #32
        ORR     fOP, OP1sue, OP1mhi, LSR tmp
        MOV     a4, #0
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

_e2f_UnderflowNeedsRounding

;tmp contains those bits out of the high word that determine rounding.
;We add in the bits from the low word, and the sticky bits.

        ORR     tmp, Rarith, tmp, LSL #1
        ORRS    tmp, tmp, OP1mlo                ;C=1; Z=round to even

        RSB     tmp, RNDexp, #32

;Merge in the sign bit and add one (C flag). Undo the rounding if we
;need to round to even and the result

        ORR     fOP, OP1sue, OP1mhi, LSR tmp
        MOV     a4, #0
        TSTEQ   fOP, #1                         ;test for even
        ADDNE   fOP, fOP, #1
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

;...........................................................................

_e2f_ExpJustUnderflow

;The number may just be representable as the single precision epsilon.

        ORR     tmp, OP1mlo, OP1mhi, LSL #1
        ORRS    tmp, tmp, Rarith
        ASSERT  OP1sue = fOP
        ORRNE   fOP, OP1sue, #1
        MOV     a4, #0
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

;...........................................................................

_e2f_Uncommon

        TST     OP1sue, #Error_bit
        BNE     _e2f_Error
        MOV     a4, #0

;And infinity or a NaN. Infinity is signalled by mhi=mlo=0

        TEQ     OP1mhi, #0
        MOVNES  OP1mhi, OP1mhi, LSL #1
        MOVMI   fOP, #-1
  IF Interworking :LOR: Thumbing
        BXMI    lr
  ELSE
        MOVMI   pc, lr
  ENDIF
        TEQEQ   OP1mlo, #0
        MOVNE   a4, #IVO_bits
  IF Interworking :LOR: Thumbing
        BXNE    lr
  ELSE
        MOVNE   pc, lr
  ENDIF

;An infinity, whose sign is in the sue register.

        MOVS    OP1sue, OP1sue, LSL #1          ; C<-sign
        MOV     fOP, #&ff000000
        MOV     fOP, fOP, RRX                   ; add sign
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

_e2f_Error

        MOV     a4, OP1sue
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

;...........................................................................

_e2f_NeedsRounding

;The sign is in OP1sue, the exponent (in range) is in RNDexp.

        BIC     OP1mhi, OP1mhi, #EIUnits_bit

;Get the bits that are to be thrown away, except for the topmost one.

        ORR     tmp, OP1mlo, OP1mhi, LSL #SFrc_len+2
        ORRS    tmp, tmp, Rarith        ; Z<-round to even

        AND     tmp, OP1sue, #Sign_bit  ; save the real sign
        MOV     fOP, RNDexp, LSL #SExp_pos
        ORR     fOP, fOP, OP1mhi, LSR #32-SFrc_len-1

        MOV     a4, #0

        BEQ     _e2f_RoundToEven        ; go out of line for speed

        ADD     fOP, fOP, #1
        ADDS    a2, fOP, #1<<SExp_pos   ; can't be done in one add :-(
        ORR     fOP, fOP, tmp
  IF Interworking :LOR: Thumbing
        BXPL    lr
  ELSE
        MOVPL   pc, lr
  ENDIF
        MOV     a4, #OVF_bits
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

_e2f_RoundToEven
        TSTEQ   fOP, #1
        ORREQ   fOP, fOP, tmp
  IF Interworking :LOR: Thumbing
        BXEQ    lr
  ELSE
        MOVEQ   pc, lr
  ENDIF

        ADD     fOP, fOP, #1
        ADDS    a2, fOP, #1<<SExp_pos   ; can't be done in one add :-(
        ORR     fOP, fOP, tmp
  IF Interworking :LOR: Thumbing
        BXPL    lr
  ELSE
        MOVPL   pc, lr
  ENDIF
        MOV     a4, #OVF_bits
  IF Interworking :LOR: Thumbing
        BX      lr
  ELSE
        MOV     pc, lr
  ENDIF

        ]       

;---------------------------------------------------------------------------

        [ :DEF: fflt_s :LOR: :DEF: ffltu_s

        MACRO
        SingleNormalise

        MOVS    utmp1, a1, LSR #16
        MOVEQ   a1, a1, LSL #16
        SUBEQ   tmp, tmp, #16<<SExp_pos
        MOVS    utmp1, a1, LSR #24
        MOVEQ   a1, a1, LSL #8
        SUBEQ   tmp, tmp, #8<<SExp_pos
        MOVS    utmp1, a1, LSR #28
        MOVEQ   a1, a1, LSL #4
        SUBEQ   tmp, tmp, #4<<SExp_pos
        MOVS    utmp1, a1, LSR #30
        MOVEQ   a1, a1, LSL #2
        SUBEQ   tmp, tmp, #2<<SExp_pos
        MOVS    utmp1, a1, LSR #31
        MOVEQ   a1, a1, LSL #1
        SUBEQ   tmp, tmp, #1<<SExp_pos
        MOV     a1, a1, LSL #1  ; throw away top bit.

; Have the normalised number in a1. We need to (possibly) round it.
; Use a2 as a scratch temporary.

        MOVS    a2, a1, LSL #24                 ;C<-round Z<-sticky
        ORRCC   fOP, tmp, a1, LSR #SExp_len+1   ;no rounding needed
        ReturnToLR CC                           ; so return

        TSTEQ   a1, #1:SHL:(SExp_len+1)         ;Z<-even
        ORR     fOP, tmp, a1, LSR #SExp_len+1   ;combine exponext/sign/mantissa
        ADDNE   a1, a1, #1                      ;round
        ReturnToLR

        MEND

        ]

;...........................................................................

        [ :DEF: fflt_s

LOC_SIZE  EQU  0x18
OrgOp1l   EQU  0x10
ExDResl   EQU  0x08
NewResl   EQU  0x10

        Export  __itos
        Export  __utos
        IMPORT  FPE_Raise

; Prolog must be the same as __itos
    NESTED_ENTRY __utos
        EnterWithLR_16
        STMFD   sp!, {lr}                    ; Save return address
        SUB     sp, sp, #LOC_SIZE            ; Allocate local storage
    PROLOG_END

        MOV     r12, r0                      ; Keep original operand
        MOV     r2, #_FpUToS                 ; Initialize opcode
        MOV     exp, #(SExp_bias+1) << SExp_pos
        B       __fflt_normalise

   ENTRY_END __utos


; Prolog must be the same as __utos
    NESTED_ENTRY __itos
        EnterWithLR_16
        STMFD   sp!, {lr}                    ; Save return address
        SUB     sp, sp, #LOC_SIZE            ; Allocate local storage
    PROLOG_END

        MOV     r12, r0                      ; Keep original operand
        MOV     r2, #_FpIToS                 ; Initialize opcode
        ANDS    exp, a1, #Sign_bit
        RSBNE   a1, a1, #0
        ORR     exp, exp, #(SExp_bias+1) << SExp_pos
        ; fallthrough

__fflt_normalise        
        MOVS    a2, a1, LSR #16
        ADDNE   exp, exp, #16 << SExp_pos
        MOVEQS  a1, a1, LSL #16
        ADDEQ   sp, sp, #LOC_SIZE
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}                       ; a1 was zero - return +0
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}                       ; a1 was zero - return +0
  ENDIF
        TST     a1, #0xFF000000
        ADDNE   exp, exp, #8 << SExp_pos
        MOVEQ   a1, a1, LSL #8
        TST     a1, #0xF0000000
        ADDNE   exp, exp, #4 << SExp_pos
        MOVEQ   a1, a1, LSL #4
        TST     a1, #0xC0000000
        ADDNE   exp, exp, #2 << SExp_pos
        MOVEQS  a1, a1, LSL #2
        ; MI if high bit set, PL if not
        ADDMI   exp, exp, #1 << SExp_pos
        MOVPL   a1, a1, LSL #1
        MOVS    a2, a1, LSL #24             ; Check for inexact
        ORRNE   r2, r2, #INX_bit            ; If bits set, have inexact
        MOVS    a2, a1, LSL #25             ; CS -> round, EQ round to even
        ADC     a1, exp, a1, ASR #8         ; combine, subtract one from exponent
        BCC     __itos_return
        BNE     __itos_return
        BIC     a1, a1, #1

__itos_return
        TST     r2, #FPECause_mask          ; Check if any exceptions
        ADDEQ   sp, sp, #LOC_SIZE           ; If no exceptions, restore stack
  IF Interworking :LOR: Thumbing
        LDMEQFD sp!, {lr}                   ;   return
        BXEQ    lr
  ELSE
        LDMEQFD sp!, {pc}                   ;   return
  ENDIF
        STR     r0, [sp, #ExDResl]          ; Store default result
        ADD     r0, sp, #NewResl            ; Pointer to return value
        MOV     r1, r2                      ; Exception information
        MOV     r2, r12                     ; Original arg

        CALL    FPE_Raise                   ; Deal with exception information

    IF Thumbing :LAND: :LNOT: Interworking
        CODE16
        bx      pc              ; switch back to ARM mode
        nop
        CODE32
    ENDIF
	
	        LDR     r0, [sp, #NewResl]          ; Load returned value
        ADD     sp, sp, #LOC_SIZE           ; Restore stack
  IF Interworking :LOR: Thumbing
        LDMFD   sp!, {lr}                   ; Return
        BX      lr
  ELSE
        LDMFD   sp!, {pc}                   ; Return
  ENDIF

  ENTRY_END __itos

        ]

;---------------------------------------------------------------------------

        [ :DEF: ll_sto_f_s :LOR: :DEF: ll_uto_f_s

        MACRO
        LongSingleNormalise

        MOV     utmp1, #0
        MOVS    utmp2, a2, LSR #16
        MOVEQ   a2, a2, LSL #16
        ADDEQ   utmp1, utmp1, #16
        MOVS    utmp2, a2, LSR #24
        MOVEQ   a2, a2, LSL #8
        ADDEQ   utmp1, utmp1, #8
        MOVS    utmp2, a2, LSR #28
        MOVEQ   a2, a2, LSL #4
        ADDEQ   utmp1, utmp1, #4
        MOVS    utmp2, a2, LSR #30
        MOVEQ   a2, a2, LSL #2
        ADDEQ   utmp1, utmp1, #2
        MOVS    utmp2, a2, LSR #31
        MOVEQ   a2, a2, LSL #1
        ADDEQ   utmp1, utmp1, #1
        MOV     a2, a2, LSL #1

        SUB     tmp, tmp, utmp1, LSL #SExp_pos

        MOV     utmp2, a1

        ; take bits from high word into mantissa
        ORR     fOP, tmp, a2, LSR #SExp_len+1

        ; get 32 - (number of bits from other word needed in mantissa)
        RSB     utmp1, utmp1, #64-SFrc_len-1
        CMP     utmp1, #32

        BHI     %ft01
        ORR     fOP, fOP, utmp2, LSR utmp1
        RSB     utmp1, utmp1, #33
        MOVS    utmp2, utmp2, LSL utmp1 ; C <- round, Z <- sticky
        ReturnToLR CC
        B       %ft02

01      ; no words from high word - get round/carry from top word
        ORRS    a2, utmp2, a2, LSL #33-(SExp_len+1) ; C <- round, Z <- sticky
        ReturnToLR CC
02      ; test to-even case
        TSTEQ   fOP, #1
        ADDNE   fOP, fOP, #1
        ReturnToLR

        MEND

        ]

;...........................................................................

        [ :DEF: ll_sto_f_s

        Export  _ll_sto_f
        ImportCodeSize _ll_to_f_shared
        ROUT

_ll_sto_f EnterWithLR_16

        IMPORT  _ffltu

        TEQ     a2, #0
        BEQ     _ffltu          ; a 'normal' long

        ANDS    tmp, a2, #Sign_bit ; Extract sign
; sign in in tmp, denormalised mantissa in a1/a2
    [   CodeSize = 2
        BEQ     _ll_to_f_shared
    |
        ORR     tmp, tmp, #((SExp_bias + 63) :AND: 0xff00) << SExp_pos
      [ CodeSize = 1
        BEQ     _ll_to_f_shared
      |

        ORR     tmp, tmp, #((SExp_bias + 63) :AND: 0x00ff) << SExp_pos
        BEQ     %ft01
      ]
    ]
        RSBS    a1, a1, #0
        RSCS    a2, a2, #0
      [ CodeSize <> 0
        BNE     _ll_to_f_shared
      |
        BEQ     %ft02


01
        LongSingleNormalise

02
      ]
        EnterWithStack
        BL      _ffltu
        ORR     fOP, fOP, #Sign_bit
        ReturnToStack

        ]

;...........................................................................

        [ :DEF: ll_uto_f_s

        Export  _ll_uto_f
        ExportCodeSize  _ll_to_f_shared

_ll_uto_f EnterWithLR_16

        IMPORT  _ffltu

        TEQ     a2, #0
        BEQ     _ffltu

     [  CodeSize = 2
        MOV     tmp, #0

_ll_to_f_shared
        ORR     tmp, tmp, #((SExp_bias + 63) :AND: 0xff00) << SExp_pos
     |
        MOV     tmp, #((SExp_bias + 63) :AND: 0xff00) << SExp_pos
     ]
     [  CodeSize = 1
_ll_to_f_shared
     ]
        ORR     tmp, tmp, #((SExp_bias + 63) :AND: 0x00ff) << SExp_pos

        LongSingleNormalise

        ]


;===========================================================================

        [ :DEF: ffix_s

        Export  _ffix
        IMPORT  __fp_exception

_ffix   EnterWithLR_16
        MOVS    a3, fOP, ASR #SFrc_len
        MOV     a1, fOP, LSL #SExp_len
        ORR     a1, a1, #1 << 31
        BMI     _ffix_negative
        RSBS    a3, a3, #31 + SExp_bias
        MOVHI   a1, a1, LSR a3
        ReturnToLR HI                   ; 9 clk
        BIC     a1, a1, #1 << 31        ; clear high bit (positive)
        B       _ffix_ivo

_ffix_negative
        AND     a3, a3, #255
        RSBS    a3, a3, #31 + SExp_bias
        MOVHI   a1, a1, LSR a3
        RSBHI   a1, a1, #0              ; negative result
        ReturnToLR HI                   ; 11 clk
        TEQEQ   a1, #0x80000000         ; MinInt special case
        ReturnToLR EQ
        ; a1 negative
_ffix_ivo  
        CMP     a3, #(31 + SExp_bias) - SExp_max    ; EQ -> inf or NaN 
        MOV     ip, #IVO_bit :OR: FixFn
        BNE     __fp_exception
        MOVS    a2, a1, LSL #1          ; NE -> NaN
        MOVNE   ip, #IVO_bit :OR: FixZeroFn
        B       __fp_exception

        ]

;---------------------------------------------------------------------------

        [ :DEF: ffixu_s

        Export  _ffixu
        IMPORT  __fp_exception

_ffixu  EnterWithLR_16
        MOVS    a3, fOP, ASR #SFrc_len
        BMI     _ffixu_negative
        MOV     a1, fOP, LSL #SExp_len
        ORR     a1, a1, #1 << 31
        RSBS    a3, a3, #31 + SExp_bias
        MOVHS   a1, a1, LSR a3
        ReturnToLR HS
        BIC     a1, a1, #1 << 31        ; clear high bit (positive)
        B       _ffixu_ivo  

_ffixu_negative        
        MOVS    a1, fOP, LSL #1         ; don't generate IVO for -0
        ReturnToLR EQ
        MOV     a1, #0x80000000         ; negative
_ffixu_ivo     
        CMP     a3, #(31 + SExp_bias) - SExp_max    ; EQ -> inf or NaN 
        MOV     ip, #IVO_bit :OR: FixuFn
        BNE     __fp_exception
        MOVS    a2, a1, LSL #1          ; NE -> NaN
        MOVNE   ip, #IVO_bit :OR: FixZeroFn
        B       __fp_exception

        ]

;---------------------------------------------------------------------------

        [ :DEF: ll_sfrom_f_s

        Export  _ll_sfrom_f

        ROUT
_ll_sfrom_f EnterWithLR_16

        MOVS    a3, fOP, LSL #1 ; C <- sign
        MOV     a3, a3, LSR #SFrc_len+1 ; Get exponent
        MOV     a2, fOP, LSL #SExp_len ; mantissa + 1 spare bit
        ORR     a2, a2, #1<<31  ; add units bit
        ; mantissa is in a2

        BCS     ll_from_f_neg

        SUBS    a3, a3, #SExp_bias
        BMI     _ll_from_f_zero
        RSBS    a4, a3, #31

        MOVGT   a1, a2, LSR a4
        MOVGT   a2, #0
        ReturnToLR GT

        ADDS    a4, a4, #32
        SUB     a3, a3, #31
        MOVGT   a1, a2, LSL a3
        MOVGT   a2, a2, LSR a4
        ReturnToLR GT
        ; fall through

        BIC     a1, a1, #Sign_bit               ; return +ve value
        B       _ll_from_f_ivo

_ll_from_f_zero
        MOV     a1, #0
        MOV     a2, #0
        ReturnToLR

ll_from_f_neg
        SUBS    a3, a3, #SExp_bias
        BMI     _ll_from_f_zero
        RSBS    a4, a3, #31

        MOVPL   a1, a2, LSR a4
        MOVPL   a2, #0
        BPL     %ft01

        ADDS    a4, a4, #32
        SUB     a3, a3, #31
        BLE     %ft02
        MOV     a1, a2, LSL a3
        MOV     a2, a2, LSR a4

01      RSBS    a1, a1, #0
        RSC     a2, a2, #0

        ReturnToLR

02
; Special case - INT_MIN will leave a shift of zero (Z set), and
; r0=0x80000000 r1=0x00000000
        TEQEQ   a2, #Sign_bit
        MOVEQ   a1, #0
        ReturnToLR EQ

        ORR     a1, a1, #Sign_bit           ; return -ve value
_ll_from_f_ivo
        ; On some systems, casting NaN returns zero
        ; check for maximum exponent
        ADD     a3, a4, #:NOT:(63-((SExp_mask:SHR:SExp_pos)-SExp_bias))
        CMN     a3, #1
        MOV     a4, #IVO_bit :OR: FixFn :OR: LongLong_bit
        BNE     __fp_nonveneer_error
        MOVS    tmp, a2, LSL #1 ; ignore units bit
        MOVNE   a4, #IVO_bit :OR: FixZeroFn :OR: LongLong_bit     
        B       __fp_nonveneer_error
        ]

;---------------------------------------------------------------------------

        [ :DEF: ll_ufrom_f_s


        Export  _ll_ufrom_f
        ExportCodeSize  _ll_from_f_shared
        ExportCodeSize  _ll_from_f_zero

_ll_ufrom_f EnterWithLR_16

        MOVS    a3, fOP, LSL #1 ; C <- sign
        BHI     _ll_ufrom_f_neg
        MOV     a3, a3, LSR #SFrc_len+1
        MOV     a2, fOP, LSL #SExp_len
        ORR     a2, a2, #1<<31

        SUBS    a3, a3, #SExp_bias
        BMI     _ll_ufrom_f_zero
        RSBS    a4, a3, #31

        MOVPL   a1, a2, LSR a4
        MOVPL   a2, #0
        ReturnToLR PL

        ADDS    a4, a4, #32
        SUB     a3, a3, #31
        MOVPL   a1, a2, LSL a3
        MOVPL   a2, a2, LSR a4
        ReturnToLR PL
        ; fall through

_ll_ufrom_f_ivo
        BIC     a1, a1, #Sign_bit ; return unsigned result
        ; On some systems, casting NaN returns zero
        ; check for maximum exponent
        ADD     a3, a4, #:NOT:(63-((SExp_mask:SHR:SExp_pos)-SExp_bias))
        CMN     a3, #1
        MOV     a4, #IVO_bit :OR: FixuFn :OR: LongLong_bit
        BNE     __fp_nonveneer_error
        MOVS    tmp, a2, LSL #1 ; ignore units bit
        MOVNE   a4, #IVO_bit :OR: FixZeroFn :OR: LongLong_bit     
        B       __fp_nonveneer_error

_ll_ufrom_f_neg
        MOV     a4, #IVO_bit :OR: FixZeroFn :OR: LongLong_bit
        B       __fp_nonveneer_error

_ll_ufrom_f_zero
        MOV     a1, #0
        MOV     a2, #0
        ReturnToLR      

        ]

;===========================================================================

        END
