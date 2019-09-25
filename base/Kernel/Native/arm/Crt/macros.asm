;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; Assembler source for FPA support code and emulator
; ==================================================
; Some useful assembler macros. Also used by "fplib".
;
; Copyright (C) Advanced RISC Machines Limited, 1992-7. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

;===========================================================================

; Register names used when isolating the base register of a PC-relative or
; register-relative expression in the macros below. The technique is to set
; a temporary arithmetic variable Base to :BASE:(expression), then refer to
; R$Base.

R00000000       RN      R0
R00000001       RN      R1
R00000002       RN      R2
R00000003       RN      R3
R00000004       RN      R4
R00000005       RN      R5
R00000006       RN      R6
R00000007       RN      R7
R00000008       RN      R8
R00000009       RN      R9
R0000000A       RN      R10
R0000000B       RN      R11
R0000000C       RN      R12
R0000000D       RN      R13
R0000000E       RN      R14
R0000000F       RN      R15

;===========================================================================

; Two general purpose arithmetic variables.

        GBLA    Tempa
        GBLA    Tempa2

;===========================================================================

; The following macro is useful for shifting bit fields around when their
; positions are symbolic constants - which makes it unclear to the author
; whether LSR or LSL is needed.

        MACRO
$label  BiShift $opc,$Rd,$Rn,$Rm,$rshift,$lshift
        [ "$lshift":LEFT:5 <> "LSL #"
          ! 4,"Left shift must start exactly 'LSL #'"
        |
          [ "$rshift":LEFT:5 <> "LSR #"
            ! 4,"Right shift must start exactly 'LSR #'"
          |
            LCLS left
            LCLS right
left        SETS "$lshift":RIGHT:(:LEN:"$lshift" - 5)
right       SETS "$rshift":RIGHT:(:LEN:"$rshift" - 5)
            [ "$Rn" = ""
              ASSERT (("$opc":LEFT:3) <> "LDR") :LAND: (("$opc":LEFT:3) <> "STR")
              [ ($right) > ($left)
$label                          $opc    $Rd,$Rm,LSR #(($right) - ($left))
              |
$label                          $opc    $Rd,$Rm,LSL #(($left) - ($right))
              ]
            |
              [ ($right) > ($left)
                [ (("$opc":LEFT:3) = "LDR") :LOR: (("$opc":LEFT:3) = "STR")
$label                          $opc    $Rd,[$Rn,$Rm,LSR #(($right) - ($left))]
                |
$label                          $opc    $Rd,$Rn,$Rm,LSR #(($right) - ($left))
                ]
              |
                [ (("$opc":LEFT:3) = "LDR") :LOR: (("$opc":LEFT:3) = "STR")
$label                          $opc    $Rd,[$Rn,$Rm,LSL #(($left) - ($right))]
                |
$label                          $opc    $Rd,$Rn,$Rm,LSL #(($left) - ($right))
                ]
              ]
            ]
          ]
        ]
        MEND

;===========================================================================

; The following macro isolates the exponent field from the standard sign/
; uncommon bit/exponent word, putting it at the top of the destination
; register.

        MACRO
$label  Exp2Top $dest,$src,$cond,$s
        [ EIExp_pos = 0
$label    MOV$cond$s $dest,$src,LSL #32-EIExp_len
        |
$label    MOV$cond   $dest,$src,LSR #EIExp_pos
          MOV$cond$s $dest,$dest,LSL #32-EIExp_len
        ]
        MEND

;===========================================================================

; The following macros isolate the exponent fields from two standard sign/
; uncommon bit/exponent words, putting the first one at the top of a
; destination register. ExpDiff puts the difference at the top of another
; register and sets the condition codes on it, while ExpComp simply sets the
; condition codes on the difference.

        MACRO
$label  ExpComp $dest,$src1,$src2,$tmp
        ASSERT  $dest <> $src1
        ASSERT  $dest <> $src2
        ASSERT  $dest <> $tmp
        ASSERT  $tmp <> $src1
        ASSERT  $tmp <> $src2
        [ EIExp_pos = 0
$label    MOV     $dest,$src1,LSL #32-EIExp_len
          CMP     $dest,$src2,LSL #32-EIExp_len
        |
$label    MOV     $dest,$src1,LSR #EIExp_pos
          MOV     $dest,$dest,LSL #32-EIExp_len
          MOV     $tmp,$src2,LSR #EIExp_pos
          CMP     $dest,$tmp,LSL #32-EIExp_len
        ]
        MEND

        MACRO
$label  ExpDiff $diff,$dest,$src1,$src2
        ASSERT  $diff <> $dest
        ASSERT  $diff <> $src1
        ASSERT  $diff <> $src2
        ASSERT  $dest <> $src1
        ASSERT  $dest <> $src2
        [ EIExp_pos = 0
$label    MOV     $dest,$src1,LSL #32-EIExp_len
          SUBS    $diff,$dest,$src2,LSL #32-EIExp_len
        |
$label    MOV     $dest,$src1,LSR #EIExp_pos
          MOV     $dest,$dest,LSL #32-EIExp_len
          MOV     $diff,$src2,LSR #EIExp_pos
          SUBS    $diff,$dest,$diff,LSL #32-EIExp_len
        ]
        MEND

;===========================================================================

; The following macro performs the standard test for infinities or NaNs on
; an internal floating point number. It only works on legitimate internal
; precision numbers - i.e. it produces undefined results if the bit pattern
; in the internal precision number is an undefined one. The parameters are:
;   $res: On exit, the top bit of this register is set if the number is a
;         NaN or infinity, clear if it isn't;
;   $sue: Register holding sign, uncommon bit and exponent of number to be
;         tested; preserved on exit;
;   $mhi: Register containing high word of mantissa of number to be tested;
;         preserved on exit;
;   $mlo: Register containing low word of mantissa of number to be tested;
;         preserved on exit;
;
; In addition, the N flag is set on exit if the number is a NaN or infinity,
; clear if it isn't.
;
; The criterion used for a number to be a NaN or infinity is:
;
;   Uncommon bit = 1; and
;   Exponent top bit = 1; and
;   Exponent = MAX or units bit = 1.
;
; Whether the operand is in fact a NaN or an infinity is then determined by
; seeing whether the fraction is non-zero or zero.

        MACRO
$label  TNaNInf $res,$sue,$mhi
        ASSERT  $res <> $sue
        ASSERT  $res <> $mhi
$label  MOV     $res,$sue,LSL #32-(EIExp_pos+EIExp_len) ;Top bit of exponent
        CMN     $res,#1:SHL:(32-(EIExp_pos+EIExp_len))  ;Is exp. = MAX? If
        ANDCC   $res,$res,$mhi                          ; not, use units bit
        ANDS    $res,$res,$sue,LSL #31-Uncommon_pos     ;Use uncommon anyway
        MEND

;===========================================================================

; The following macro contains the standard code for denormalising a
; mantissa by a specified amount, producing guard, round and sticky bits in
; the process. The parameters are:
;   $mhi: Register containing mantissa high word; updated on exit;
;   $mlo: Register containing mantissa low word; updated on exit;
;   $grs: Register that will contain the guard bit (in bit 31), the round
;         bit (in bit 30) and the sticky bit (in whether bits 29:0 are zero
;         or non-zero) on exit;
;   $sh:  Register containing the shift amount; corrupt on exit;
;   $t1,$t2: Registers used as temporaries; corrupt on exit.
; $grs may be null to indicate that the guard, round and sticky information
; isn't wanted. $mlo can be null to indicate that we only need to
; denormalise a single word: in this case, $grs must be null.
;   Note that the $grs register may alternatively be interpreted as
; containing a round bit in bit 31 and a sticky bit in bits 30:0, in cases
; when there is no need for a guard bit. Also note that $sh may be the same
; register as either of $grs and $t2; otherwise, the registers must be
; distinct from each other.
;   Finally, note that branch instructions are used around a 4 instruction
; sequence and a 5 instruction sequence. This is because statistics show
; that larger shift amounts are less common than smaller ones in general:
; thus these instruction sequences are obeyed less than 50% of the time,
; which makes the code with branches slightly faster.

        MACRO
$label  Denorm  $mhi,$mlo,$grs,$sh,$t1,$t2
        ASSERT  $mhi <> $sh
        ASSERT  $mhi <> $t1
        ASSERT  $mhi <> $t2
        ASSERT  $sh <> $t1
        ASSERT  $t1 <> $t2
$label  MOV     $t1,$sh,LSR #5          ;Number of words to shift by
        BIC     $t2,$sh,$t1,LSL #5      ;Number of odd bits to shift by
        [ "$mlo" = ""
          ASSERT  "$grs" = ""
          CMP     $t1,#1                  ;At least one word?
          MOVLO   $mhi,$mhi,LSR $t2       ;Shift by odd bits if not
          MOVHS   $mhi,#0                 ;And clear out completely if so
        |
          ASSERT  $mlo <> $mhi
          ASSERT  $mlo <> $sh
          ASSERT  $mlo <> $t1
          ASSERT  $mlo <> $t2
          [ "$grs" = ""
            CMP     $t1,#1                  ;HI for 2+ words, EQ for 1, LO for 0
            RSBLS   $t1,$t2,#32             ;Shift by the number of odd bits
            MOVLS   $mlo,$mlo,LSR $t2
            ORRLS   $mlo,$mlo,$mhi,LSL $t1
            MOVLS   $mhi,$mhi,LSR $t2
            MOVEQ   $mlo,$mhi               ;Now do full words
            MOVHI   $mlo,#0
            MOVHS   $mhi,#0
          |
            ASSERT  $grs <> $mhi
            ASSERT  $grs <> $mlo
            ASSERT  $grs <> $t1
            ASSERT  $grs <> $t2
            CMP     $t1,#2                  ;CS/NE for 3+ words, CS/EQ for 2,
            TEQCC   $t1,#0                  ; CC/NE for 1 and CC/EQ for 0.
            RSB     $t1,$t2,#32             ;Shift by the number of odd bits
            MOV     $grs,$mlo,LSL $t1
            MOV     $mlo,$mlo,LSR $t2
            ORR     $mlo,$mlo,$mhi,LSL $t1
            MOV     $mhi,$mhi,LSR $t2
            BEQ     %f90                    ;Branch if no 32-bit shift
            ORRNE   $grs,$grs,$grs,LSL #2   ;Shift by 32 bits, accumulating
            ORRNE   $grs,$mlo,$grs,LSR #2   ; sticky bit
            MOVNE   $mlo,$mhi
            MOVNE   $mhi,#0
90
            BCC     %f99                    ;Branch if no 64-bit shift
            ORRCS   $grs,$grs,$mlo          ;Shift by 64 bits, accumulating
            ORRCS   $grs,$grs,$grs,LSL #2   ; sticky bit
            ORRCS   $grs,$mhi,$grs,LSR #2
            MOVCS   $mlo,#0
            MOVCS   $mhi,#0
99
          ]
        ]
        MEND

;===========================================================================

; Macro to separate a 32-bit value in a register into its two 16-bit halves.

        MACRO
$label  Split16 $resh,$resl,$src
        ASSERT  $resh <> $src
$label  MOV     $resh,$src,LSR #16
        BIC     $resl,$src,$resh,LSL #16
        MEND

;===========================================================================

; Macro to do a (16,16)x32 -> 64 multiplication. Done by breaking it up into
; four 16x16 multiplications and recombining the pieces. (N.B. The trick
; described in Knuth section 4.3.3 for reducing the four multiplications to
; three plus some additions and sign manipulations is not profitable at this
; size: it only becomes profitable when trying to synthesise a 64x64
; multiplication out of 32x32 multiplications.)
;   Also allows the flags to be set on the high word of the result and an
; optional addend to be added into the high word of the result: however,
; combining these does *not* result in the C flag being set correctly for
; the carry-out from the notional addition of the addend and the high word.
; Only the Z and N flags have meaningful values.
;   The operands are:
; $resh,$resl: Registers that will receive the 64-bit product;
; $op1h,$op1l: Registers containing the high and low 16 bits of the first
;              32-bit operand;
; $op2:        Register containing the second 32-bit operand;
; $add:        If present, register containing the addend;
; $s:          "S" to set the condition codes;
; $t1,$t2,$t3: Three temporary registers required during the calculation.
; The restrictions on which registers may be the same are complicated and
; are detailed in the ASSERT statements below.

        MACRO
$label  Mul64   $resh,$resl,$op1h,$op1l,$op2,$add,$s,$t1,$t2,$t3
        ASSERT  $resh <> $resl
        ASSERT  $resl <> $op1h
        ASSERT  $resl <> $t1
        ASSERT  $resl <> $t2
        ASSERT  $resl <> $t3
        ASSERT  $op1h <> $op1l
        ASSERT  $op1h <> $op2
        ASSERT  $op1h <> $t1
        ASSERT  $op1h <> $t2
        ASSERT  $op1h <> $t3
        ASSERT  $op1l <> $op2
        ASSERT  $op1l <> $t1
        ASSERT  $op1l <> $t2
        ASSERT  $op1l <> $t3
        ASSERT  $op2  <> $t1
        ASSERT  $t1   <> $t2
        ASSERT  $t1   <> $t3
        ASSERT  $t2   <> $t3
$label  Split16 $t1,$t2,$op2            ;t1 := op2h, t2 := op2l
        [ "$add" <> ""
          ASSERT  $add <> $op1h
          ASSERT  $add <> $op1l
          ASSERT  $add <> $op2
          ASSERT  $add <> $t1
          ASSERT  $add <> $t2
          MLA     $t3,$op1h,$t1,$add      ;t3 := op1h * op2h + add
        |
          MUL     $t3,$op1h,$t1           ;t3 := op1h * op2h
        ]
        MUL     $t1,$op1l,$t1           ;t1 := op1l * op2h
        MUL     $resl,$t2,$op1l         ;resl := op1l * op2l
        ADDS    $resl,$resl,$t1,LSL #16 ;Add op1l * op2h into (t3,resl)
        ADC     $t3,$t3,$t1,LSR #16
        MUL     $t2,$op1h,$t2           ;t2 := op1h * op2l
        ADDS    $resl,$resl,$t2,LSL #16 ;Add op1h * op2l into (t3,resl)
        ADC$s   $resh,$t3,$t2,LSR #16   ; to produce (resh,resl)
        MEND

;===========================================================================

; Macro to transfer the destination register of an instruction to a set of
; registers. Operands are:
; $type:     "FPASC" or "FPE";
; $dest:     The destination register list;
; $instr:    The instruction whose destination is to be transferred;
; $t:        A temporary.

        MACRO
$label  GetDst  $type,$dest,$instr,$t
        LCLA    Base
        LCLA    Offset
        ASSERT  ("$type" = "FPASC") :LOR: ("$type" = "FPE")
        [ ("$type" = "FPASC")
$label    TST     $instr,#4:SHL:Ds_pos          ;Check whether F0-3 or F4-7
          SFMEQFD F0,4,[Rsp]!                   ;Dump set of 4 registers -
          SFMNEFD F4,4,[Rsp]!                   ; faster than trying to get
                                                ; the correct register only
          AND     $t,$instr,#3:SHL:Ds_pos       ;Get position in dump
          ADD     $t,$t,$t,LSL #1               ;Convert to number of words
          BiShift ADD,$t,Rsp,$t,LSR #Ds_pos,LSL #2 ;Make address of register
          LDMIA   $t,$dest                      ; value, then get value
          ADD     Rsp,Rsp,#48                   ;Discard dumped registers
          ASSERT  Ds_mask = ((4+3):SHL:Ds_pos)
        |
$label    AND     $t,$instr,#Ds_mask
          [ :LNOT:FPE4WordsPerReg
            ADD     $t,$t,$t,LSL #1
            ASSERT  Ds_pos <= 27
          ]
Base      SETA            :BASE:FPE_Regs
          [ Base = 15
Offset      SETA            FPE_Regs-({PC}+8)
          |
Offset      SETA            :INDEX:FPE_Regs
          ]
          [ FPE4WordsPerReg
            BiShift ADD,$t,R$Base,$t,LSR #Ds_pos,LSL #4
          |
            BiShift ADD,$t,R$Base,$t,LSR #Ds_pos,LSL #2
          ]
          [ Offset <> 0
            ADD     $t,$t,#Offset
          ]
          LDMIA   $t,$dest
        ]
        MEND

;===========================================================================

; Macro to transfer the destination register of a non-FLT instruction from a
; set of registers. Operands are:
; $type:     "FPASC" or "FPE";
; $source:   The source register list;
; $instr:    The instruction whose destination is to be transferred;
; $t:        A temporary.
; $l:        If present, this produces a "long" form of the macro

        MACRO
$label  PutDst  $type,$source,$instr,$t,$l
        ASSERT  $t <> $instr
        LCLA    Base
        LCLA    Offset
        ASSERT  ("$type" = "FPASC") :LOR: ("$type" = "FPE")
        [ ("$type" = "FPASC")
          ALIGN
$label
          STMFD   Rsp!,$source
          AND     $t,$instr,#Ds_mask
10
          BiShift ADD,$t,PC,$t,LSR #Ds_pos,LSL #3
          [ "$l"=""
            MOV     LR,PC
            ADD     PC,$t,#($type._PutDstRoutines - (%b10+8))
          |
            ADD     $t,$t,#($type._PutDstRoutines - (%b10+8)):AND:&FF
            MOV     LR,PC
            ADD     PC,$t,#($type._PutDstRoutines - (%b10+8)):AND::NOT:&FF
          ]
        |
        ; "$type" = "FPE"
$label    AND     $t,$instr,#Ds_mask
          [ :LNOT:FPE4WordsPerReg
            ADD     $t,$t,$t,LSL #1
            ASSERT  Ds_pos <= 27
          ]
Base      SETA            :BASE:FPE_Regs
          [ Base = 15
Offset      SETA            FPE_Regs-({PC}+8)
          |
Offset      SETA            :INDEX:FPE_Regs
          ]
          [ FPE4WordsPerReg
            BiShift ADD,$t,R$Base,$t,LSR #Ds_pos,LSL #4
          |
            BiShift ADD,$t,R$Base,$t,LSR #Ds_pos,LSL #2
          ]
          [ Offset <> 0
            ADD     $t,$t,#Offset
          ]
          STMIA   $t,$source
        ]
        MEND

;===========================================================================

; Macro to transfer the destination register of a FLT instruction from a set
; of registers. Operands are:
; $type:     "FPASC" or "FPE";
; $source:   The source register list;
; $instr:    The instruction whose destination is to be transferred;
; $t:        A temporary.

        MACRO
$label  PutFDst $type,$source,$instr,$t
        ASSERT  $t <> $instr
        LCLA    Base
        LCLA    Offset
        ASSERT  ("$type" = "FPASC") :LOR: ("$type" = "FPE")
        [ ("$type" = "FPASC")
          ALIGN
$label
          STMFD   Rsp!,$source
          AND     $t,$instr,#S1_mask
10
          BiShift ADD,$t,PC,$t,LSR #S1_pos,LSL #3
          MOV     LR,PC
          ADD     PC,$t,#($type._PutDstRoutines - (%b10+8))
        |
        ; "$type" = "FPE"
$label    AND     $t,$instr,#S1_mask
          [ :LNOT:FPE4WordsPerReg
            ADD     $t,$t,$t,LSL #1
            ASSERT  S1_pos <= 27
          ]
Base      SETA            :BASE:FPE_Regs
          [ Base = 15
Offset      SETA            FPE_Regs-({PC}+8)
          |
Offset      SETA            :INDEX:FPE_Regs
          ]
          [ FPE4WordsPerReg
            BiShift ADD,$t,R$Base,$t,LSR #S1_pos,LSL #4
          |
            BiShift ADD,$t,R$Base,$t,LSR #S1_pos,LSL #2
          ]
          [ Offset <> 0
            ADD     $t,$t,#Offset
          ]
          STMIA   $t,$source
        ]
        MEND

;===========================================================================

; Macro to get the first source register of an instruction into three
; registers. Operands are:
; $type:     "FPASC" or "FPE";
; $dest:     The destination register list;
; $instr:    The instruction whose first source is to be transferred;
; $t:        A temporary.

        MACRO
$label  GetS1   $type,$dest,$instr,$t
        LCLA    Base
        LCLA    Offset
        ASSERT  ("$type" = "FPASC") :LOR: ("$type" = "FPE")
        [ ("$type" = "FPASC")
$label    TST     $instr,#4:SHL:S1_pos          ;Check whether F0-3 or F4-7
          SFMEQFD F0,4,[Rsp]!                   ;Dump set of 4 registers -
          SFMNEFD F4,4,[Rsp]!                   ; faster than trying to get
                                                ; the correct register only
          AND     $t,$instr,#3:SHL:S1_pos       ;Get position in dump
          ADD     $t,$t,$t,LSL #1               ;Convert to number of words
          BiShift ADD,$t,Rsp,$t,LSR #S1_pos,LSL #2 ;Make address of register
          LDMIA   $t,$dest                      ; value, then get value
          ADD     Rsp,Rsp,#48                   ;Discard dumped registers
          ASSERT  S1_mask = ((4+3):SHL:S1_pos)
        |
$label    AND     $t,$instr,#S1_mask
          [ :LNOT:FPE4WordsPerReg
            ADD     $t,$t,$t,LSL #1
            ASSERT  S1_pos <= 27
          ]
Base      SETA            :BASE:FPE_Regs
          [ Base = 15
Offset      SETA            FPE_Regs-({PC}+8)
          |
Offset      SETA            :INDEX:FPE_Regs
          ]
          [ FPE4WordsPerReg
            BiShift ADD,$t,R$Base,$t,LSR #S1_pos,LSL #4
          |
            BiShift ADD,$t,R$Base,$t,LSR #S1_pos,LSL #2
          ]
          [ Offset <> 0
            ADD     $t,$t,#Offset
          ]
          LDMIA   $t,$dest
        ]
        MEND

;===========================================================================

; Macro to get the second source register or constant of an instruction into
; three registers. Operands are:
; $type:     "FPASC" or "FPE";
; $dest:     The destination register list;
; $instr:    The instruction whose second source is to be transferred;
; $t,$t2:    Temporaries.

        MACRO
$label  GetS2   $type,$dest,$instr,$t,$t2
        LCLA    Base
        LCLA    Offset
        ASSERT  ("$type" = "FPASC") :LOR: ("$type" = "FPE")
        ASSERT  S2_Ibit = 1:SHL:(S2_pos+3)
        ASSERT  S2_pos = 0
        ASSERT  $t <> $t2
$label  MOVS    $t2,$instr,LSL #29      ;C:=S2_Ibit, N:=F4-7, not F0-3
                                        ;$t2 := left-al. reg/const no.
        [ ("$type" = "FPASC")
Base      SETA            :BASE:$type.ConstTable
          [ Base = 15
Offset      SETA            $type.ConstTable-({PC}+8)
          |
Offset      SETA            :INDEX:$type.ConstTable
          ]
          ADDCS   $t,R$Base,$t2,LSR #25         ;Address the constant if it
          [ Offset <> 0
            ADDCS   $t,$t,#Offset               ; is one
          ]
          BCS     %f10
          SFMPLFD F0,4,[Rsp]!                   ;Dump set of 4 registers -
          SFMMIFD F4,4,[Rsp]!                   ; faster than trying to get
                                                ; the correct register only
          BIC     $t2,$t2,#TopBit               ;Get position within set
          ADD     $t,Rsp,$t2,LSR #27            ;Make address of register
          ADD     $t,$t,$t2,LSR #26             ; value
10
          LDMIA   $t,$dest                      ;Get reg. value or constant
          ADDCC   Rsp,Rsp,#48                   ;If reg, discard dumped regs
        |
Base      SETA            :BASE:FPEConstTable
          [ Base = 15
Offset      SETA            FPEConstTable-({PC}+8)
          |
Offset      SETA            :INDEX:FPEConstTable
          ]
          ADDCS   $t,R$Base,$t2,LSR #25
          [ Offset <> 0
            ADDCS   $t,$t,#Offset
          ]
Base      SETA            :BASE:FPE_Regs
          [ Base = 15
Offset      SETA            FPE_Regs-({PC}+8)
          |
Offset      SETA            :INDEX:FPE_Regs
          ]
          [ FPE4WordsPerReg
            ADDCC   $t,R$Base,$t2,LSR #25
          |
            ADDCC   $t,R$Base,$t2,LSR #27
            ADDCC   $t,$t,$t2,LSR #26
          ]
          [ Offset <> 0
            ADDCC   $t,$t,#Offset
          ]
          LDMIA   $t,$dest
        ]
        MEND

;===========================================================================

; Macro to get both source operands of an instruction into two groups of
; three registers. Operands are:
; $type:     "FPASC" or "FPE";
; $dest1:    The destination register list for the first operand;
; $dest2:    The destination register list for the second operand;
; $instr:    The instruction whose second source is to be transferred;
; $t, $t2:   Temporaries.

        MACRO
$label  GetS12  $type,$dest1,$dest2,$instr,$t,$t2
        LCLA    Base
        LCLA    Offset
        ASSERT  ("$type" = "FPASC") :LOR: ("$type" = "FPE")
        [ ("$type" = "FPASC")
          SFMFD   F4,4,[Rsp]!                   ;Dump all registers
          SFMFD   F0,4,[Rsp]!
          AND     $t,$instr,#S1_mask            ;Get S1 position in dump
          ADD     $t,$t,$t,LSL #1               ;Convert to number of words
          BiShift ADD,$t,Rsp,$t,LSR #S1_pos,LSL #2 ;Make address of register
          LDMIA   $t,$dest1                     ; value, then get value
          ASSERT  S2_Ibit = 1:SHL:(S2_pos+3)
          ASSERT  S2_pos = 0
          MOVS    $t2,$instr,LSL #29    ;C:=S2_Ibit, N:=F4-7, not F0-3
                                        ;$t2 := left-al. reg/const no.
Base      SETA            :BASE:$type.ConstTable
          [ Base = 15
Offset      SETA            $type.ConstTable-({PC}+8)
          |
Offset      SETA            :INDEX:$type.ConstTable
          ]
          ADDCS   $t,R$Base,$t2,LSR #25         ;Address the constant if it
          [ Offset <> 0
            ADDCS   $t,$t,#Offset               ; is one
          ]
          ADDCC   $t,Rsp,$t2,LSR #27            ;Otherwise address the register
          ADDCC   $t,$t,$t2,LSR #26             ; value
          LDMIA   $t,$dest2
          ADD     Rsp,Rsp,#96                   ;Discard the register dump
        |
$label    GetS1   $type,$dest1,$instr,$t
          GetS2   $type,$dest2,$instr,$t,$t2
        ]
        MEND

;===========================================================================

; The standard macro to return to the caller. Note that care has to be taken
; here never to leave Rsp pointing above any useful stack contents, in case
; of a badly-timed interrupt.

        MACRO
$label  Return
        [ {CONFIG} = 26
$label    MOV     Rsp,Rfp               ;Discard now-spurious stack contents
        ]
        [ {CONFIG} = 32
$label    LDMDB   Rfp,{Rtmp,Rtmp2}      ;Recover the SPSR and CPSR
          MSR     CPSR_all,Rtmp2        ; (restoring the CPSR re-disables
          MSR     SPSR_all,Rtmp         ; interrupts, so the SPSR isn't ever
                                        ; valid when interrupts are enabled)
          MOV     Rsp,Rfp               ;Discard now-spurious stack contents
        ]
        LDMIA   Rfp,{R0-R14}^           ;Coding rules: cannot use write-back
        NOP                             ; and must protect next instruction
        ADD     Rsp,Rsp,#15*4           ;Do the write-back
        LDMFD   Rsp!,{PC}^              ;Restore R13_svr/R13_und, PC and PSR
        MEND

;===========================================================================

; Macro to get the processor mode for the caller, with the 26/32 bit
; distinction removed. The flags are set on the result value, so Z indicates
; whether we're in user mode.

        MACRO
$label  GetMode $res
        [ {CONFIG}=32
$label    LDR     $res,[Rfp,#-8]                ;Recover original SPSR value
          ANDS    $res,$res,#Mode_mask-Mode_32not26
          ASSERT  (Mode_USR26:AND::NOT:Mode_32not26) = 0
          ASSERT  (Mode_USR32:AND::NOT:Mode_32not26) = 0
        ]
        [ {CONFIG}=26
$label    LDR     $res,[Rfp,#15*4]              ;Recover original LR value
          ANDS    $res,$res,#Mode_mask
          ASSERT  Mode_USR26 = 0
        ]
        MEND

;===========================================================================

; Macro to insert the right amount of padding between a table-driven branch
; instruction (e.g. ADD PC,PC,reg,LSL #2) and the in-line branch table that
; follows it. Made into a macro for documentation purposes, and also just in
; case the user-visible pipeline depth has to change at some point in the
; future.

        MACRO
        BranchTablePad
        DCD     0               ;Padding before branch table
        MEND

;===========================================================================

; Macro to re-enable interrupts if "EnableInterrupts" is {TRUE}. Only
; argument is a temporary register.

        MACRO
$label  InterruptEnable $t
        [ EnableInterrupts
          [ {CONFIG} = 32
$label      MRS     $t,CPSR_all
            BIC     $t,$t,#I_bit
            MSR     CPSR_all,$t
          ]
          [ {CONFIG} = 26
$label      MOV     $t,PC
            BIC     $t,$t,#I_bit
            TEQP    PC,$t
          ]
          NOP
        ]
        MEND

;===========================================================================

; Macro to re-disable interrupts if "EnableInterrupts" is {TRUE}. Only
; argument is a temporary register.

        MACRO
$label  InterruptDisable $t
        [ EnableInterrupts
          [ {CONFIG} = 32
$label      MRS     $t,CPSR_all
            ORR     $t,$t,#I_bit
            MSR     CPSR_all,$t
          ]
          [ {CONFIG} = 26
$label      MOV     $t,PC
            ORR     $t,$t,#I_bit
            TEQP    PC,$t
          ]
          NOP
        ]
        MEND

;===========================================================================

; Macro to do the standard "enter recursive floating point code" processing.
; The operands are:
; $freeregs: Number of floating point registers to free up, in the range 1
;            to 8;
; $extra:    Number of bytes of extra space to be left on the stack above
;            the register dump;
; $addr:     Register to contain address of extra space - also used to hold
;            temporary values during macro, so must be present even if no
;            extra space is wanted;
; $nofpsr:   If this operand is non-null, it inhibits the FPSR changes
;            described below.
; Rsp and Rfpsr are also operands.
;   This code is written quite carefully, to avoid the use of floating point
; instructions the FPE won't like (e.g. those which use mode-dependent
; registers). It also disables interrupts (if they were ever enabled) and
; leaves a record of what floating point registers are on the stack, to make
; certain core_abort works. Finally, it clears out the exception enable bits
; and cumulative flags from the real FPSR, since exceptions in recursive
; code must not go out to the user trap handlers. Note that Rfpsr holds the
; real FPSR value and will be written back to the real FPSR before control
; is returned to the user, either via a trap handler or by normal return.

        MACRO
$label  EnterRecursive $freeregs,$extra,$addr,$nofpsr
        ASSERT  ($freeregs) <= 8
        ASSERT  ($freeregs) >= 1
$label  SUB     Rsp,Rsp,#($freeregs)*12+4+($extra)
        MOV     $addr,Rfpsr,LSL #8
        ORR     $addr,$addr,#(1:SHL:($freeregs))-1
        STR     $addr,[Rsp]
        InterruptDisable $addr
        [ "$nofpsr" = ""
          BIC     $addr,Rfpsr,#IOE_bit+DZE_bit+OFE_bit+UFE_bit+IXE_bit
          BIC     $addr,$addr,#IOC_bit+DZC_bit+OFC_bit+UFC_bit+IXC_bit
          WFS     $addr
        ]
        ADD     $addr,Rsp,#($freeregs)*12+4
        [ ($freeregs) <= 4
          SFM     F0,($freeregs),[$addr,#-12*($freeregs)]
        |
          SFM     F0,4,[$addr,#-12*($freeregs)]
          SFM     F4,($freeregs)-4,[$addr,#-12*($freeregs)+48]
        ]
        MEND

;===========================================================================

; Macro to do the standard "exit recursive floating point code" processing.
; The operands are:
; $freeregs: Number of floating point registers to recover from the stack,
;            in the range 1 to 8;
; $extra:    Number of bytes of extra space to recover from the stack;
; $t:        A temporary register;
; $fpres:    Floating point register that contains the floating point result
;            - null if no such result;
; $result:   Register list to take 3 word floating point result - null if
;            no such result.
; Rsp is also an operand.

        MACRO
$label  ExitRecursive $freeregs,$extra,$t,$fpres,$result
        ASSERT  ($freeregs) <= 8
        ASSERT  ($freeregs) >= 1
        ADD     $t,Rsp,#($freeregs)*12+4
        [ "$fpres" <> ""
          ASSERT  ($extra) >= 12
          SFM     $fpres,1,[$t]
          LDMIA   $t,$result
        ]
        [ ($freeregs) <= 4
          LFM     F0,($freeregs),[$t,#-12*($freeregs)]
        |
          LFM     F0,4,[$t,#-12*($freeregs)]
          LFM     F4,($freeregs)-4,[$t,#-12*($freeregs)+48]
        ]
        ADD     Rsp,Rsp,#($freeregs)*12+4+($extra)
        InterruptEnable $t
        MEND

;===========================================================================

; Macro to determine whether an exception was precise or imprecise. Implicit
; operands are Rfpsr (for the SO bit and to determine whether it is a
; hardware or software context) and Rins (to determine what type of
; instruction this is). Explicit operands are:
;   $dst: Set to zero if precise, non-zero if imprecise;
;   $t:   A temporary register;
;   $tbl_fpa: The address of a bit table used to determine whether FPA
;         instructions are capable of producing imprecise exceptions.
;
; The full set of conditions for the operation to be imprecise are:
;
;   * The FPA hardware is being used;
;   * The SO bit is clear in the FPSR;
;   * The instruction is a CPDO or CPRT;
;   * The instruction is capable of delivering an imprecise exception (e.g.
;     not a purely software-implemented instruction, a FIX or a compare);
;
; Testing this last condition is complicated: it is done via the bit table
; mentioned above.
;
; The optimisation that the whole test is unnecessary for FPE-only code is
; not performed here: it is instead done in the main assembly source and
; this macro is never used.

        MACRO
$label  TestImp $dst,$t,$tbl_fpa
        ASSERT  $dst <> Rins
        ASSERT  $dst <> Rfpsr
        ASSERT  $t   <> Rins
        ASSERT  $t   <> Rfpsr
        ASSERT  $t   <> $dst
$label
        ; Address the table
        ADR     $t,$tbl_fpa
        ; Then look up correct table entry
        AND     $dst,Rins,#RTnotDO_bit
        BiShift LDR,$dst,$t,$dst,LSR #RTnotDO_pos,LSL #2
        TST     Rins,#Op2_mask
        MOVNE   $dst,$dst,LSR #16
        AND     $t,Rins,#Op1_mask
        MOV     $t,$t,LSR #Op1_pos
        ; Now incorporate other tests
        MOV     $dst,$dst,LSR $t                ;Bit0 is result so far
        AND     $dst,$dst,Rfpsr,LSR #31         ;Isolate bit0 and AND
                                                ; with (hardware in use)
        BIC     $dst,$dst,Rfpsr,LSR #SO_pos     ;AND with (SO bit clear)
        AND     $dst,$dst,Rins,LSR #RTDOnotDT_pos ;AND with (CPRT or CPDO)
        MEND

;===========================================================================

; Macros used for byte arrays.

                GBLA    ByteArrayCount
ByteArrayCount  SETA    0

        MACRO
$label  BytesStart
        ALIGN
$label
ByteArray_$ByteArrayCount
        MEND

        MACRO
$label  BytesEnd
        ALIGN
$label
ByteArrayEnd_$ByteArrayCount
ByteArrayCount  SETA    ByteArrayCount+1
        MEND

;===========================================================================

        END
