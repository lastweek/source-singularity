;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

; fpe.s
;
; Copyright (C) Advanced RISC Machines Limited, 1994. All rights reserved.
;
; RCS Revision: 1 
; Checkin Date: 2007/06/29 02:59:16 
; Revising Author

        GET     defaults.asm
        GET     callcode.asm
        GBLL    FPEWanted
        GBLL    FPASCWanted
        GBLL    EnableInterrupts
        GBLA    CoreDebugging

FPEWanted       SETL    {FALSE}
FPASCWanted     SETL    {FALSE}
EnableInterrupts        SETL    {FALSE}
CoreDebugging   SETA    0


;==============================================================================

; 
; Allow some control over the code/speed of code produced.
; 0 = fastest -> 2 = smallest (overall)
; 

        GBLA    CodeSize
CodeSize        SETA    0

        MACRO
        ImportCodeSize $name
        [ CodeSize <> 0
        IMPORT  $name
        ]
        MEND

        MACRO
        ExportCodeSize $name
        [ CodeSize <> 0
        EXPORT  $name
        ]
        MEND

;==============================================================================

        MACRO
$label  CDebug4 $level,$message,$reg1,$reg2,$reg3,$reg4
        MEND
        MACRO
$label  CDebug3 $level,$message,$reg1,$reg2,$reg3
        MEND
        MACRO
$label  CDebug2 $level,$message,$reg1,$reg2
        MEND
        MACRO
$label  CDebug1 $level,$message,$reg1
        MEND
        MACRO
$label  CDebug0 $level,$message
        MEND

; File for setting up THUMB macros for entry and exit from the THUMB
; versions of the functions.

        GBLA    V_N

        [ :DEF: thumb

        MACRO
$label  VEnter_16               ; Like VEnter, but declare __16$label as the
        CODE16                  ; THUMB entry point
__16$label
        BX      pc
        CODE32
V_N     SETA    V_N+1
        LCLS    f_lab
f_lab   SETS    "|":CC:"$F":CC::STR:V_N:CC:"|"
        KEEP    $f_lab
$f_lab
$label  STMFD   r13!,veneer_s   ; ARM is the declared entry point
        MEND

        MACRO
$label  VEnter                  ; Declare the THUMB entry point as the main
        CODE16                  ; entry point
$label  BX      pc
        CODE32
V_N     SETA    V_N+1
        LCLS    f_lab
f_lab   SETS    "|":CC:"$F":CC::STR:V_N:CC:"|"
        KEEP    $f_lab
$f_lab
__32$label                      ; Declare a __32$label entry point for ARM
        STMFD   r13!,veneer_s
        MEND

        MACRO
$label  VReturn $cc
$label  LDM$cc.FD r13!,veneer_s
        BX$cc   lr
        MEND

        MACRO
$label  VPull $cc
$label  LDM$cc.FD r13!,veneer_s
        MEND

        MACRO
$label  ReturnToLR $cc
$label  BX$cc   lr
        MEND

        MACRO
$label  ReturnToLR_flg $cc
$label  BX$cc   lr
        MEND

        MACRO
$label  ReturnToStack $cc
$label  LDM$cc.FD sp!,{lr}
        BX$cc   lr
        MEND

        MACRO
$label  PullFromStack $cc
$label  LDM$cc.FD sp!,{lr}
        MEND

        MACRO
$label  EnterWithLR_16
        CODE16
__16$label
        BX      pc
        CODE32
V_N     SETA    V_N+1
        LCLS    f_lab
f_lab   SETS    "|":CC:"$F":CC::STR:V_N:CC:"|"
        KEEP    $f_lab
$f_lab
$label
        MEND

        MACRO
$label  EnterWithStack_16
        CODE16
__16$label
        BX      pc
        CODE32
V_N     SETA    V_N+1
        LCLS    f_lab
f_lab   SETS    "|":CC:"$F":CC::STR:V_N:CC:"|"
        KEEP    $f_lab
$f_lab
$label  STMFD   sp!,{lr}
        MEND

        MACRO
$label  EnterWithLR
        CODE16
$label  BX      pc
        CODE32
V_N     SETA    V_N+1
        LCLS    f_lab
f_lab   SETS    "|":CC:"$F":CC::STR:V_N:CC:"|"
        KEEP    $f_lab
$f_lab
__32$label
        MEND

        MACRO
$label  EnterWithStack
        CODE16
$label  BX      pc
        CODE32
V_N     SETA    V_N+1
        LCLS    f_lab
f_lab   SETS    "|":CC:"$F":CC::STR:V_N:CC:"|"
        KEEP    $f_lab
$f_lab
__32$label
        STMFD   sp!,{lr}
        MEND
        
        MACRO
        Export $name
        EXPORT  $name
        EXPORT  __16$name
        MEND

        MACRO
        Export_32 $name
        EXPORT  __32$name
        EXPORT  $name
        MEND

        MACRO
        Import_32 $name
        IMPORT __32$name
        MEND

        MACRO
$label  B_32 $name
$label  B       __32$name
        MEND

        |

;ARM 32 and 26-bit mode

        MACRO
$label  VEnter_16
$label  STMFD   r13!,veneer_s
        MEND

        MACRO
$label  VEnter
$label  STMFD   r13!,veneer_s
        MEND

        MACRO
$label  VReturn $cc
$label  [ Interworking :LOR: Thumbing
        LDM$cc.FD r13!,veneer_s
        BX$cc   lr
        |
        [ {CONFIG} = 32 
        LDM$cc.FD r13!,veneer_l
        ]
        [ {CONFIG} = 26
        LDM$cc.FD r13!,veneer_l^
        ]
        ]
        MEND    

        MACRO
$label  VPull $cc
$label  LDM$cc.FD r13!,veneer_s
        MEND

        MACRO
$label  ReturnToLR $cc
$label  [ Interworking :LOR: Thumbing
        BX$cc   lr
        |
        [ {CONFIG} = 32
        MOV$cc  pc,lr
        ]
        [ {CONFIG} = 26
        MOV$cc.S pc,lr
        ]
        ]
        MEND

        MACRO
$label  ReturnToLR_flg $cc
$label  [ Interworking :LOR: Thumbing
        BX$cc   lr
        |
        MOV$cc  pc,lr
        ]
        MEND

        MACRO
$label  ReturnToStack $cc
$label  [ Interworking :LOR: Thumbing
        LDM$cc.FD sp!,{lr}
        BX$cc    lr
        |
        [ {CONFIG} = 32
        LDM$cc.FD sp!,{pc}
        ]
        [ {CONFIG} = 26
        LDM$cc.FD sp!,{pc}^
        ]
        ]
        MEND

        MACRO
$label  PullFromStack $cc
$label  LDM$cc.FD sp!,{lr}
        MEND

        MACRO
$label  EnterWithLR_16
$label
        MEND

        MACRO
$label  EnterWithStack_16
$label  STMFD   sp!,{lr}
        MEND

        MACRO
$label  EnterWithLR
$label
        MEND

        MACRO
$label  EnterWithStack
$label  STMFD   sp!,{lr}
        MEND

        MACRO
        Export $name
        EXPORT  $name
        MEND

        MACRO
        Export_32 $name
        EXPORT  $name
        MEND

        MACRO
        Import_32 $name
        IMPORT $name
        MEND

        MACRO
$label  B_32 $name
$label  B       $name
        MEND

        ]

        MACRO
        CodeArea $name
;; $name will be a name for the area. However for a release we'll use
;; C$$code instead
        [ Interworking
	AREA   |.text|, CODE, READONLY
        |
	AREA   |.text|, CODE, READONLY
        ]
        MEND

        GET     regnames.asm
        GET     armdefs.asm
        GET     fpadefs.asm
        GET     macros.asm

sp      RN      R13
lr      RN      R14
pc      RN      R15

dOP1h   RN      R1      ;Double OP1 hi-reg ("First word") - sign,expn,etc.
dOP1l   RN      R0      ;Double OP1 lo-reg ("Second word")
dOPh    RN      R1      ;Double OP hi-reg (unary ops)
dOPl    RN      R0      ;Double OP lo-reg
dOP2h   RN      R3      ;Double OP2 hi-reg ("First word")
dOP2l   RN      R2      ;Double OP2 lo-reg ("Second word")

fOP1    RN      R0      ;Float OP1
fOP     RN      R0      ;Float OP for unary ops
fOP2    RN      R1      ;Float OP2

utmp1   RN      R2      ;Temporary register fo unary operations
utmp2   RN      R3      ;    "

ip      RN      R12
tmp     RN      R12     ;A temporary register

SignBit         EQU     &80000000
fSignalBit      EQU     &00400000
dSignalBit      EQU     &00080000
w_oSignBit      EQU     &7fffffff
w_ofSignalBit    EQU     &ffbfffff
w_odSignalBit    EQU     &fff7ffff
Internal_mask   EQU     &00000000
Single_pos      EQU     0
Double_pos      EQU     1
Single_mask     EQU     1:SHL:Single_pos
Double_mask     EQU     1:SHL:Double_pos
Reverse         EQU     0x4     ; Used to signal a reverse divide

;;Error flags - an extension to the normal internal format

Error_pos       EQU     29
Error_bit       EQU     1:SHL:Error_pos

Except_len      EQU     5
Except_pos      EQU     Error_pos-Except_len

        ASSERT  IOC_pos < DZC_pos
        ASSERT  DZC_pos < OFC_pos
        ASSERT  OFC_pos < UFC_pos
        ASSERT  UFC_pos < IXC_pos
FPExceptC_pos   EQU     IOC_pos
        ASSERT  IOE_pos < DZE_pos
        ASSERT  DZE_pos < OFE_pos
        ASSERT  OFE_pos < UFE_pos
        ASSERT  UFE_pos < IXE_pos
FPExceptE_pos   EQU     IOE_pos


; Following fields are used to identify the originator function and the return type so that the
; error handler can return the correct value.

;;
;;  All fields and values must agree with C headers and programs.
;;
;;  r12 (defined as ip above) is used to pass information about the operation being performed
;;  to the exception handler.  The bit fields are defined as follows.
;;
;;   31                             0
;;  +--------------------------------+
;;  |                                |
;;  +--------------------------------+
;;
;;  Bits   Meaning
;;  ~~~~   ~~~~~~~
;;  31     unused
;;  30     Uncommon (possible exceptional case -- requires more checking)
;;  29     Error (exceptional case)
;;  28:25  unused
;;  24:20  Operation code (must agree with enumerated type in fpraise.c)
;;  19:5   unused
;;   4     Exception cause: Inexact   (must agree with float.h)
;;   3     Exception cause: Underflow
;;   2     Exception cause: Overflow
;;   1     Exception cause: Zero Divide
;;   0     Exception cause: Invalid Operation
;;


;;
;;  Operation code defines.  These must match with the FP_CODE enumerated
;;  type in fpraise.c.
;;
Fn_pos          EQU     20               ;; Function (operation) code position
Fn_mask         EQU     31 << Fn_pos     ;; Mask for the field

_FpAddD         EQU     ( 0 << Fn_pos)   ;; Add Double
_FpAddS         EQU     ( 1 << Fn_pos)   ;; Add Single
_FpSubD         EQU     ( 2 << Fn_pos)   ;; Subtract Double
_FpSubS         EQU     ( 3 << Fn_pos)   ;; Subtract Single
_FpCmpD         EQU     ( 4 << Fn_pos)   ;; Compare Double
_FpCmpS         EQU     ( 5 << Fn_pos)   ;; Compare Single
_FpDivD         EQU     ( 6 << Fn_pos)   ;; Divide Double
_FpDivS         EQU     ( 7 << Fn_pos)   ;; Divide Single
_FpDToI         EQU     ( 8 << Fn_pos)   ;; Convert Double To int
_FpDToI64       EQU     ( 9 << Fn_pos)   ;; Convert Double To __int64
_FpDToS         EQU     (10 << Fn_pos)   ;; Convert Double To Single
_FpDToU         EQU     (11 << Fn_pos)   ;; Convert Double To unsigned int
_FpDToU64       EQU     (12 << Fn_pos)   ;; Convert Double To unsigned __int64
_FpIToS         EQU     (13 << Fn_pos)   ;; Convert int To Single
_FpMulD         EQU     (14 << Fn_pos)   ;; Multiply Double
_FpMulS         EQU     (15 << Fn_pos)   ;; Multiply Single
_FpSToD         EQU     (16 << Fn_pos)   ;; Convert Single To Double
_FpSToI         EQU     (17 << Fn_pos)   ;; Convert Single To int
_FpSToI64       EQU     (18 << Fn_pos)   ;; Convert Single To __int64
_FpSToU         EQU     (19 << Fn_pos)   ;; Convert Single To unsigned int
_FpSToU64       EQU     (20 << Fn_pos)   ;; Convert Single To unsigned __int64
_FpUToS         EQU     (21 << Fn_pos)   ;; Convert unsigned int To Single
_FpI64ToD       EQU     (22 << Fn_pos)   ;; Convert __int64 To Double
_FpI64ToS       EQU     (23 << Fn_pos)   ;; Convert __int64 To Single
_FpU64ToD       EQU     (24 << Fn_pos)   ;; Convert unsigned __int64 To Double
_FpU64ToS       EQU     (25 << Fn_pos)   ;; Convert unsigned __int64 To Single
_FpRndD         EQU     (26 << Fn_pos)   ;; Round to double integer


;; FP Exception Causes (must agree with fpraise.c FPExInfo)
;; Note that this is modelled after the ARM 7500FE FPSR Cumulative exception
;; flags byte.  The semantics here are slightly different.  If a bit is set
;; here, it means that the corresponding exception occurred during the current
;; FP operation.  If a bit is clear, it means that the corresponding exception
;; did not occur during the current FP operation.  The bits are set regardless
;; of which exceptions are enabled, etc.  Raising exceptions, checking enabled
;; exceptions, and updating status and cause bits is done in fpraise.c which
;; maintains the "true" FPSCR.
INX_bit         EQU     (1 << 4)      ;; Inexact
UNF_bit         EQU     (1 << 3)      ;; Underflow
OVF_bit         EQU     (1 << 2)      ;; Overflow
DVZ_bit         EQU     (1 << 1)      ;; Zero Divide
IVO_bit         EQU     (1 << 0)      ;; Invalid Operation
FPECause_mask   EQU     (INX_bit :OR: \
                         UNF_bit :OR: \
                         OVF_bit :OR: \
                         DVZ_bit :OR: \
                         IVO_bit )


INX_bits         EQU     (INX_bit)
UNF_bits         EQU     (UNF_bit :OR: INX_bit)
OVF_bits         EQU     (OVF_bit :OR: INX_bit)
DVZ_bits         EQU     (DVZ_bit)
IVO_bits         EQU     (IVO_bit)


;; FP compare values from fpieee.h _FPIEEE_COMPARE_RESULT
;; These are used for the exception handler.
_FpCompareEqual      EQU   0
_FpCompareGreater    EQU   1
_FpCompareLess       EQU   2
_FpCompareUnordered  EQU   3



Double_bit      EQU     ((1 << 18) :AND:0)         ;; RDCFix: Get rid of this and fix what it breaks.
LongLong_bit    EQU     ((1 << 18) :AND:0)         ;; RDCFix: Get rid of this and fix what it breaks.

EDOM            EQU     1                          ;; RDCFix: Need this?
ERANGE          EQU     2                          ;; RDCFix: Need this?
ESIGNUM         EQU     3                          ;; RDCFix: Need this?

veneer_s        RLIST   {r4-r9,r11,lr}
veneer_l        RLIST   {r4-r9,r11,pc}


;; Macro to do a load immediate of an arbitrary whole word.
    MACRO
    LWI $cc, $reg, $imm
    MOV$cc $reg, #(($imm) :AND: 0x000000FF)
    ORR$cc $reg, $reg, #(($imm) :AND: 0x0000FF00)
    ORR$cc $reg, $reg, #(($imm) :AND: 0x00FF0000)
    ORR$cc $reg, $reg, #(($imm) :AND: 0xFF000000)
    MEND





        END
