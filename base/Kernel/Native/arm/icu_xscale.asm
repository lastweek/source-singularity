;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity ARM Bootstrap
;;;
;;; XScale 81348 ICU support routines
;;;

;;; Definitions taken from:
;;;
;;;  Chapter 10, Intel 81348 I/O Processor, September 2006, O/N: 315036-001US
;;;
;;; # Name  CRm     CRn
;;; INTBASE 2       0
;;; INTSIZE 2       2
;;; IINTVEC 2       3
;;; FINTVEC 2       4
;;; IPIPNDR 2       8
;;;
;;; INTPND0 3       0
;;; INTPND1 3       1
;;; INTPND2 3       2
;;; INTPND3 3       3
;;;
;;; INTCTL0 4       0
;;; INTCTL1 4       1
;;; INTCTL2 4       2
;;; INTCTL3 4       3
;;;
;;; INTSTR0 5       0
;;; INTSTR1 5       1
;;; INTSTR2 5       2
;;; INTSTR3 5       3
;;;
;;; IINTSRC0 6       0
;;; IINTSRC1 6       1
;;; IINTSRC2 6       2
;;; IINTSRC3 6       3
;;;
;;; FINTSRC0 7       0
;;; FINTSRC1 7       1
;;; FINTSRC2 7       2
;;; FINTSRC3 7       3
;;;
;;; IPR0     8       0
;;; IPR1     8       1
;;; IPR2     8       2
;;; IPR3     8       3
;;; IPR4     8       4
;;; IPR5     8       5
;;; IPR6     8       6
;;; IPR7     8       7
;;;
;;; MRC = coprocessor transfer to ARM register
;;; mrc <page>, <opcode_1>, <Rd>, <CRn>, <CRm>, <Opcode_2>
;;;
;;; MCR = ARM register to coprocessor transfer
;;; mcr <page>, <opcode_1>, <Rd>, <CRn>, <CRm>, <Opcode_2>
;;;

        CODE32

        AREA   |.text|, CODE, ARM

        ;;; Register operations for INTBASE ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTBASE@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTBASE@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c0, c2, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTBASE@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTBASE@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c0, c2, 0
        bx      lr
        ENDP

        ;;; Register operations for INTSIZE ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTSIZE@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTSIZE@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c2, c2, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTSIZE@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTSIZE@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c2, c2, 0
        bx      lr
        ENDP

        ;;; Register operations for IINTVEC ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIINTVEC@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIINTVEC@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c3, c2, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIINTVEC@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIINTVEC@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c3, c2, 0
        bx      lr
        ENDP

        ;;; Register operations for FINTVEC ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadFINTVEC@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadFINTVEC@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c4, c2, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteFINTVEC@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteFINTVEC@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c4, c2, 0
        bx      lr
        ENDP

        ;;; Register operations for IPIPNDR ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIPIPNDR@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIPIPNDR@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c8, c2, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIPIPNDR@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIPIPNDR@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c8, c2, 0
        bx      lr
        ENDP

        ;;; Register operations for INTPND0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTPND0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTPND0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c0, c3, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTPND0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTPND0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c0, c3, 0
        bx      lr
        ENDP

        ;;; Register operations for INTPND1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTPND1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTPND1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c1, c3, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTPND1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTPND1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c1, c3, 0
        bx      lr
        ENDP

        ;;; Register operations for INTPND2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTPND2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTPND2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c2, c3, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTPND2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTPND2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c2, c3, 0
        bx      lr
        ENDP

        ;;; Register operations for INTPND3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTPND3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTPND3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c3, c3, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTPND3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTPND3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c3, c3, 0
        bx      lr
        ENDP

        ;;; Register operations for INTCTL0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTCTL0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTCTL0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c0, c4, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTCTL0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTCTL0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c0, c4, 0
        bx      lr
        ENDP

        ;;; Register operations for INTCTL1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTCTL1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTCTL1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c1, c4, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTCTL1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTCTL1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c1, c4, 0
        bx      lr
        ENDP

        ;;; Register operations for INTCTL2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTCTL2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTCTL2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c2, c4, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTCTL2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTCTL2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c2, c4, 0
        bx      lr
        ENDP

        ;;; Register operations for INTCTL3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTCTL3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTCTL3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c3, c4, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTCTL3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTCTL3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c3, c4, 0
        bx      lr
        ENDP

        ;;; Register operations for INTSTR0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTSTR0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTSTR0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c0, c5, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTSTR0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTSTR0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c0, c5, 0
        bx      lr
        ENDP

        ;;; Register operations for INTSTR1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTSTR1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTSTR1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c1, c5, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTSTR1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTSTR1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c1, c5, 0
        bx      lr
        ENDP

        ;;; Register operations for INTSTR2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTSTR2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTSTR2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c2, c5, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTSTR2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTSTR2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c2, c5, 0
        bx      lr
        ENDP

        ;;; Register operations for INTSTR3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadINTSTR3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadINTSTR3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c3, c5, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteINTSTR3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteINTSTR3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c3, c5, 0
        bx      lr
        ENDP

        ;;; Register operations for IINTSRC0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIINTSRC0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIINTSRC0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c0, c6, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIINTSRC0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIINTSRC0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c0, c6, 0
        bx      lr
        ENDP

        ;;; Register operations for IINTSRC1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIINTSRC1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIINTSRC1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c1, c6, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIINTSRC1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIINTSRC1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c1, c6, 0
        bx      lr
        ENDP

        ;;; Register operations for IINTSRC2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIINTSRC2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIINTSRC2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c2, c6, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIINTSRC2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIINTSRC2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c2, c6, 0
        bx      lr
        ENDP

        ;;; Register operations for IINTSRC3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIINTSRC3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIINTSRC3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c3, c6, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIINTSRC3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIINTSRC3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c3, c6, 0
        bx      lr
        ENDP

        ;;; Register operations for FINTSRC0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadFINTSRC0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadFINTSRC0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c0, c7, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteFINTSRC0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteFINTSRC0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c0, c7, 0
        bx      lr
        ENDP

        ;;; Register operations for FINTSRC1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadFINTSRC1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadFINTSRC1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c1, c7, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteFINTSRC1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteFINTSRC1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c1, c7, 0
        bx      lr
        ENDP

        ;;; Register operations for FINTSRC2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadFINTSRC2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadFINTSRC2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c2, c7, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteFINTSRC2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteFINTSRC2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c2, c7, 0
        bx      lr
        ENDP

        ;;; Register operations for FINTSRC3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadFINTSRC3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadFINTSRC3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c3, c7, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteFINTSRC3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteFINTSRC3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c3, c7, 0
        bx      lr
        ENDP

        ;;; Register operations for IPR0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIPR0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIPR0@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c0, c8, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIPR0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIPR0@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c0, c8, 0
        bx      lr
        ENDP

        ;;; Register operations for IPR1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIPR1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIPR1@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c1, c8, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIPR1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIPR1@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c1, c8, 0
        bx      lr
        ENDP

        ;;; Register operations for IPR2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIPR2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIPR2@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c2, c8, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIPR2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIPR2@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c2, c8, 0
        bx      lr
        ENDP

        ;;; Register operations for IPR3 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIPR3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIPR3@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c3, c8, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIPR3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIPR3@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c3, c8, 0
        bx      lr
        ENDP

        ;;; Register operations for IPR4 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIPR4@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIPR4@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c4, c8, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIPR4@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIPR4@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c4, c8, 0
        bx      lr
        ENDP

        ;;; Register operations for IPR5 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIPR5@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIPR5@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c5, c8, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIPR5@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIPR5@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c5, c8, 0
        bx      lr
        ENDP

        ;;; Register operations for IPR6 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIPR6@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIPR6@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c6, c8, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIPR6@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIPR6@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c6, c8, 0
        bx      lr
        ENDP

        ;;; Register operations for IPR7 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadIPR7@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ|
|?g_ReadIPR7@Class_Microsoft_Singularity_Hal_Icu@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c7, c8, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteIPR7@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z|
|?g_WriteIPR7@Class_Microsoft_Singularity_Hal_Icu@@SAXI@Z| PROC
        mcr     p6, 0, r0, c7, c8, 0
        bx      lr
        ENDP

        END

