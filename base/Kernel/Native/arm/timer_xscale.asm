;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity ARM Bootstrap
;;;
;;; XScale timer support routines
;;;
;;; Definitions taken from:
;;;
;;;  Chapter 11, Intel 81348 I/O Processor, September 2006, O/N: 315036-001US
;;;

        CODE32

        AREA   |.text|, CODE, ARM

        ;;; Register operations for TMR0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadTMR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ|
|?g_ReadTMR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c0, c9, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteTMR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z|
|?g_WriteTMR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z| PROC
        mcr     p6, 0, r0, c0, c9, 0
        bx      lr
        ENDP

        ;;; Register operations for TMR1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadTMR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ|
|?g_ReadTMR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c1, c9, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteTMR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z|
|?g_WriteTMR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z| PROC
        mcr     p6, 0, r0, c1, c9, 0
        bx      lr
        ENDP

        ;;; Register operations for TCR0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadTCR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ|
|?g_ReadTCR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c2, c9, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteTCR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z|
|?g_WriteTCR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z| PROC
        mcr     p6, 0, r0, c2, c9, 0
        bx      lr
        ENDP

        ;;; Register operations for TCR1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadTCR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ|
|?g_ReadTCR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c3, c9, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteTCR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z|
|?g_WriteTCR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z| PROC
        mcr     p6, 0, r0, c3, c9, 0
        bx      lr
        ENDP

        ;;; Register operations for TRR0 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadTRR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ|
|?g_ReadTRR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c4, c9, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteTRR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z|
|?g_WriteTRR0@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z| PROC
        mcr     p6, 0, r0, c4, c9, 0
        bx      lr
        ENDP

        ;;; Register operations for TRR1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadTRR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ|
|?g_ReadTRR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c5, c9, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteTRR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z|
|?g_WriteTRR1@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z| PROC
        mcr     p6, 0, r0, c5, c9, 0
        bx      lr
        ENDP

        ;;; Register operations for TISR ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadTISR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ|
|?g_ReadTISR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c6, c9, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteTISR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z|
|?g_WriteTISR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z| PROC
        mcr     p6, 0, r0, c6, c9, 0
        bx      lr
        ENDP

        ;;; Register operations for WDTCR ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadWDTCR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ|
|?g_ReadWDTCR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c7, c9, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteWDTCR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z|
|?g_WriteWDTCR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z| PROC
        mcr     p6, 0, r0, c7, c9, 0
        bx      lr
        ENDP

        ;;; Register operations for WRTSR ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        EXPORT |?g_ReadWRTSR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ|
|?g_ReadWRTSR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAIXZ| PROC
        mov     r0, #0
        mrc     p6, 0, r0, c8, c9, 0
        bx      lr
        ENDP

        EXPORT |?g_WriteWRTSR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z|
|?g_WriteWRTSR@Class_Microsoft_Singularity_Hal_XScaleTimers@@SAXI@Z| PROC
        mcr     p6, 0, r0, c8, c9, 0
        bx      lr
        ENDP

        END

