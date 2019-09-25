;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity ARM Bootstrap
;;;
;;;

        IMPORT |?brtmain@@3P6AHPAUClassVector_Class_System_String@@@ZA|

|defining ?g_CallMain@Class_Microsoft_Singularity_AppRuntime@@SAHPAUClassVector_Class_System_String@@@Z| EQU 1        
        
        include hal.inc

        MACRO
        BREAKPOINT
        ;; bkpt    0xffff
        swi     0xffff03
        MEND

        
        TEXTAREA

;;;
;;; "void __cdecl Draw(unsigned char)"
;;;
        EXPORT |?Draw@@YAXE@Z|
|?Draw@@YAXE@Z| PROC
        mov     pc, lr
        ENDP
                                
;;;
;;; "public: static int Class_Microsoft_Singularity_AppRuntime::g_CallMain(struct ClassVector_Class_System_String *)"
;;;
        LEAF_ENTRY ?g_CallMain@Class_Microsoft_Singularity_AppRuntime@@SAHPAUClassVector_Class_System_String@@@Z
        
        ldr     r1, brtmain
        ldr     r1, [r1]
        mov     pc, r1

brtmain DCD     |?brtmain@@3P6AHPAUClassVector_Class_System_String@@@ZA|
        NESTED_END

;;;
;;;
;;;
        LEAF_ENTRY fmod
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;;
;;;
        LEAF_ENTRY fmodf
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;;
;;;
        LEAF_ENTRY ?Halt@@YAXXZ
        DCD     0xe320f003      ;; WFI Note: ARMv7 Specific.
        bx      lr
        LEAF_END

        END
