;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;;
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

|defining ?g_SetCurrentThreadContext@Class_Microsoft_Singularity_Processor@@SAXPAUStruct_Microsoft_Singularity_X86_ThreadContext@@@Z| EQU 1
|defining ?g_Initialize@Class_System_VTable@@SAXXZ| EQU 1
|defining ?g_Halt@Struct_Microsoft_Singularity_Hal_Cpu@@SAXXZ| EQU 1
|defining ?c_exceptionHandler@@3P6AXHPAUStruct_Microsoft_Singularity_ThreadContext@@@ZA| EQU 1
|defining ?c_interruptHandler@@3P6AXHPAUStruct_Microsoft_Singularity_ThreadContext@@@ZA| EQU 1
|defining ?g_DisablePaging@Class_Microsoft_Singularity_Processor@@SAXXZ| EQU 1
|defining ?g_EnterRing3@Class_Microsoft_Singularity_Processor@@SAXXZ| EQU 1
|defining ?g_GetFrameEbp@Class_Microsoft_Singularity_Processor@@SAPAUuintPtr@@PAU2@@Z| EQU 1
|defining ?g_GetStackPointer@Class_Microsoft_Singularity_Processor@@SAPAUuintPtr@@XZ| EQU 1
|defining ?g_GetFrameEip@Class_Microsoft_Singularity_Processor@@SAPAUuintPtr@@PAU2@@Z| EQU 1
|defining ?g_GetFramePointer@Class_Microsoft_Singularity_Processor@@SAPAUuintPtr@@XZ| EQU 1
|defining ?g_ReadMsr@Class_Microsoft_Singularity_Processor@@SA_KI@Z| EQU 1
|defining ?c_LinkStackFunctionsBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA| EQU 1
|defining ?c_LinkStackFunctionsLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA| EQU 1
|defining ?c_LinkStackBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA| EQU 1
|defining ?c_LinkStackLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA| EQU 1
|defining ?c_UnlinkStackBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA| EQU 1
|defining ?c_UnlinkStackLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA| EQU 1
|defining ?c_LinkStackStubsBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA| EQU 1
|defining ?c_LinkStackStubsLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA| EQU 1
|defining ?g_GetCr3@Class_Microsoft_Singularity_Processor@@SAIXZ| EQU 1
|defining ?g_InitFpu@Class_Microsoft_Singularity_Processor@@SAXXZ| EQU 1
|defining ?g_ClearFpuStatus@Class_Microsoft_Singularity_Processor@@SAXXZ| EQU 1
|defining ?g_ReadFpuStatus@Class_Microsoft_Singularity_Processor@@SAIXZ| EQU 1
|defining ?g_LimitedDispatchException@Class_Microsoft_Singularity_Processor@@SAXHPAUStruct_Microsoft_Singularity_X86_ThreadContext@@@Z| EQU 1
|defining ?g_MpCallEntryPoint@Class_Microsoft_Singularity_Processor@@SAXPAUuintPtr@@@Z| EQU 1
|defining ?g_PrivateChangeAddressSpace@Class_Microsoft_Singularity_Processor@@SAXI@Z| EQU 1
|defining ?g_PrivateEnablePaging@Class_Microsoft_Singularity_Processor@@SAXI@Z| EQU 1
|defining ?g_PrivateInvalidateTLBEntry@Class_Microsoft_Singularity_Processor@@SAXPAUuintPtr@@@Z| EQU 1
|defining ?g_WriteMsr@Class_Microsoft_Singularity_Processor@@SAXI_K@Z| EQU 1
;|defining ?g_CollectBodyTransition@Class_System_GC@@SAXPAUClass_System_Threading_Thread@@H@Z| EQU 1
;|defining ?g_setStopContext@Class_System_Threading_Thread@@SAXPAU1@PAUClass_System_Exception@@@Z| EQU 1
|defining __throwDispatcherExplicitAddrAfter| EQU 1
;|defining staticDataPointerBitMap| EQU 1
|defining ?g_HalGetMpBootInfo@Struct_Microsoft_Singularity_MpBootInfo@@SAPAU1@XZ| EQU 1
|defining ?g_LinkSharedStack@Struct_Microsoft_Singularity_V1_Services_StackService@@SAXXZ| EQU 1
|defining ?g_UnlinkSharedStack@Struct_Microsoft_Singularity_V1_Services_StackService@@SAXXZ| EQU 1
|defining ?g_LinkStack0@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack4@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack8@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack12@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack16@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack20@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack24@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack28@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack32@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack36@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack40@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack44@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack48@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack52@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack56@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack60@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack64@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack68@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack72@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack76@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack80@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack84@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack88@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack92@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack96@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack100@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack104@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack108@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack112@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack116@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack120@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack124@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_LinkStack128@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack0@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack4@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack8@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack12@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack16@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack20@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack24@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack28@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack32@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack36@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack40@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack44@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack48@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack52@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack56@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack60@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack64@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack68@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack72@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack76@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack80@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack84@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack88@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack92@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack96@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack100@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack104@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack108@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack112@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack116@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack120@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack124@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1
|defining ?g_UnlinkStack128@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ| EQU 1

        include hal.inc

        MACRO
        BREAKPOINT
        ;; bkpt    0xffff
        swi     0xffff03
        MEND


        TEXTAREA

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Processor::g_SetCurrentThreadContext(struct Struct_Microsoft_Singularity_X86_ThreadContext *)"
;;;
        LEAF_ENTRY ?g_SetCurrentThreadContext@Class_Microsoft_Singularity_Processor@@SAXPAUStruct_Microsoft_Singularity_X86_ThreadContext@@@Z
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_System_VTable::g_Initialize(void)"
;;;
        LEAF_ENTRY ?g_Initialize@Class_System_VTable@@SAXXZ
;;;     BREAKPOINT ; we ignore this for now.
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Struct_Microsoft_Singularity_Hal_Cpu::g_Halt(void)"
;;;
        LEAF_ENTRY ?g_Halt@Struct_Microsoft_Singularity_Hal_Cpu@@SAXXZ
        DCD     0xe320f003      ;; WFI Note: ARMv7 Specific.
        bx      lr
        LEAF_END

;;;
;;; "void(__cdecl* c_exceptionHandler)(int,struct Struct_Microsoft_Singularity_ThreadContext *)"
;;;
        LEAF_ENTRY ?c_exceptionHandler@@3P6AXHPAUStruct_Microsoft_Singularity_ThreadContext@@@ZA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "void(__cdecl* c_interruptHandler)(int,struct Struct_Microsoft_Singularity_ThreadContext *)"
;;;
        LEAF_ENTRY ?c_interruptHandler@@3P6AXHPAUStruct_Microsoft_Singularity_ThreadContext@@@ZA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned char Class_Microsoft_Singularity_Memory_Stacks::c_LinkStackBegin"
;;;
        LEAF_ENTRY ?c_LinkStackFunctionsBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned char Class_Microsoft_Singularity_Memory_Stacks::c_LinkStackLimit"
;;;
        LEAF_ENTRY ?c_LinkStackFunctionsLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned char Class_Microsoft_Singularity_Memory_Stacks::c_LinkStackBegin"
;;;
        LEAF_ENTRY ?c_LinkStackBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned char Class_Microsoft_Singularity_Memory_Stacks::c_LinkStackLimit"
;;;
        LEAF_ENTRY ?c_LinkStackLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned char Class_Microsoft_Singularity_Memory_Stacks::c_LinkStackBegin"
;;;
        LEAF_ENTRY ?c_UnlinkStackBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned char Class_Microsoft_Singularity_Memory_Stacks::c_LinkStackLimit"
;;;
        LEAF_ENTRY ?c_UnlinkStackLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned char Class_Microsoft_Singularity_Memory_Stacks::c_LinkStackBegin"
;;;
        LEAF_ENTRY ?c_LinkStackStubsBegin@Class_Microsoft_Singularity_Memory_Stacks@@2EA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static unsigned char Class_Microsoft_Singularity_Memory_Stacks::c_LinkStackLimit"
;;;
        LEAF_ENTRY ?c_LinkStackStubsLimit@Class_Microsoft_Singularity_Memory_Stacks@@2EA
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_Microsoft_Singularity_Processor::g_LimitedDispatchException(int,struct Struct_Microsoft_Singularity_X86_ThreadContext *)"
;;;
        LEAF_ENTRY ?g_LimitedDispatchException@Class_Microsoft_Singularity_Processor@@SAXHPAUStruct_Microsoft_Singularity_X86_ThreadContext@@@Z
        BREAKPOINT
        bx      lr
        LEAF_END

;;;
;;; "public: static void __cdecl Class_System_GC::g_CollectBodyTransition(struct Class_System_Threading_Thread *,int)"
;;;
;        LEAF_ENTRY ?g_CollectBodyTransition@Class_System_GC@@SAXPAUClass_System_Threading_Thread@@H@Z
;        BREAKPOINT
;        bx      lr
;        LEAF_END

;;;
;;; "public: static void __cdecl Class_System_Threading_Thread::g_setStopContext(struct Class_System_Threading_Thread *,struct Class_System_Exception *)"
;;;
;        LEAF_ENTRY ?g_setStopContext@Class_System_Threading_Thread@@SAXPAU1@PAUClass_System_Exception@@@Z
;        BREAKPOINT
;        bx      lr
;        LEAF_END

;;;
;;; "__throwDispatcherExplicitAddrAfter"
;;;
        LEAF_ENTRY __throwDispatcherExplicitAddrAfter
        BREAKPOINT
        bx      lr
        LEAF_END

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; ??????????????
;;;
;;;
;;; "staticDataPointerBitMap"
;;;
;        LEAF_ENTRY staticDataPointerBitMap
;        BREAKPOINT
;        bx      lr
;        LEAF_END

;;;
;;; "Win32RaceRegionStart"/"Win32RaceRegionStart"
;;;
        EXPORT |Win32RaceRegionStart|
|Win32RaceRegionStart|  DCD     0
        EXPORT |Win32RaceRegionEnd|
|Win32RaceRegionEnd|    DCD     0

        LEAF_ENTRY ?g_HalGetMpBootInfo@Struct_Microsoft_Singularity_MpBootInfo@@SAPAU1@XZ
        BREAKPOINT
        bx      lr
        LEAF_END

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Linked Stacks.
;;;
        LEAF_ENTRY ?g_LinkSharedStack@Struct_Microsoft_Singularity_V1_Services_StackService@@SAXXZ
        bkpt    0xffff
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_UnlinkSharedStack@Struct_Microsoft_Singularity_V1_Services_StackService@@SAXXZ
        bkpt    0xffff
        bx      lr
        LEAF_END

        LEAF_ENTRY ?g_LinkStack0@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack4@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack8@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack12@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack16@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack20@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack24@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack28@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack32@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack36@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack40@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack44@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack48@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack52@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack56@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack60@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack64@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack68@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack72@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack76@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack80@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack84@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack88@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack92@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack96@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack100@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack104@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack108@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack112@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack116@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack120@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack124@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_LinkStack128@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack0@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack4@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack8@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack12@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack16@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack20@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack24@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack28@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack32@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack36@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack40@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack44@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack48@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack52@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack56@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack60@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack64@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack68@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack72@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack76@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack80@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack84@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack88@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack92@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack96@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack100@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack104@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack108@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack112@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack116@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack120@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack124@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

        LEAF_ENTRY ?g_UnlinkStack128@Class_Microsoft_Singularity_Memory_Stacks@@SAXXZ
        bkpt    0xffff
        LEAF_END

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; "activationDescriptorTable"
;;;
;        EXPORT |activationDescriptorTable|
;|activationDescriptorTable| DCD 0

;;;
;;; "callSetSiteNumberToIndex"
;;;
;        EXPORT |callSetSiteNumberToIndex|
;|callSetSiteNumberToIndex| DCD 0

;;;
;;; "callSiteSetCount"
;;;
;        EXPORT |callSiteSetCount|
;|callSiteSetCount| DCD 0

;;;
;;; "returnAddressToCallSiteSetNumbers"
;;;
;        EXPORT |returnAddressToCallSiteSetNumbers|
;|returnAddressToCallSiteSetNumbers| DCD 0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

        END
