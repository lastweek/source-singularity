;
; Copyright (c) Microsoft Corporation.   All rights reserved.
;
; Dummy include file for assembly files.

externdef ?c_halPageDescriptor@Class_System_GCs_PageTable@@2PEAUUntracedPtr_uint32@@EA:NEAR 
externdef ?c_threadTable@Class_System_Threading_Thread@@2PEAUClassVector_Class_System_Threading_Thread@@EA:NEAR
externdef ?c_initialThread@Class_System_Threading_Thread@@2PEAU1@EA:NEAR
externdef ?c_segmentAlignMask@Class_System_GCs_DistributedPT@@2PEAUuintPtr@@EA:NEAR 
externdef ?c_pageInSegmentAlignMask@Class_System_GCs_DistributedPT@@2PEAUuintPtr@@EA:NEAR 

; reg64 and reg32 may be the same register (e.g. rax and eax)
CurrentThreadIndex MACRO reg64, reg32, tmp64
;        int 3	
        mov reg64, rsp

if DISTRIBUTED_PT
    if FLAT_PT
        mov tmp64, reg64
        ;get segment part
        and tmp64, qword ptr [?c_segmentAlignMask@Class_System_GCs_DistributedPT@@2PEAUuintPtr@@EA]
        ;get page number within the segment
        and reg64, qword ptr [?c_pageInSegmentAlignMask@Class_System_GCs_DistributedPT@@2PEAUuintPtr@@EA]
        ; calculate address of the page entry
        shr reg64, PAGE_BITS
        lea reg64, dword ptr [reg64*4]
        add reg64, tmp64
        add reg64, qword ptr ?c_halPageDescriptor@Class_System_GCs_PageTable@@2PEAUUntracedPtr_uint32@@EA
        mov reg32, dword ptr [reg64]
    else
        ; todo: two level table support
        int 3
    endif
else        
        shr reg64, PAGE_BITS
        lea reg64, dword ptr [reg64*4]
        add reg64, qword ptr ?c_halPageDescriptor@Class_System_GCs_PageTable@@2PEAUUntracedPtr_uint32@@EA
        mov reg32, dword ptr [reg64]
endif 
        
        and reg32, 0FFF0h
        shr reg32, 4
        ENDM

; reg64 and reg32 may be the same register (e.g. rax and eax)
ThreadFromIndex MACRO reg64, reg32
if REFERENCE_COUNTING_GC
        int 3 ;12 below is wrong
        lea reg64, qword ptr [reg32*8+12]
elseif DEFERRED_REFERENCE_COUNTING_GC
        int 3 ;12 below is wrong
        lea reg64, qword ptr [reg32*8+12]
else ; REFERENCE_COUNTING_GC
        lea reg64, qword ptr [reg32*8+16]
endif
        add reg64, qword ptr ?c_threadTable@Class_System_Threading_Thread@@2PEAUClassVector_Class_System_Threading_Thread@@EA
        mov reg64, qword ptr [reg64]
        ENDM

; reg64 and reg32 may be the same register (e.g. rax and eax)
BartokCurrentThread MACRO reg64, reg32, tmp64
;        int 3	
        CurrentThreadIndex reg64,reg32, tmp64
        ThreadFromIndex reg64,reg32
        ENDM

; must use this macro for any push in a prolog
; so that call stack will be correct
PrologPush MACRO reg
        push      reg
        .pushreg  reg
        ENDM

; must use this macro for any "mov rbp, rsp"
; in a prolog so that call stack will be correct
SetFramePointer MACRO bpreg
        mov        bpreg, rsp
        .setframe  bpreg, 0
        ENDM

; must use this macro for any "sub rsp, x"
; in a prolog so that call stack will be correct
SubRsp MACRO amount
        sub          rsp, amount
        .allocstack  amount
        ENDM
