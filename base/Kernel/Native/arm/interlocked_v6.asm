;     title  "Interlocked Operations"
;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;   intrlock.asm
;
; Abstract:
;
;   This module implements the 32 and 16 bit interlocked operations for ARMv6 and beyond.
;   The instructions used in this module for gaining exclusive access to a memory location 
;   arent supported in ARMv5 and earlier
;
;   The functions aren't optimized because these are brand new instructions that we dont 
;   understand completely. That should be done after profiling and understanding their behavior.
; 
;   This whole file will be discarded when the intrinsics come in.
;
; Environment:
;
;   Kernel and User mode.
;
;--

#include "ksarm.h"

#if defined(_ARM_WORKAROUND_)
; The LDREXH, STREXH, LDREXD, STREXD and CLREX instructions arent supported 
; by the current assembler. Remove this and replace with the actual instructions
; when the assembler supports it
; This is not a generic assembler so I am explicitly defining values only for the 
; instructions I am using


#define LDREXH_R12_R0           0xE1F0CF9F          ;ldrexh      r12, [r0]          (1110 0001 1111 0000 1100 1111 1001 1111)
#define STREXHEQ_R3_R1_R0       0x01E03F91          ;strexheq    r3,  r1,  [r0]     (0000 0001 1110 0000 0011 1111 1001 0001)
#define STREXH_R3_R12_R0        0xE1E03F9C          ;strexh      r3,  r12, [r0]     (1110 0001 1110 0000 0011 1111 1001 1100)
#define LDREXD_R4_R0            0xE1B04F9F          ;ldrexd      r4,  [r0]          (1110 0001 1011 0000 0100 1111 1001 1111)
#define STREXDEQ_R2_R6_R0       0x01A02F96          ;strexdeq    r2,  r6,  [r0]     (0000 0001 1010 0000 0010 1111 1001 0110)

#define CLREX                   0xF57FF01F          ; clrex                         (1111 0101 0111 1111 1111 0000 0001 1111)

#endif


        TEXTAREA
   
    LEAF_ENTRY InterlockedExchange
1       ldrex       r12, [r0]                       ; load from the address and mark it exclusive
        strex       r3,  r1,  [r0]                  ; attempt to store the new value
        cmp         r3,  #1                         ; check if the store failed (0=success, 1=failure)
        beq         %B1                             ; restart if the store failed
        mov         r0,  r12                        ; return the original value
        mov         pc,  lr
    LEAF_END
 
    LEAF_ENTRY InterlockedCompareExchange
1       ldrex       r12, [r0]                       ; load from the address and mark it exclusive
        cmp         r12, r2                         ; compare the value with the comperand(r2)
        strexeq     r3,  r1,  [r0]                  ; if they were equal, attempt to store the new value (r1)
        bne         %F2                             ; if they were not equal jump to (2) which clears the exclusive tag on the address and returns
        cmp         r3,  #1                         ; check the status of the store (returned in r3)
        beq         %B1                             ; go back to the start if it failed (0=success, 1=failure)
        bne         %F3                             ; if it succeeded, jump to (3) and return. there is no need to clrex if strex succeeded
2       dcd         CLREX                           ; clrex
3       mov         r0,  r12
        mov         pc,  lr
    LEAF_END

    LEAF_ENTRY InterlockedCompareExchange16         ; has the same structure as InterlockedCompareExchange, but uses half word operands
1       dcd         LDREXH_R12_R0
        cmp         r12, r2
        dcd         STREXHEQ_R3_R1_R0         
        bne         %F2
        cmp         r3,  #1
        beq         %B1
        bne         %F3
2       dcd         CLREX                           ; clrex
3       mov         r0,  r12
        mov         pc,  lr
    LEAF_END
 
    LEAF_ENTRY InterlockedIncrement
1       ldrex       r12, [r0]                       ; load from the address and mark it exclusive
        add         r12, r12, #1                    ; increment it
        strex       r3,  r12, [r0]                  ; attempt to store the new value
        cmp         r3,  #1                         ; check if it succeeded (0=success, 1=failure)
        beq         %B1                             ; loop if it failed
        mov         r0,  r12                        ; return the increment value if it succeeded
        mov         pc,  lr
    LEAF_END
 
    LEAF_ENTRY InterlockedIncrement16               ; has the same structure as InterlockedIncrement, but uses half word operands
1       dcd         LDREXH_R12_R0
        add         r12, r12, #1
        dcd         STREXH_R3_R12_R0
        cmp         r3, #1
        beq         %B1
        mov         r0,  r12
        mov         pc,  lr
    LEAF_END
 
    LEAF_ENTRY InterlockedDecrement                 ; has the same structure as InterlockedIncrement
1       ldrex       r12, [r0]
        sub         r12, r12, #1
        strex       r3,  r12, [r0]
        cmp         r3, #1
        beq         %B1
        mov         r0,  r12
        mov         pc,  lr
    LEAF_END
     
    LEAF_ENTRY InterlockedDecrement16               ; has the same structure as InterlockedIncrement
1       dcd         LDREXH_R12_R0
        sub         r12, r12, #1
        dcd         STREXH_R3_R12_R0
        cmp         r3, #1
        beq         %B1
        mov         r0,  r12
        mov         pc,  lr
    LEAF_END  

    LEAF_ENTRY InterlockedExchangeAdd               ; has the same structure as InterlockedIncrement
1       ldrex       r12, [r0]
        add         r2,  r12, r1
        strex       r3,  r2,  [r0]
        cmp         r3,  #1
        beq         %B1
        mov         r0,  r12
        mov         pc,  lr
    LEAF_END
     
    LEAF_ENTRY InterlockedOr                        ; has the same structure as InterlockedIncrement
1       ldrex       r12, [r0]
        orr         r2,  r12, r1
        strex       r3,  r2,  [r0]
        cmp         r3,  #1
        beq         %B1
        mov         r0,  r12
        mov         pc,  lr
    LEAF_END

    LEAF_ENTRY InterlockedAnd                       ; has the same structure as InterlockedIncrement
1       ldrex       r12, [r0]
        and         r2,  r12, r1
        strex       r3,  r2,  [r0]
        cmp         r3,  #1
        beq         %B1
        mov         r0,  r12
        mov         pc,  lr
    LEAF_END
     
    LEAF_ENTRY InterlockedXor                       ; has the same structure as InterlockedIncrement
1       ldrex       r12, [r0]
        eor         r2,  r12, r1
        strex       r3,  r2,  [r0]
        cmp         r3,  #1
        beq         %B1
        mov         r0,  r12
        mov         pc,  lr
    LEAF_END
    
    
    ; InterlockedCompareExchange64 - 
    ; Arguments:
    ; r0 = Pointer to Destination
    ; r1 = Exchange.LowPart
    ; r2 = Exchange.HighPart
    ; r3 = Comperand.LowPart
    ; [sp] = Comperand.HighPart
    
    NESTED_ENTRY InterlockedCompareExchange64
        stmdb       sp!, {r4-r7, lr}
        PROLOG_END
        ldr         r12,  [sp, #0x14]               ; load r12 with Comperand.HighPart
        mov         r6,   r1                        ; move [Exchange.LowPart,Exchange.HighPart] to [r6,r7] because the strex instruction demands that Rm be an even numbered register
        mov         r7,   r2
1       dcd         LDREXD_R4_R0                    ; ldrexd      r4,  [r0] (r4 = Destination.LowPart, r5 = Destination.HighPart)
        cmp         r4,  r3                         ; if (Destination.LowPart == Comperand.LowPart)
        cmpeq       r5,  r12                        ;  && (Destination.HightPart == Comperand.HighPart)
        dcd         STREXDEQ_R2_R6_R0               ; streqd      r2,  r6, [r0] (attempt to store the new value if equal. [r0] = r6; [r0 + 4] = r7;)
        bne         %F2                             ; if not equal, branch to end and return
        cmp         r2,  #1                         ; check the status of the attempt (0=success, 1=failure)
        beq         %B1                             ; loop if the store failed
        bne         %F3
2       dcd         CLREX                           ; clrex
3       mov         r0,  r4
        mov         r1,  r5
        ldmia       sp!, {r4-r7, pc}
    NESTED_END
     
    END
 
