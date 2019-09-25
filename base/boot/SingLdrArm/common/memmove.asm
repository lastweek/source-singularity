;**********************************************************************
; void *
; memmove( void *dest, const void *src, size_t count );
;
;   memmove() copies 'count' bytes from the source buffer to the 
;   destination buffer and returns a pointer to the destination 
;   buffer. memmove() guarantees the overlaping buffers will 
;   be copied successfully. 
;
;**********************************************************************
;
; $$$ NOTE $$$: These routines use the LDRH opcode which is not 
; supported on ARM 3 or 3T architectures.  Hence, these routines 
; assume ARM 4 or later architectures.
;
;**********************************************************************

	OPT	2	; disable listing
	INCLUDE kxarm.inc
	OPT	1	; reenable listing

dest    RN  R0
source  RN  R1
count   RN  R2
temp1   RN  R3
temp2   RN  R4
temp3   RN  R5
temp4   RN  R12

  IF Thumbing
    THUMBAREA
  ENDIF

    NESTED_ENTRY memmove

    ROUT

  IF Thumbing
    ; Switch from Thumb mode to ARM mode
    DCW     0x4778              ; bx pc
    DCW     0x46C0              ; nop
  ENDIF

    STMDB   sp!, {dest,temp2,temp3,lr}  ; save registers

    PROLOG_END

            ;if source comes before destination copy from tail to head
    CMP     source, dest
    BGE     HEAD_TO_TAIL                    ; if source < dest

;**********************************************************************
; Copy from tail to head to avoid source overwrite because the source 
; precedes the destination
;**********************************************************************
TAILTOHEAD
            ;Move pointers to the tails
    ADD     source, source, count
    ADD     dest,   dest,   count

    CMP     count, #8                       ;if < 8 bytes, byte moves
    BLT     TTH_BYTEMOVE4

            ;check if destination is word aligned, if not then align it
    ANDS    temp1, dest, #3                         ; 2-3 cycles
    BEQ     TTH_CHKSRC_ALIGN
;
;read 1 to 3 bytes until the destination is word aligned, then 
;see if the source is word aligned, if it is then go back to 
;word length moves, else continue on with single byte moves
;
TTH_ATTEMPTALIGN
    LDRB    temp2, [source, #-1]!                   ; 8 cycles/1-3 bytes
    CMP     temp1, #2
    STRB    temp2, [dest,   #-1]!
    LDRGEB  temp3, [source, #-1]!
    SUB     count, count, temp1
    LDRGTB  temp2, [source, #-1]!
    STRGEB  temp3, [dest,   #-1]!
    STRGTB  temp2, [dest,   #-1]!

    ; Check if source is word aligned, if not check for word
    ; alignment. 
TTH_CHKSRC_ALIGN
    TST     source, #1                              ; 3-7 cycles
    BNE     TTH_UNALIGNED           ; Unaligned moves
    TST     source, #2
    BNE     TTH_HWORD_ALIGNED       ; Half Word aligned

;
; Word aligned source and destination.
;   Move blocks of 32 bytes until we have less than 32 bytes left,
;   then divide moves in half down to less than 4 then jump to byte
;   moves.
;   NOTE: Because of the overhead of pushing registers for 32 byte
;   moves it is actually more efficient to use 16 byte moves for
;   blocks of less than 128 bytes.
;
TTH_REALIGNED
    SUBS    count, count, #32                       ; 2-3 cycles
    BLT     TTH_BLK16

TTH_BLK32                                           ; 20 cycles/32 bytes
    LDMDB   source!, {temp1,temp2,temp3,lr}
    STMDB   dest!,   {temp1,temp2,temp3,lr}
    LDMDB   source!, {temp1,temp2,temp3,lr}
    SUBS    count, count, #32
    STMDB   dest!,   {temp1,temp2,temp3,lr}
    BGE     TTH_BLK32

TTH_BLK16                                           ; 10 cycles/16 bytes
    ADDS    count, count, #16
    LDMGEDB source!, {temp1, temp2, temp3, lr}
    SUBGE   count, count, #16
    STMGEDB dest!,   {temp1, temp2, temp3, lr}

TTH_BLK8                                            ; 6 cycles / 8 bytes
    ADDS    count, count, #8
    LDMGEDB source!, {temp1, temp2}
    SUBGE   count, count, #8
    STMGEDB dest!,   {temp1, temp2}

TTH_BLK4                                            ; 6-9 cycles/4 bytes
    ADDS    count, count, #4
    LDRGE   temp1, [source, #-4]!
    STRGE   temp1, [dest, #-4]!

TTH_WORD_BYTES
    ADDLTS  count, count, #4
    BEQ     TTH_WORD_EXIT
    LDRB    temp1, [source, #-1]!                   ; 4-7 cycles/1 byte
    CMP     count, #2
    STRB    temp1, [dest,   #-1]!
    LDRGEB  temp2, [source, #-1]!
    LDRGTB  temp3, [source, #-1]!                   ; 8 cycles/1-2 bytes
    STRGEB  temp2, [dest,   #-1]!
    STRGTB  temp3, [dest,   #-1]!


TTH_WORD_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}
  ENDIF

;
; Source and Destination are half word aligned.
;   For blocks < 96 bytes it's actually more efficient to jump to 
;   the 8 byte copy than take the hit for setup time on 32 byte copy.
;
TTH_HWORD_ALIGNED
    LDRH    lr, [source, #-2]!                      ; 4-5 cycles
    SUBS    count, count, #32
    MOV     lr, lr, LSL #16
    BLT     TTH_HWORD8_TST

TTH_HWORD32                                         ; 35 cycles/32 bytes
    LDMDB   source!, {temp1,temp2,temp3,temp4}
    SUBS    count, count, #32
    ORR     lr, lr, temp4, LSR #16
    MOV     temp4, temp4, LSL #16
    ORR     temp4, temp4, temp3, LSR #16
    MOV     temp3, temp3, LSL #16
    ORR     temp3, temp3, temp2, LSR #16
    MOV     temp2, temp2, LSL #16
    ORR     temp2, temp2, temp1, LSR #16
    STMDB   dest!, {temp3,temp4,lr}         ; Store bytes 21-32
    STR     temp2, [dest, #-4]!             ; Store bytes 17-20
    MOV     lr, temp1, LSL #16
    LDR     temp4, [source, #-4]!
    LDMDB   source!, {temp1,temp2,temp3}
    ORR     lr, lr, temp4, LSR #16
    MOV     temp4, temp4, LSL #16
    ORR     temp4, temp4, temp3, LSR #16
    MOV     temp3, temp3, LSL #16
    ORR     temp3, temp3, temp2, LSR #16
    MOV     temp2, temp2, LSL #16
    ORR     temp2, temp2, temp1, LSR #16
    STMDB   dest!, {temp3,temp4,lr}         ; Store bytes 5-16
    STR     temp2, [dest, #-4]!             ; Store bytes 1-4
    MOV     lr, temp1, LSL #16
    BGE     TTH_HWORD32

TTH_HWORD8_TST
    ADDS    count, count, #24
    BLT     TTH_HWORD4

TTH_HWORD8                                          ; 11 cycles/8 bytes
    LDMDB   source!, {temp2, temp3}
    SUBS    count, count, #8
    ORR     lr, lr, temp3, LSR #16
    MOV     temp3, temp3, LSL #16
    ORR     temp3, temp3, temp2, LSR #16
    STR     lr, [dest, #-4]!
    STR     temp3, [dest, #-4]!
    MOV     lr, temp2, LSL #16
    BGE     TTH_HWORD8

TTH_HWORD4                                          ; 3-12 cycles/4 bytes
    ADDS    count, count, #4
    BLT     TTH_HWORD_BYTES
    LDR     temp1, [source, #-4]!
    ORR     lr, lr, temp1, LSR #16
    STR     lr, [dest, #-4]!
    MOV     lr, temp1, LSL #16

TTH_HWORD_BYTES
    ADDLTS  count, count, #4
    BEQ     TTH_HWORD_EXIT
    
    MOV     lr, lr, LSR #16                         ; 11 cycles/1-3 bytes
    CMP     count, #2
    MOVLT   lr, lr, LSR #8
    STRLTB  lr, [dest, #-1]!
    LDRGTB  temp1, [source, #-1]!
    STRGEH  lr, [dest, #-2]!
    STRGTB  temp1, [dest, #-1]!

TTH_HWORD_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}
  ENDIF

TTH_UNALIGNED
    TST     source, #2
    BEQ     TTH_OFFONE
;
; 3 Byte difference between word and source.
;
TTH_OFFTHREE
    LDRB    temp3, [source, #-1]!                   ; 5-6 cycles
    LDRH    lr,    [source, #-2]!
    SUBS    count, count, #32
    ORR     lr, lr, temp3, LSL #16
    MOV     lr, lr, LSL #8
    BLT     TTH_OFFTHREE8_TST

TTH_OFFTHREE32                                      ; 35 cycles/32 bytes
    LDMDB   source!, {temp1,temp2,temp3,temp4}
    SUBS    count, count, #32
    ORR     lr, lr, temp4, LSR #24
    MOV     temp4, temp4, LSL #8
    ORR     temp4, temp4, temp3, LSR #24
    MOV     temp3, temp3, LSL #8
    ORR     temp3, temp3, temp2, LSR #24
    MOV     temp2, temp2, LSL #8
    ORR     temp2, temp2, temp1, LSR #24
    STMDB   dest!, {temp3,temp4,lr}         ; Store bytes 21-32
    STR     temp2, [dest, #-4]!             ; Store bytes 17-20
    MOV     lr, temp1, LSL #8
    LDR     temp4, [source, #-4]!
    LDMDB   source!, {temp1,temp2,temp3}
    ORR     lr, lr, temp4, LSR #24
    MOV     temp4, temp4, LSL #8
    ORR     temp4, temp4, temp3, LSR #24
    MOV     temp3, temp3, LSL #8
    ORR     temp3, temp3, temp2, LSR #24
    MOV     temp2, temp2, LSL #8
    ORR     temp2, temp2, temp1, LSR #24
    STMDB   dest!, {temp3,temp4,lr}         ; Store bytes 5-16
    STR     temp2, [dest, #-4]!             ; Store bytes 1-4
    MOV     lr, temp1, LSL #8
    BGE     TTH_OFFTHREE32

TTH_OFFTHREE8_TST
    ADDS    count, count, #24
    BLT     TTH_OFFTHREE4

TTH_OFFTHREE8                                       ; 11 cycles/8 bytes
    LDMDB   source!, {temp1, temp2}
    SUBS    count, count, #8
    ORR     lr, lr, temp2, LSR #24
    MOV     temp2, temp2, LSL #8
    ORR     temp2, temp2, temp1, LSR #24
    STR     lr, [dest, #-4]!                ; Store bytes 5-8
    STR     temp2, [dest, #-4]!             ; Store bytes 1-4
    MOV     lr, temp1, LSL #8
    BGE     TTH_OFFTHREE8

TTH_OFFTHREE4                                       ; 3-11 cycles/4 bytes
    ADDS    count, count, #4
    BLT     TTH_OFFTHREE_BYTES
    LDR     temp3, [source, #-4]!
    ORR     lr, lr, temp3, LSR #24
    STR     lr, [dest, #-4]!
    MOV     lr, temp3, LSL #8

TTH_OFFTHREE_BYTES
    ADDLTS  count, count, #4
    BEQ     TTH_OFFTHREE_EXIT
    MOV     lr, lr, LSR #8                          ; 11 cycles/1-3 bytes
    CMP     count, #2
    MOVLT   temp1, lr, LSR #16
    STRLTB  temp1, [dest, #-1]!
    MOVGE   temp1, lr, LSR #8
    STRGEH  temp1, [dest, #-2]!
    STRGTB  lr, [dest, #-1]!

TTH_OFFTHREE_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}
  ENDIF

;
; One Byte difference between word and source.
;
TTH_OFFONE
    LDRB    lr, [source, #-1]!
    SUBS    count, count, #32                       ; 2-3 cycles
    MOV     lr, lr, LSL #24
    BLT     TTH_OFFONE8_TST

TTH_OFFONE32                                        ; 35 cycles/32 bytes
    LDMDB   source!, {temp1,temp2,temp3,temp4}
    SUBS    count, count, #32                   ; avoid result delay
    ORR     lr, lr, temp4, LSR #8
    MOV     temp4, temp4, LSL #24
    ORR     temp4, temp4, temp3, LSR #8
    MOV     temp3, temp3, LSL #24
    ORR     temp3, temp3, temp2, LSR #8
    MOV     temp2, temp2, LSL #24
    ORR     temp2, temp2, temp1, LSR #8
    STMDB   dest!, {temp3,temp4,lr}             ; Store bytes 21-32
    STR     temp2, [dest, #-4]!                 ; STore bytes 17-20
    MOV     lr, temp1, LSL #24
    LDR     temp4, [source, #-4]!
    LDMDB   source!, {temp1,temp2,temp3}
    ORR     lr, lr, temp4, LSR #8
    MOV     temp4, temp4, LSL #24
    ORR     temp4, temp4, temp3, LSR #8
    MOV     temp3, temp3, LSL #24
    ORR     temp3, temp3, temp2, LSR #8
    MOV     temp2, temp2, LSL #24
    ORR     temp2, temp2, temp1, LSR #8
    STMDB   dest!, {temp3,temp4,lr}             ; Store bytes 5-16
    STR     temp2, [dest, #-4]!                 ; STore bytes 1-4
    MOV     lr, temp1, LSL #24
    BGE     TTH_OFFONE32

TTH_OFFONE8_TST
    ADDS    count, count, #24
    BLT     TTH_OFFONE4

TTH_OFFONE8                                         ; 11 cycles/8 bytes
    LDMDB   source!, {temp2, temp3}
    SUBS    count, count, #8
    ORR     lr, lr, temp3, LSR #8
    MOV     temp3, temp3, LSL #24
    STR     lr, [dest, #-4]!
    ORR     temp3, temp3, temp2, LSR #8
    STR     temp3, [dest, #-4]!
    MOV     lr, temp2, LSL #24
    BGE     TTH_OFFONE8

TTH_OFFONE4                                         ; 8-10 cycles/4 bytes
    ADDS    count, count, #4
    BLT     TTH_OFFONE_BYTES
    LDR     temp3, [source, #-4]!
    ORR     lr, lr, temp3, LSR #8
    STR     lr, [dest, #-4]!
    MOV     lr, temp3, LSL #24

TTH_OFFONE_BYTES                                    ; 13 cycles/1-3 bytes
    ADDLTS  count, count, #4
    BEQ     TTH_OFFONE_EXIT
    MOV     lr, lr, LSR #24
    CMP     count, #2
    STRB    lr, [dest, #-1]!
    BLT     TTH_OFFONE_EXIT
    LDRGEB  temp1, [source, #-1]!
    LDRGTB  temp2, [source, #-1]!
    STRGEB  temp1, [dest, #-1]!
    STRGTB  temp2, [dest, #-1]!

TTH_OFFONE_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}
  ENDIF

TTH_BYTEMOVE4                                       ; 12 cycles/4 bytes
    CMP     count, #4
    BLT     TTH_LAST3
    LDRB    temp1, [source, #-1]!
    LDRB    temp2, [source, #-1]!
    LDRB    temp3, [source, #-1]!
    LDRB    lr, [source, #-1]!
    SUB     count, count,   #4
    STRB    temp1, [dest,   #-1]!
    STRB    temp2, [dest,   #-1]!
    STRB    temp3, [dest,   #-1]!
    STRB    lr, [dest,   #-1]!

; Move the last 0-3 bytes
TTH_LAST3
    CMP     count, #0                               ; 2 or 5 cycles
    BEQ     TTH_BYTEMOVE_EXIT
;
;single byte moves
;
TTH_BYTEMOVE                                        ; 11 cycles/1-3 bytes
    LDRB    temp1, [source, #-1]!
    CMP     count, #2
    STRB    temp1, [dest,   #-1]!
    BLT     TTH_BYTEMOVE_EXIT
    LDRGEB  temp2, [source, #-1]!
    LDRGTB  temp3, [source, #-1]!
    STRGEB  temp2, [dest,   #-1]!
    STRGTB  temp3, [dest,   #-1]!

TTH_BYTEMOVE_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}
  ENDIF

;**********************************************************************
; Copy from head to tail to avoid source overwrite because the source 
; destination the source
;**********************************************************************
HEAD_TO_TAIL
    ;if LT 8 bytes store them and exit
    CMP     count, #8                               ; 2-3 cycles
    BLT     BYTEMOVE4

    ;Check alignment of parameters
    ANDS    temp1, dest, #3                         ; 2-3 cycles
    BEQ     SRCALIGN

    ; destination is at least 1 byte misaligned
    ; Read and write (4 - alignment) bytes to align destination.
    RSB     temp1, temp1, #4                        ; 9 cycles
    LDRB    temp2, [source], #1
    CMP     temp1, #2
    STRB    temp2, [dest],   #1
    LDRGEB  temp3, [source], #1         ; >= 2 == at least 2 bytes
    LDRGTB  temp2, [source], #1         ; > 2 == 3 bytes unaligned
    SUB     count, count, temp1
    STRGEB  temp3, [dest],   #1
    STRGTB  temp2, [dest],   #1

SRCALIGN                                            ; 3 - 7 cycles
    TST     source, #1                  ; save alignment of src
    BNE     UNALIGNED                   ; src 3 byte unaligned.
    TST     source, #2
    BNE     HWORDMOVE                   ; src and dst are hword aligned

;
;word aligned source and destination, move blocks of 32 bytes
;until we have less than 32 bytes left, then divide moves in
;half down to less than 4, where we will move the last 3 or less
;bytes
;
WORDMOVE
    SUBS    count, count, #32                       ; 2-3 cycles
    BLT     BLK16

BLK32                                               ; 20 cycles/32 bytes
    LDMIA   source!, {temp1,temp2,temp3,lr}
    STMIA   dest!,   {temp1,temp2,temp3,lr}
    LDMIA   source!, {temp1,temp2,temp3,lr}
    SUBS    count, count, #32
    STMIA   dest!,   {temp1,temp2,temp3,lr}
    BGE     BLK32

BLK16                                               ; 11-4 cycles/16 bytes
    ADDS    count, count, #16
    LDMGEIA source!, {temp1, temp2, temp3, lr}
    STMGEIA dest!,   {temp1, temp2, temp3, lr}
    BEQ     WORD_BYTES_EXIT
    SUBGTS    count, count, #16

BLK8                                                ; 6 cycles/8 bytes
    ADDS    count, count, #8
    LDMGEIA source!, {temp1, temp2}
    SUBGE   count, count, #8
    STMGEIA dest!,   {temp1, temp2}

BLK4
    ADDS    count, count, #4                        ; 6-9 cycles/4 bytes
    LDRGE   temp1, [source], #4
    STRGE   temp1, [dest], #4

WORD_BYTES
    ADDLTS  count, count, #4
    BEQ     WORD_BYTES_EXIT                         ; On zero, Return to caller

    LDR     temp1, [source], #4                     ; 10 cycles/1-3 bytes
    CMP     count, #2
    STRGEH  temp1, [dest], #2
    STRLTB  temp1, [dest], #1
    MOVGT   temp1, temp1, LSR #16
    STRGTB  temp1, [dest], #1

WORD_BYTES_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}
  ENDIF

;
; half word align source and destination
;
HWORDMOVE                                           ; 2-3 cycles
    LDRH    temp1, [source], #2
    SUBS    count, count, #32
    BLT     HWORD8_TST

HWORD32                                             ; 35 cycles/32 bytes
    LDMIA   source!, {temp2,temp3,temp4,lr}
    ORR     temp1, temp1, temp2, LSL #16
    MOV     temp2, temp2, LSR #16
    ORR     temp2, temp2, temp3, LSL #16
    MOV     temp3, temp3, LSR #16
    ORR     temp3, temp3, temp4, LSL #16
    MOV     temp4, temp4, LSR #16
    ORR     temp4, temp4, lr, LSL #16
    STMIA   dest!, {temp1,temp2,temp3,temp4}    ; Store bytes 1-16
    MOV     temp1, lr, LSR #16
    LDMIA   source!, {temp2,temp3,temp4,lr}
    ORR     temp1, temp1, temp2, LSL #16
    MOV     temp2, temp2, LSR #16
    ORR     temp2, temp2, temp3, LSL #16
    MOV     temp3, temp3, LSR #16
    ORR     temp3, temp3, temp4, LSL #16
    MOV     temp4, temp4, LSR #16
    ORR     temp4, temp4, lr, LSL #16
    STMIA   dest!, {temp1,temp2,temp3,temp4}    ; Store bytes 17-32
    SUBS    count, count, #32
    MOV     temp1, lr, LSR #16
    BGE     HWORD32

HWORD8_TST
    ADDS    count, count, #24
    BLT     HWORD4

HWORD8                                              ; 11 cycles/8 bytes
    LDMIA   source!, {temp2,temp3}
    ORR     temp1, temp1, temp2, LSL #16
    MOV     temp2, temp2, LSR #16
    ORR     temp2, temp2, temp3, LSL #16
    STMIA   dest!, {temp1, temp2}
    SUBS    count, count, #8
    MOV     temp1, temp3, LSR #16
    BGE     HWORD8

HWORD4                                              ; 3-7 cycles/4 bytes
    ADDS    count, count, #4
    BLT     HWORD_BYTES
    LDR     temp2, [source], #4
    ORR     temp1, temp1, temp2, LSL #16
    STR     temp1, [dest], #4
    MOV     temp1, temp2, LSR #16

HWORD_BYTES                                         ; 5-11 cycles/1-3 bytes
    ADDLTS  count, count, #4
    BEQ     HWORD_BYTES_EXIT                        ; On zero, Return to caller
    CMP     count, #2
    STRLTB  temp1, [dest], #1
    LDRGTB  temp2, [source], #1
    STRGEH  temp1, [dest], #2
    STRGTB  temp2, [dest], #1

HWORD_BYTES_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}
  ENDIF

;
; Unaligned Moves
;
UNALIGNED
    TST     source, #2
    BEQ     UNALIGNED1

UNALIGNED3                                          ; 3-4 cycles
    LDRB    temp1, [source], #1
    SUBS    count, count, #32
    BLT     OFFTHREE8_TST

OFFTHREE32                                          ; 35 cycles/32 bytes
    LDMIA   source!, {temp2,temp3,temp4,lr}
    ORR     temp1, temp1, temp2, LSL #8
    MOV     temp2, temp2, LSR #24
    ORR     temp2, temp2, temp3, LSL #8
    MOV     temp3, temp3, LSR #24
    ORR     temp3, temp3, temp4, LSL #8
    MOV     temp4, temp4, LSR #24
    ORR     temp4, temp4, lr, LSL #8
    STMIA   dest!, {temp1,temp2,temp3,temp4}    ; Store bytes 1-16
    MOV     temp1, lr, LSR #24
    LDMIA   source!, {temp2,temp3,temp4,lr}
    ORR     temp1, temp1, temp2, LSL #8
    MOV     temp2, temp2, LSR #24
    ORR     temp2, temp2, temp3, LSL #8
    MOV     temp3, temp3, LSR #24
    ORR     temp3, temp3, temp4, LSL #8
    MOV     temp4, temp4, LSR #24
    ORR     temp4, temp4, lr, LSL #8
    STMIA   dest!, {temp1,temp2,temp3,temp4}    ; Store bytes 17-32
    SUBS    count, count, #32
    MOV     temp1, lr, LSR #24
    BGE     OFFTHREE32

OFFTHREE8_TST
    ADDS    count, count, #24
    BLT     OFFTHREE4

OFFTHREE8                                           ; 11 cycles/8 bytes
    LDMIA   source!, {temp2,temp3}
    ORR     temp1, temp1, temp2, LSL #8
    MOV     temp2, temp2, LSR #24
    ORR     temp2, temp2, temp3, LSL #8
    STMIA   dest!, {temp1, temp2}
    SUBS    count, count, #8
    MOV     temp1, temp3, LSR #24
    BGE     OFFTHREE8

OFFTHREE4                                           ; 3-7 cycles/4 bytes
    ADDS    count, count, #4
    BLT     OFFTHREE_BYTES
    LDR     temp2, [source], #4
    ORR     temp1, temp1, temp2, LSL #8
    STR     temp1, [dest], #4
    MOV     temp1, temp2, LSR #24

OFFTHREE_BYTES                                      ; 5-12 cycles/ 1-3 bytes
    ADDLTS  count, count, #4
    BEQ     OFFTHREE_EXIT                           ; On zero, Return to caller
    CMP     count, #2
    LDRGEH  temp2, [source], #2
    STRB    temp1, [dest], #1
    STRGEB  temp2, [dest], #1
    MOVGT   temp2, temp2, LSR #8
    STRGTB  temp2, [dest], #1

OFFTHREE_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}           ; On zero, Return to caller
  ENDIF

;
; Source is one byte from word alignment.
;   Read a byte & half word then multiple words and a byte.  Then
;   shift and ORR them into consecutive words for STM writes
UNALIGNED1                                          ; 5-6 cycles
    LDRB    temp1, [source], #1
    LDRH    temp2, [source], #2
    SUBS    count, count, #32
    ORR     temp1, temp1, temp2, LSL #8
    BLT     OFFONE8_TST

OFFONE32                                            ; 35 cycles/32 bytes
    LDMIA   source!, {temp2, temp3, temp4, lr}
    ORR     temp1, temp1, temp2, LSL #24
    MOV     temp2, temp2, LSR #8
    ORR     temp2, temp2, temp3, LSL #24
    MOV     temp3, temp3, LSR #8
    ORR     temp3, temp3, temp4, LSL #24
    MOV     temp4, temp4, LSR #8
    ORR     temp4, temp4, lr, LSL #24
    STMIA   dest!, {temp1,temp2,temp3,temp4}    ; Store bytes 1-16
    MOV     temp1, lr, LSR #8
    LDMIA   source!, {temp2,temp3,temp4,lr}
    ORR     temp1, temp1, temp2, LSL #24
    MOV     temp2, temp2, LSR #8
    ORR     temp2, temp2, temp3, LSL #24
    MOV     temp3, temp3, LSR #8
    ORR     temp3, temp3, temp4, LSL #24
    MOV     temp4, temp4, LSR #8
    ORR     temp4, temp4, lr, LSL #24
    STMIA   dest!, {temp1,temp2,temp3,temp4}    ; Store bytes 17-32
    SUBS    count, count, #32
    MOV     temp1, lr, LSR #8
    BGE     OFFONE32

OFFONE8_TST
    ADDS    count, count, #24
    BLT     OFFONE4

OFFONE8                                             ; 11 cycles/8 bytes
    LDMIA   source!, {temp2,temp3}
    ORR     temp1, temp1, temp2, LSL #24
    MOV     temp2, temp2, LSR #8
    ORR     temp2, temp2, temp3, LSL #24
    STMIA   dest!, {temp1,temp2}
    SUBS    count, count, #8
    MOV     temp1, temp3, LSR #8
    BGE     OFFONE8

OFFONE4                                             ; 3-9 cycles/4 bytes
    ADDS    count, count, #4
    BLT     OFFONE_BYTES
    LDR     temp2, [source], #4
    ORR     temp1, temp1, temp2, LSL #24
    STR     temp1, [dest], #4
    BEQ     OFFONE_EXIT
    MOV     temp1, temp2, LSR #8

OFFONE_BYTES                                        ; 11 cycles/1-3 bytes
    ADDLTS  count, count, #4
    BEQ     OFFONE_EXIT
    CMP     count, #2
    STRLTB  temp1, [dest], #1
    STRGEH  temp1, [dest], #2
    MOVGT   temp1, temp1, LSR #16
    STRGTB  temp1, [dest], #1

OFFONE_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}           ; Return to caller
  ENDIF
    
BYTEMOVE4                                           ; 12 cycles/4 bytes
    CMP     count, #4
    BLT     MMOVEXIT
    LDRB    temp1, [source], #1
    SUB     count, count, #4
    LDRB    temp2, [source], #1
    LDRB    temp3, [source], #1
    LDRB    lr, [source], #1
    STRB    temp1, [dest], #1
    STRB    temp2, [dest], #1
    STRB    temp3, [dest], #1
    STRB    lr, [dest], #1

MMOVEXIT                                            ; 2-5 cycles
    CMP     count, #0
  IF Interworking :LOR: Thumbing
    LDMEQIA sp!, {dest, temp2, temp3, lr}
    BXEQ    lr
  ELSE
    LDMEQIA sp!, {dest, temp2, temp3, pc}           ; On zero, Return to caller
  ENDIF

;
; Store last 3 or so bytes and exit
;
BYTEMOVE                                            ; 4-7 cycles/1 byte
    LDRB    temp1, [source], #1
    CMP     count, #2
    STRB    temp1, [dest], #1
    BLT     BYTEMOVE_EXIT
    LDRGEB  temp2, [source], #1                     ; 8 cycles/1-2 bytes
    LDRGTB  temp3, [source], #1
    STRGEB  temp2, [dest], #1
    STRGTB  temp3, [dest], #1

BYTEMOVE_EXIT

  IF Interworking :LOR: Thumbing
    LDMIA   sp!, {dest, temp2, temp3, lr}
    BX      lr
  ELSE
    LDMIA   sp!, {dest, temp2, temp3, pc}           ; Return to caller
  ENDIF

    ENTRY_END memmove

    END
