;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Microsoft Research Singularity
;;; 
;;; Copyright (c) Microsoft Corporation.  All rights reserved.
;;;
;;; This file contains ARM-specific assembly code.
;;;

;**********************************************************************
; void *
; memcpy( void *dest, const void *src, size_t count );
;   The memcpy function copies count bytes of src to dest. 
;   If the source and destination overlap, this function does 
;   not ensure that the original source bytes in the overlapping 
;   region are copied before being overwritten. Use memmove to 
;   handle overlapping regions.
;
;**********************************************************************

        OPT     2       ; disable listing
        INCLUDE kxarm.inc
        OPT     1       ; reenable listing

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

    NESTED_ENTRY memcpy

	ROUT

  IF Thumbing
; Switch from Thumb mode to ARM mode
	DCW     0x4778              ; bx pc
	DCW     0x46C0              ; nop
  ENDIF

	;//Save registers onto the stack
    STMDB   sp!, {dest,temp2,temp3,lr}  ; save registers

	PROLOG_END

; Use a threshold to determine which code to use:
;
;   if destination & source are naturally aligned, then
;     threshold = 512
;   else
;     threshold = 128
;
;   if copy size > threshold, then
;     use memcpybigblk
;   else
;     use .NET code

    ORR     temp1, dest, source
    TST     temp1, #3
    MOVEQ   temp1, #512
    MOVNE   temp1, #128
    CMP     count, temp1
    BHI     UNDO_PROLOG    ; revert and continue to memcpybigblk

; NOTE: UNDO_PROLOG just restores SP, so do NOT modify anything other
;       than r3 (temp1) and r12 (temp4) before this point

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


; THIS IS NOT A RETURN
; The following reverts the stack to its state at the point of entry
; of memcpy.  It then falls through to memcpybigblk to perform the
; large copy
UNDO_PROLOG
	ADD     sp, sp, #0x10
;
; FALLTHRU
;
    ENTRY_END memcpy


    NESTED_ENTRY memcpybigblk

	ROUT

	;//Save registers onto the stack
	;//R3 should be OK to destroy.  If not, we stack it off too.
	stmfd 	sp!, {r0,r4-r11, lr}

	PROLOG_END

prefetch_setup
;//Prefetch the source.
;//Have to align source register with word boundary first
	mov 	r5, r1
	and		r5, r5, #~0x3
	
;//The PLD instruction just happens to be a Never Execute on ARM V4,
;//so we can in-line the PLD instruction and still maintain V4 compatibility
;//        0x0000000c:    f5d5f000    ....    PLD      [r5,#0]
;//        0x00000010:    f5d5f020     ...    PLD      [r5,#0x20]
;//        0x00000014:    f5d5f040    @...    PLD      [r5,#0x40]
	DCD		0xf5d5f000
	DCD		0xf5d5f020
	DCD		0xf5d5f040
	
;//If there are 4 or less bytes to copy, we just jump to the end
;//and do a straight byte copy.
	cmp 	r2, #4
	bls 	finish

;//Align the destination to a word boundary.
	rsb		r4, r0, #0				;//Figure out how many bytes
	ands	r4, r4, #0x2			;//See if we need to do 2 copies
	ldrneb 	r5, [r1], #1			;//Read the two bytes
	ldrneb	r6, [r1], #1
	subne	r2, r2, #2				;//Decrement count by 2
	strneb	r5, [r0], #1			;//Now store the two bytes
	strneb  r6, [r0], #1			;//Have to do two seperate byte stores 
									;//because of possible address misalignment

	ands 	r4, r0, #0x1			;//See if we need to do 1 copy
	ldrneb	r5, [r1], #1			;//Load the single byte
	subne	r2, r2, #1				;//Decrement count by 1
	strneb	r5, [r0], #1			;//Store the single byte

;//We need to choose which memcpy we use based
;//on how the source is now aligned.  If the destination and source
;//are both aligned, then we fall through to the aligned copy

;//Check the byte alignment of the source
;//We do it in reverse order just because.  If most memcopies are
;//expected to be off by a certain #, that should be placed first.
	and		r3, r1, #3
	cmp 	r3, #3						;//If both bits are set, go do case 3, off by 3 bytes
	beq		memcpyoffby3				;//Goto case 3
	cmp		r3, #2						;//Check for case 2, off by 2 bytes
	beq		memcpyoffby2				;//Goto case 2
	cmp		r3, #1						;//Check for case 1, off by 1 byte
	beq		memcpyoffby1				;//Goto case 1

;//The source and destination are word aligned.  We get an easy job.
memcpyoffby0

;//Now we need to align the destination to a cache line boundary
;//We need to figure out how many words are needed to align it.
;//If the number of words to align it are less than the number of words
;//we're asked to copy, just copy the required number of words.
	and		r4, r0, #0x1C				;//Grab the low bits of the destination
	rsb		r4, r4, #32					;//Negate them and
										;//add 32 to the low bits(this is  
										;//how many we need to move to get aligned)
 	and		r5, r2, #0x1C				;//Check only the number of words from count
	cmp		r4, r2	 					;//Compare low bits to align against the words from count
	movhi	r4, r5						;//If words to align is greater than the count, then
										;//use the words from count instead

	cmp		r4, #0
	beq		offby0mainloop

;//r4 now contains the number of times we need to do a word load/store
;//So we need to sortof back-calculate how many of the word load/stores to
;//skip in memcpyoffby0cachelinealignload/store
	rsb 	r3, r4, #32
	and		r3, r3, #0x1C
;//r3 now contains the number of *instructions* to skip over.

;//Deduct words from size
	sub 	r2, r2, r4
		
;//Because the & 0x1C corresponds to words, we don't have to shift anything
;//when we jump into load table
;//Using two jump tables is faster because it gives the processor a chance to load
;//data before we try to store it out.
	adr 	r12, offby0cachelinealignload
	add 	pc, r12, r3

offby0cachelinealignload				;//Need to have up to 8 words (1 cache line)
	ldr 	r4, [r1], #4				;//Could also do load/store pairs, and shift
	ldr 	r5, [r1], #4				;//r3 left 1 bit to calculate jump address
	ldr 	r6, [r1], #4
	ldr 	r7, [r1], #4
	ldr 	r8, [r1], #4
	ldr 	r9, [r1], #4
	ldr 	r10,[r1], #4
	ldr 	r11,[r1], #4

;//Now jump into the store table
	adr 	r12, offby0cachelinealignstore
	add		pc, r12, r3

offby0cachelinealignstore
	str		r4, [r0], #4
	str		r5, [r0], #4
	str		r6, [r0], #4
	str		r7, [r0], #4
	str		r8, [r0], #4
	str		r9, [r0], #4
	str		r10,[r0], #4
	str		r11,[r0], #4

;//We are now cache line aligned. 
;//We loop around doing prefetches and copies based on how far ahead we want to look

offby0mainloop
	cmp 	r2, #(32*3 + 32)			;//Only keep looking ahead by 4 cache lines
	bmi 	offby0endofmainloop
	
;//Preload the data
;//        0x000000f4:    f5d1f060    `...    PLD      [r1,#0x60]
;//        0x000000f8:    f5d1f080    ....    PLD      [r1,#0x80]

	DCD		0xf5d1f060
	DCD		0xf5d1f080

;//Here is the main loop that handles pipelining the loads
	
	ldmia	r1!, {r4-r11}
	stmia	r0!, {r4-r11}

	ldmia	r1!, {r4-r11}
	stmia	r0!, {r4-r11}
	
	sub		r2, r2, #64					;//Take 64 bytes off of count
	
	b 		offby0mainloop
	
offby0endofmainloop	
;//If we still have more than 32*4 words to move, do one more preload
	cmp		r2, #32*4
	bls		offby0nopreload
;//        0x0000011c:    f5d1f080    ....    PLD      [r1,#0x80]
	DCD		0xf5d1f080
	
offby0nopreload

;//Now we finish up the copy without any preloads.  The data should have already
;//been loaded into the caches
;//Copy 32 bytes at a time
offby0finishcachelines
	cmp 	r2, #32
	bmi		offby0endoffinishcachelines

	ldmia	r1!, {r4-r11}
	stmia	r0!, {r4-r11}
	
	sub		r2, r2, #32					;//Take 32 bytes off of count
	b		offby0finishcachelines

offby0endoffinishcachelines

;//Now we need to finish off any partial cache lines that may be left. We do a similar
;//algorithm to the cachelinealign loop above.
	ands	r3, r2, #0x1C				;//Get number of words left
	beq		finish						;//If words left==0, then branch to finish
	sub		r2, r2, r3					;//Subtract words left from count
	rsb		r3, r3, #32					;//Get 32-number of words left
	
	adr		r12, offby0finishload		;//That's the instructions to skip
	add 	pc, r12, r3

offby0finishload						;//Need to have up to 8 words (1 cache line)
	ldr 	r4, [r1], #4				;//Could also do load/store pairs, and shift
	ldr 	r5, [r1], #4				;//r3 left 1 bit to calculate jump address
	ldr 	r6, [r1], #4
	ldr 	r7, [r1], #4
	ldr 	r8, [r1], #4
	ldr 	r9, [r1], #4
	ldr 	r10,[r1], #4
	ldr 	r11,[r1], #4

;//Now jump into the store table
	adr 	r12, offby0finishstore
	add		pc, r12, r3

offby0finishstore
	str		r4, [r0], #4
	str		r5, [r0], #4
	str		r6, [r0], #4
	str		r7, [r0], #4
	str		r8, [r0], #4
	str		r9, [r0], #4
	str		r10,[r0], #4
	str		r11,[r0], #4

;//Copy the last 4 bytes, if necessary
	rsb		r2, r2, #4					;//Find how many bytes to copy (0, 1,2,3, or 4)
	adr 	r12, finishloadby0
	add		pc, r12, r2, LSL #2			;//Need to shift r2 left by 2 bits to jump instructions

finishloadby0
	ldrb		r3, [r1], #1
	ldrb		r4, [r1], #1 
	ldrb		r5, [r1], #1
	ldrb		r6, [r1], #1
	
	adr		r12, finishstoreby0
	add		pc, r12, r2, LSL #2

finishstoreby0
	strb		r3, [r0], #1
	strb		r4, [r0], #1
	strb		r5, [r0], #1
	strb		r6, [r0], #1

;//Return to calling function
    IF Interworking :LOR: Thumbing
        ldmfd sp!, {r0,r4-r11, lr}
        bx      lr
    ELSE
        ldmfd sp!, {r0,r4-r11, pc}
    ENDIF


;//The source and destination are not aligned.  We're going to have 
;//to load and shift data from a temporary buffer.  Stuff needs to be 
;//shifted to the right by 8 bits to align properly
memcpyoffby1

;//First we need to word align the source
	and 	r3, r1, #~0x3
;//Load the first value into the holding buffer (lr)
	ldr		lr, [r3], #4
	mov		lr, lr, LSR #8

;//Now we need to align the destination to a cache line boundary
;//We need to figure out how many words are needed to align it.
;//If the number of words to align it are less than the number of words
;//we're asked to copy, just copy the required number of words.
	and		r4, r0, #0x1C				;//Grab the low bits of the destination
	rsb		r4, r4, #32					;//Negate them
										;//Add 32 to the low bits(this is  
										;//how many we need to move to get aligned)
 	and		r5, r2, #0x1C				;//Check only the number of words from count
	cmp		r4, r2	 					;//Compare low bits to align against the words from count
	movhi	r4, r5						;//If words to align is greater than the count, then
										;//use the words from count instead

	cmp		r4, #0
	beq		offby1mainloop
;//r4 now contains the number of times we need to do a word load/store
;//So we need to sortof back-calculate how many of the word load/stores to
;//skip in memcpyoffby1cachelinealignload
	rsb 	r6, r4, #32
	and		r6, r6, #0x1C
;//r3 now contains the number of *words* to skip over.

;//Deduct words from size
	sub 	r2, r2, r4
		
;//Because the & 0x1C corresponds to words, we DO need to shift this time around
;//when we jump into load table
	adr 	r12, offby1cachelinealignload
	add 	pc, r12, r6, LSL #2			;//Allows 4 instructions per byteblit

;//Because there is no convenient way to split the load/store into multiples of 2
;//unless we keep them together, for misaligned data we leave them together.
offby1cachelinealignload				;//Need to have up to 8 words (1 cache line)
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
;//We are now cache line aligned.
;//We loop around doing prefetches and copies based on how far ahead we want to look
offby1mainloop
	cmp 	r2, #(32*4 + 32)			;//Only keep looking ahead by 4 cache lines
	bmi 	offby1endofmainloop
	
;//Preload		
;//        0x00000264:    f5d3f060    `...    PLD      [r3,#0x60]
;//        0x00000268:    f5d3f080    ....    PLD      [r3,#0x80]
	DCD		0xf5d3f060
	DCD		0xf5d3f080
	
;//Here is the main loop that handles pipelining the loads for off by 1
	ldmia	r3!, {r4, r5, r6, r7, r8, r9, r10, r11}
	
	orr		r1,lr, r4, LSL #24
	mov		lr, r4, LSR #8
	
	orr		r4, lr, r5, LSL #24
	mov		lr, r5, LSR #8

	orr		r5, lr, r6, LSL #24
	mov		lr, r6, LSR #8

	orr		r6, lr, r7, LSL #24
	mov		lr, r7, LSR #8

	orr		r7, lr, r8, LSL #24
	mov		lr, r8, LSR #8

	orr		r8, lr, r9, LSL #24
	mov		lr, r9, LSR #8

	orr		r9, lr, r10, LSL #24
	mov		lr, r10, LSR #8

	orr		r10, lr, r11, LSL #24
	mov		lr, r11, LSR #8

	stmia	r0!, {r1, r4, r5, r6, r7, r8, r9, r10}

	ldmia	r3!, {r4, r5, r6, r7, r8, r9, r10, r11}

	orr		r1,lr, r4, LSL #24
	mov		lr, r4, LSR #8
	
	orr		r4, lr, r5, LSL #24
	mov		lr, r5, LSR #8

	orr		r5, lr, r6, LSL #24
	mov		lr, r6, LSR #8

	orr		r6, lr, r7, LSL #24
	mov		lr, r7, LSR #8

	orr		r7, lr, r8, LSL #24
	mov		lr, r8, LSR #8

	orr		r8, lr, r9, LSL #24
	mov		lr, r9, LSR #8

	orr		r9, lr, r10, LSL #24
	mov		lr, r10, LSR #8

	orr		r10, lr, r11, LSL #24
	mov		lr, r11, LSR #8

	stmia	r0!, {r1, r4, r5, r6, r7, r8, r9, r10}

	sub		r2, r2, #64					;//Take 64 bytes off of count

	b 		offby1mainloop

offby1endofmainloop	
;//If we still have more than 32*4 words to move, do one more preload
	cmp		r2, #32*4
	bls		offby1nopreload
;//        0x00000338:    f5d3f080    ....    PLD      [r3,#0x80]
	DCD		0xf5d3f080

offby1nopreload

;//Now we finish up the copy without any preloads.  The data should have alread
;//been loaded into the caches
;//Copy 32 bytes at a time
offby1finishcachelines
	cmp 	r2, #32
	bmi		offby1endoffinishcachelines
	
	ldmia	r3!, {r4, r5, r6, r7, r8, r9, r10, r11}
	
	orr		r1,lr, r4, LSL #24
	mov		lr, r4, LSR #8
	
	orr		r4, lr, r5, LSL #24
	mov		lr, r5, LSR #8

	orr		r5, lr, r6, LSL #24
	mov		lr, r6, LSR #8

	orr		r6, lr, r7, LSL #24
	mov		lr, r7, LSR #8

	orr		r7, lr, r8, LSL #24
	mov		lr, r8, LSR #8

	orr		r8, lr, r9, LSL #24
	mov		lr, r9, LSR #8

	orr		r9, lr, r10, LSL #24
	mov		lr, r10, LSR #8

	orr		r10, lr, r11, LSL #24
	mov		lr, r11, LSR #8

	stmia	r0!, {r1, r4, r5, r6, r7, r8, r9, r10}
		
	sub		r2, r2, #32					;//Take 32 bytes off of count
	b		offby1finishcachelines

offby1endoffinishcachelines

;//Now we need to finish off any partial cache lines that may be left. We do a similar
;//algorithm to the cachelinealign loop above.
	ands	r6, r2, #0x1C				;//Get number of words left
	subeq	r1, r3, #3					;//Realign source on exact byte if need to branch
	beq		finish						;//If words left==0, then branch to finish
	sub		r2, r2, r6					;//Subtract words left from count
	rsb		r6, r6, #32					;//Get 32-number of words left
	
	adr		r12, offby1finishload		;//That's the copies to skip
	add 	pc, r12, r6, LSL #2			;//..but need to multiply by 4 to get instructions

offby1finishload				;//Need to have up to 8 words (1 cache line)
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #24
	str 	r12,[r0], #4
	mov		lr, r4, LSR #8

	sub		r1, r3, #3					;//Realign source on exact byte
	
;//Copy the last 4 bytes, if necessary
	rsb		r2, r2, #4					;//Find how many bytes to copy (1,2,3, or 4)
	adr 	r12, finishloadby1
	add		pc, r12, r2, LSL #2			;//Need to shift r2 left by 2 bits to jump instructions

finishloadby1
	ldrb		r3, [r1], #1
	ldrb		r4, [r1], #1 
	ldrb		r5, [r1], #1
	ldrb		r6, [r1], #1
	
	adr		r12, finishstoreby1
	add		pc, r12, r2, LSL #2
	
finishstoreby1
	strb		r3, [r0], #1
	strb		r4, [r0], #1
	strb		r5, [r0], #1
	strb		r6, [r0], #1

;//Return to calling function
    IF Interworking :LOR: Thumbing
        ldmfd sp!, {r0,r4-r11, lr}
        bx      lr
    ELSE
        ldmfd sp!, {r0,r4-r11, pc}
    ENDIF
	
;//The source and destination are not aligned.  We're going to have to load
;//and shift data from a temporary buffer.  Stuff needs to be shifted to the
;//right by 16 bits to align properly
memcpyoffby2

;//First we need to word align the source
	and 	r3, r1, #~0x3
;//Load the first value into the holding buffer (lr)
	ldr		lr, [r3], #4
	mov		lr, lr, LSR #16

;//Now we need to align the destination to a cache line boundary
;//We need to figure out how many words are needed to align it.
;//If the number of words to align it are less than the number of words
;//we're asked to copy, just copy the required number of words.
	and		r4, r0, #0x1C				;//Grab the low bits of the destination
	rsb		r4, r4, #32					;//Negate them
										;//Add 32 to the low bits(this is  
										;//how many we need to move to get aligned)
 	and		r5, r2, #0x1C				;//Check only the number of words from count
	cmp		r4, r2	 					;//Compare low bits to align against the words from count
	movhi	r4, r5						;//If words to align is greater than the count, then
										;//use the words from count instead

	cmp		r4, #0
	beq		offby2mainloop

;//r4 now contains the number of times we need to do a word load/store
;//So we need to sortof back-calculate how many of the word load/stores to
;//skip in memcpyoffby2cachelinealignload
	rsb 	r6, r4, #32
	and		r6, r6, #0x1C
;//r3 now contains the number of *words* to skip over.

;//Deduct words from size
	sub 	r2, r2, r4
		
;//Because the & 0x1C corresponds to words, we DO need to shift this time around
;//when we jump into load table
	adr 	r12, offby2cachelinealignload
	add 	pc, r12, r6, LSL #2			;//Allows 4 instructions per byteblit

;//Because there is no convenient way to split the load/store into multiples of 2
;//unless we keep them together, for misaligned data we leave them together.
offby2cachelinealignload				;//Need to have up to 8 words (1 cache line)
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
;//So in theory we should now be cache line aligned.
;//We loop around doing prefetches and copies based on how far ahead we want to look
offby2mainloop
	cmp 	r2, #(32*4 + 32)			;//Only keep looking ahead by 4 cache lines
	bmi 	offby2endofmainloop
	
;//Preload
;//        0x00000514:    f5d3f060    `...    PLD      [r3,#0x60]
;//        0x00000518:    f5d3f080    ....    PLD      [r3,#0x80]
	DCD		0xf5d3f060
	DCD		0xf5d3f080

;//Here is the main loop that handles pipelining the loads for off by 2
	ldmia	r3!, {r4, r5, r6, r7, r8, r9, r10, r11}
	
	orr		r1,lr, r4, LSL #16
	mov		lr, r4, LSR #16
	
	orr		r4, lr, r5, LSL #16
	mov		lr, r5, LSR #16

	orr		r5, lr, r6, LSL #16
	mov		lr, r6, LSR #16

	orr		r6, lr, r7, LSL #16
	mov		lr, r7, LSR #16

	orr		r7, lr, r8, LSL #16
	mov		lr, r8, LSR #16

	orr		r8, lr, r9, LSL #16
	mov		lr, r9, LSR #16

	orr		r9, lr, r10, LSL #16
	mov		lr, r10, LSR #16

	orr		r10, lr, r11, LSL #16
	mov		lr, r11, LSR #16

	stmia	r0!, {r1, r4, r5, r6, r7, r8, r9, r10}

	ldmia	r3!, {r4, r5, r6, r7, r8, r9, r10, r11}

	orr		r1,lr, r4, LSL #16
	mov		lr, r4, LSR #16
	
	orr		r4, lr, r5, LSL #16
	mov		lr, r5, LSR #16

	orr		r5, lr, r6, LSL #16
	mov		lr, r6, LSR #16

	orr		r6, lr, r7, LSL #16
	mov		lr, r7, LSR #16

	orr		r7, lr, r8, LSL #16
	mov		lr, r8, LSR #16

	orr		r8, lr, r9, LSL #16
	mov		lr, r9, LSR #16

	orr		r9, lr, r10, LSL #16
	mov		lr, r10, LSR #16

	orr		r10, lr, r11, LSL #16
	mov		lr, r11, LSR #16

	stmia	r0!, {r1, r4, r5, r6, r7, r8, r9, r10}

	sub		r2, r2, #64					;//Take 64 bytes off of count
	b 		offby2mainloop
	
offby2endofmainloop	
;//If we still have more than 32*4 words to move, do one more preload
	cmp		r2, #32*4
	bls		offby2nopreload
;//        0x000005e8:    f5d3f080    ....    PLD      [r3,#0x80]
	DCD		0xf5d3f080

offby2nopreload

;//Now we finish up the copy without any preloads.  The data should have already
;//been loaded into the caches
;//Copy 32 bytes at a time
offby2finishcachelines
	cmp 	r2, #32
	bmi		offby2endoffinishcachelines

	ldmia	r3!, {r4, r5, r6, r7, r8, r9, r10, r11}

	orr		r1,lr, r4, LSL #16
	mov		lr, r4, LSR #16
	
	orr		r4, lr, r5, LSL #16
	mov		lr, r5, LSR #16

	orr		r5, lr, r6, LSL #16
	mov		lr, r6, LSR #16

	orr		r6, lr, r7, LSL #16
	mov		lr, r7, LSR #16

	orr		r7, lr, r8, LSL #16
	mov		lr, r8, LSR #16

	orr		r8, lr, r9, LSL #16
	mov		lr, r9, LSR #16

	orr		r9, lr, r10, LSL #16
	mov		lr, r10, LSR #16

	orr		r10, lr, r11, LSL #16
	mov		lr, r11, LSR #16

	stmia	r0!, {r1, r4, r5, r6, r7, r8, r9, r10}
		
	sub		r2, r2, #32					;//Take 32 bytes off of count
	b		offby2finishcachelines

offby2endoffinishcachelines

;//Now we need to finish off any partial cache lines that may be left. We do a similar
;//algorithm to the cachelinealign loop above.
	ands		r6, r2, #0x1C			;//Get number of words left
	subeq	r1, r3, #2					;//Realign source on exact byte if need to branch
	beq		finish						;//If words left==0, then branch to finish
	sub		r2, r2, r6					;//Subtract words left from count
	rsb		r6, r6, #32					;//Get 32-number of words left
	
	adr		r12, offby2finishload		;//That's the copies to skip
	add 	pc, r12, r6, LSL #2			;//..but need to multiply by 4 to get instructions

offby2finishload				;//Need to have up to 8 words (1 cache line)
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #16
	str 	r12,[r0], #4
	mov		lr, r4, LSR #16

	sub		r1, r3, #2					;//Realign source on exact byte
	
;//Copy the last 4 bytes, if necessary
	rsb		r2, r2, #4					;//Find how many bytes to copy (1,2,3, or 4)
	adr 	r12, finishloadby2
	add		pc, r12, r2, LSL #2			;//Need to shift r2 left by 2 bits to jump instructions

finishloadby2
	ldrb		r3, [r1], #1
	ldrb		r4, [r1], #1 
	ldrb		r5, [r1], #1
	ldrb		r6, [r1], #1
	
	adr		r12, finishstoreby2
	add		pc, r12, r2, LSL #2
	
finishstoreby2
	strb		r3, [r0], #1
	strb		r4, [r0], #1
	strb		r5, [r0], #1
	strb		r6, [r0], #1
		
;//Return to calling function
    IF Interworking :LOR: Thumbing
        ldmfd sp!, {r0,r4-r11, lr}
        bx      lr
    ELSE
        ldmfd sp!, {r0,r4-r11, pc}
    ENDIF

;//The source and destination are not aligned.  We're going to have to load
;//and shift data from a temporary buffer.  Stuff needs to be shifted to the
;//right by 24 bits to align properly
memcpyoffby3

;//First we need to word align the source
	and 	r3, r1, #~0x3
;//Load the first value into the holding buffer (lr)
	ldr		lr, [r3], #4
	mov		lr, lr, LSR #24
	

;//Now we need to align the destination to a cache line boundary
;//We need to figure out how many words are needed to align it.
;//If the number of words to align it are less than the number of words
;//we're asked to copy, just copy the required number of words.
	and		r4, r0, #0x1C				;//Grab the low bits of the destination
	rsb		r4, r4, #32					;//Negate them
										;//Add 32 to the low bits(this is  
										;//how many we need to move to get aligned)
 	and		r5, r2, #0x1C				;//Check only the number of words from count
	cmp		r4, r2	 					;//Compare low bits to align against the words from count
	movhi	r4, r5						;//If words to align is greater than the count, then
										;//use the words from count instead

	cmp		r4, #0
	beq		offby3mainloop

;//r4 now contains the number of times we need to do a word load/store
;//So we need to sortof back-calculate how many of the word load/stores to
;//skip in memcpyoffby3cachelinealignload
	rsb 	r6, r4, #32
	and		r6, r6, #0x1C
;//r3 now contains the number of *words* to skip over.

;//Deduct words from size
	sub 	r2, r2, r4
		
;//Because the & 0x1C corresponds to words, we DO need to shift this time around
;//when we jump into load table
	adr 	r12, offby3cachelinealignload
	add 	pc, r12, r6, LSL #2			;//Allows 4 instructions per byteblit

;//Because there is no convenient way to split the load/store into multiples of 2
;//unless we keep them together, for misaligned data we leave them together.
offby3cachelinealignload				;//Need to have up to 8 words (1 cache line)
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
;//So in theory we should now be cache line aligned.
;//We loop around doing prefetches and copies based on how far ahead we want to look
offby3mainloop
	cmp 	r2, #(32*4 + 32)			;//Only keep looking ahead by 4 cache lines
	bmi 	offby3endofmainloop
	
;//Preload
;//        0x000007c4:    f5d3f060    `...    PLD      [r3,#0x60]
;//        0x000007c8:    f5d3f080    ....    PLD      [r3,#0x80]
	DCD		0xf5d3f060
	DCD		0xf5d3f080

;//Here is the main loop that handles pipelining the loads for off by 1
	ldmia	r3!, {r4, r5, r6, r7, r8, r9, r10, r11}
	
	orr		r1,lr, r4, LSL #8
	mov		lr, r4, LSR #24

	orr		r4, lr, r5, LSL #8
	mov		lr, r5, LSR #24

	orr		r5, lr, r6, LSL #8
	mov		lr, r6, LSR #24

	orr		r6, lr, r7, LSL #8
	mov		lr, r7, LSR #24

	orr		r7, lr, r8, LSL #8
	mov		lr, r8, LSR #24

	orr		r8, lr, r9, LSL #8
	mov		lr, r9, LSR #24

	orr		r9, lr, r10, LSL #8
	mov		lr, r10, LSR #24

	orr		r10, lr, r11, LSL #8
	mov		lr, r11, LSR #24

	stmia	r0!, {r1, r4, r5, r6, r7, r8, r9, r10}

	ldmia	r3!, {r4, r5, r6, r7, r8, r9, r10, r11}

	orr		r1,lr, r4, LSL #8
	mov		lr, r4, LSR #24
	
	orr		r4, lr, r5, LSL #8
	mov		lr, r5, LSR #24

	orr		r5, lr, r6, LSL #8
	mov		lr, r6, LSR #24

	orr		r6, lr, r7, LSL #8
	mov		lr, r7, LSR #24

	orr		r7, lr, r8, LSL #8
	mov		lr, r8, LSR #24

	orr		r8, lr, r9, LSL #8
	mov		lr, r9, LSR #24

	orr		r9, lr, r10, LSL #8
	mov		lr, r10, LSR #24

	orr		r10, lr, r11, LSL #8
	mov		lr, r11, LSR #24

	stmia	r0!, {r1, r4, r5, r6, r7, r8, r9, r10}

	sub		r2, r2, #64					;//Take 64 bytes off of count
	b 		offby3mainloop
	
offby3endofmainloop	
;//If we still have more than 32*4 words to move, do one more preload
	cmp		r2, #32*4
	bls		offby3nopreload
;//        0x00000898:    f5d3f080    ....    PLD      [r3,#0x80]
	DCD		0xf5d3f080

offby3nopreload

;//Now we finish up the copy without any preloads.  The data should have alread
;//been loaded into the caches
;//Copy 32 bytes at a time
offby3finishcachelines
	cmp 	r2, #32
	bmi		offby3endoffinishcachelines
	
	ldmia	r3!, {r4, r5, r6, r7, r8, r9, r10, r11}

	orr		r1,lr, r4, LSL #8
	mov		lr, r4, LSR #24
	
	orr		r4, lr, r5, LSL #8
	mov		lr, r5, LSR #24

	orr		r5, lr, r6, LSL #8
	mov		lr, r6, LSR #24

	orr		r6, lr, r7, LSL #8
	mov		lr, r7, LSR #24

	orr		r7, lr, r8, LSL #8
	mov		lr, r8, LSR #24

	orr		r8, lr, r9, LSL #8
	mov		lr, r9, LSR #24

	orr		r9, lr, r10, LSL #8
	mov		lr, r10, LSR #24

	orr		r10, lr, r11, LSL #8
	mov		lr, r11, LSR #24

	stmia	r0!, {r1, r4, r5, r6, r7, r8, r9, r10}
		
	sub		r2, r2, #32					;//Take 32 bytes off of count
	b		offby3finishcachelines

offby3endoffinishcachelines

;//Now we need to finish off any partial cache lines that may be left. We do a similar
;//algorithm to the cachelinealign loop above.
	ands		r6, r2, #0x1C			;//Get number of words left
	subeq	r1, r3, #1					;//Realign source on exact byte if need to branch
	beq		finish						;//If words left==0, then branch to finish
	sub		r2, r2, r6					;//Subtract words left from count
	rsb		r6, r6, #32					;//Get 32-number of words left
	
	adr		r12, offby3finishload		;//That's the copies to skip
	add 	pc, r12, r6, LSL #2			;//..but need to multiply by 4 to get instructions

offby3finishload						;//Need to have up to 8 words (1 cache line)
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24
		
	ldr 	r4, [r3], #4
	orr		r12,lr, r4, LSL #8
	str 	r12,[r0], #4
	mov		lr, r4, LSR #24

	sub		r1, r3, #1					;//Realign source on exact byte
	
;//	b finish							;//Not needed, just fall through

;//Copy the last 4 bytes, if necessary
finish									;//This finish also used in < 4 bytes case
	rsb		r2, r2, #4					;//Find how many bytes to copy (1,2,3, or 4)
	adr 	r12, finishloadby3
	add		pc, r12, r2, LSL #2			;//Need to shift r2 left by 2 bits to jump instructions

finishloadby3
	ldrb		r3, [r1], #1
	ldrb		r4, [r1], #1 
	ldrb		r5, [r1], #1
	ldrb		r6, [r1], #1
	
	adr		r12, finishstoreby3
	add		pc, r12, r2, LSL #2
	
finishstoreby3
	strb		r3, [r0], #1
	strb		r4, [r0], #1
	strb		r5, [r0], #1
	strb		r6, [r0], #1
		
;//Return to calling function
    IF Interworking :LOR: Thumbing
	ldmfd sp!, {r0,r4-r11, lr}
	bx      lr
    ELSE
	ldmfd sp!, {r0,r4-r11, pc}
    ENDIF


    ENTRY_END memcpybigblk
	
    END

