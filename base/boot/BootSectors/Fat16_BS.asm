;; ----------------------------------------------------------------------------
;;
;;  Copyright (c) Microsoft Corporation.  All rights reserved.
;;
;; ----------------------------------------------------------------------------

;;;;;;;;;;;;;;;;;;;;
; Concerns
;  1 - there is no error checking on the int13 calls
;  2 - we assume that the disk is FAT16, and that the parameters in the BPB are correct.

;;;;;;;;;;;;;;;;;;;;
; Constants

BootSecOrigin       EQU     07c00h      ; the BIOS always puts the boot sector here
EndOfClusterMarker  EQU     0FFF8h      ; End of cluster is here or higher

; a little trickery here:  Inside the Boot Sector data structure, there several bytes that we never use.
; whether the real file system uses them or not, we don't need them, and we could use the space for locals.

FirstDataSector     EQU     OemName
RootDirSectors      EQU     OemName+2
RootDirStart        EQU     OemName+4
LBAStart            EQU     SerialNum

;;;;;;;;;;;;;;;;;;;;
; Directives

.model tiny
.686p

;;;;;;;;;;;;;;;;;;;;
; Begin Code segment

_TEXT SEGMENT use16 ; 16-bit code segment
.code
ORG     0h                          ; BIOS puts us at 07c0h:0000

start:

    ; standard boot loader proceedure is to jump over the BPB and BS data structures, then nop
    jmp short bootloader
    nop

;;; Example BPB and BS for Singularity, assuming a 64MB disk.  Installers must NEVER copy these 59 bytes - use what the HD has...
BPB:
    OemName         DW      'IS'    ; setting up the first 8 bytes like this lets us address them via the hack above
                    DB      'NGULAR'
    BytesPerSector  DW      512
    SecsPerClust    DB      4
    ReservedSecs    DW      1
    NumFats         DB      2
    RootDirEntries  DW      512
    TotalSectors    DW      0
    MediaByte       DB      0F8H
    NumFatSecs      DW      128
    SecPerTrack     DW      011h
    NumHeads        DW      08h
    HiddenSecs      DD      011h
    BigTotalSecs    DD      1ff87h
    BootDrv         DB      80h
    BSReserved1     DB      0h
    ExtBootSig      DB      41
    SerialNum       DD      0
    VolumeLabel     DB      'SINGULARITY'
    FatId           DB      'FAT16   '

bootloader:

    db      0eah                    ; jmp far
    dw      OFFSET Step1            ; offset
    dw      007c0h                  ; segment
        
Step1:    ; set CS,DS,SS,ES segments to 07c0h, set stack to 07c0h:0400h
    mov     cx, cs
    mov     ss, cx
    mov     sp, 0400h
    mov     es, cx
    mov     ds, cx
    mov     bp, sp

Step2:    ; Clear the Screen
    mov     ax, 02h
    int     010h

Step3:    ; Save the boot drive
    mov     [BootDrv], dl

Step4:    ; Ensure Int13X is supported.  (It's the only way we'll access the HD)
    mov     ax, 4100h
    mov     bx, 055aah              ; required parameter
   
    int     13h                     ; check availability of extended int 13 (dl holds BootDrv)

    jc      HWUnsupportedError      ; CF is set on error
    cmp     bx,0aa55h
    jne     HWUnsupportedError      ; BX != 0xaa55 on error
    test    cl,1
    jz      HWUnsupportedError      ; bit 0 off on error

Step5:    ; Find the first FAT16 partition in the MBR and store the starting LBA offset.
    xor     eax, eax
    mov     bx, 4000h
    mov     es, bx
    mov     cx, 1
    call    ReadDisk                ; load the MBR to 4000:0000

    mov     cx, 4                   ; check up to 4 entries in the partition table
    mov     di, 446                 ; the offset of the table within the MBR

    mov     eax, 00eh               ; 00eh is the signature for a Fat16 LBA-accessible partition
FindFat16Partition:
    cmp     al, es:[di+4]
    je      FoundFat16Partition
    add     di, 16
    dec     cx
    jz      PartitionNotFoundError
    jmp     FindFat16Partition

FoundFat16Partition:
    mov     eax, es:[di+8]
    mov     [LBAStart], eax         ; save the starting lba

Step6:    ; Compute the First Data Sector of the FAT
    movzx   eax, [RootDirEntries]
    shl     eax, 5                  ; (assume no overflow)
    movzx   ecx, [BytesPerSector]
    add     eax, ecx
    dec     eax
    div     ecx                     ; (discard remainder)
    mov     [RootDirSectors], ax    ; RootDirSectors = ((RootDirEntries * 32) + (BytesPerSector - 1)) / BytesPerSector

    movzx   eax, [SecsPerClust]
    mul     ecx
    shr     eax, 4
    push    ax                      ; save the cluster size on the stack

    movzx   eax, [NumFats]
    mul     [NumFatSecs]            ; (assume no overflow)
    add     ax, [ReservedSecs]
    mov     [RootDirStart], ax      ; RootDirStart = ReservedSecs + (NumFats * NumFatSecs)

    add     ax, [RootDirSectors]
    mov     [FirstDataSector], ax   ; FirstDataSector = RootDirStart + RootDirSectors

Step7:    ; Search the Root Directory for 'SINGLDR ', find its starting cluster

    mov     dx, [RootDirSectors]    ; set counter for # sectors in root dir

    mov     ax, 4000h
    mov     es, ax                  ; set up ES for a disk transfer

    movzx   eax, [RootDirStart]
    add     eax, [LBAStart]         ; compute true first sector of root dir

LoadNextSector:
    mov     ecx, 1
    call    ReadDisk                ; read 1 sector (eax has sector #) to es:0000h

    mov     bx, [BytesPerSector]    ; set a counter for how many directory entries we will check (32 bytes per entry)
    xor     di, di                  ; prep for comparison between [ds:si] (search string) and [es:di] (sector data)

CompareDirEntries:
    mov     si, OFFSET Stage2File   ; [ds:si] points to the string we are looking for...
    mov     cx, 11                  ; we are matching an 11-character file name
    repe    cmpsb
    je      FoundMatch
    add     di, cx
    add     di, 21                  ; move to next dir entry, but first make sure we aren't at the last entry!
    sub     bx,32
    jnz     CompareDirEntries

    inc     eax                     ; prep to read next entry
    dec     edx
    jz      FileNotFoundError
    jmp     LoadNextSector

FoundMatch:
                                    ; es:[di] points to 12th byte of the 32-byte 
                                    ; directory entry for the 2nd stage boot loader file
    mov     ax, es:[di+15]          ; read the cluster at offset 26

Step8:    ; Load the file whose first cluster is ax to 57c0:0000

    mov     cx, 057c0h
    mov     es, cx

DoRead:
    call    ReadCluster
    push    es
    
    mov     cx, 04000h              ; use different segment to find next cluster
    mov     es, cx
    call    CalcNextCluster
    pop     cx
    add     cx, [bp-2]
    mov     es, cx
    cmp     ax, EndOfClusterMarker
    jb      DoRead

Step9:    ; Transfer Control to the boot loader file, which we stored at 5000:7c00

    movzx   edx, [BootDrv]
    push    edx                     ; SINGLDR will need to know the boot drive #
    pushd   04806h                  ; H6 boot signature = HD, Fat16
        
    db      09Ah                    ; emit a long call to 5000:7c00
    dd      50007c00h
        
    mov     al, "*"
    jmp     PrintError
        
;;;;;;;;;;;;;;;;;;;;
; CalcNextCluster
;
; Inputs:       ax      = current cluster
;               es      = target segment for disk read (es:00)
; Operation:    Read the FAT, lookup the value for the cluster in ax, and return it as ax

CalcNextCluster PROC NEAR
    and     eax, 0FFFFh             ; clear top half of eax
    shl     ax, 1
    xor     dx, dx                  ; clear top half of dividend
    div     [BytesPerSector]
    push    dx                      ; save remainder for later - it is the offset
    add     ax, [ReservedSecs]
    add     eax, [LBAStart]         ; eax has the sector to read

    ; Call ReadDisk for 1 sector to es:0000
    mov     cx, 1
    call    ReadDisk

    ; read cluster# at the offset
    pop     bx                      ; pop the offset
    mov     ax, es:[bx]             ; get the value, put it in ax
    ret
CalcNextCluster ENDP

;;;;;;;;;;;;;;;;;;;;
; ReadCluster
;
; Inputs:       ax      = cluster number to read
;               es      = segment into which we will read (at es:0000)
; Operation:    Read a cluster from the HD, using ReadDisk as a subroutine

ReadCluster PROC NEAR
    pushad

    ; compute the sector that starts the cluster
    and     eax, 0FFFFh             ; clear top half of eax for safety.
    sub     eax, 2
    movzx   ecx, [SecsPerClust]     ; cx = sectors to load (this always read full clusters)
    mul     ecx
    add     ax, [FirstDataSector]
    add     eax, [LBAStart]         ; eax holds the sector to read
    call    ReadDisk

    popad
    ret
ReadCluster ENDP

;;;;;;;;;;;;;;;;;;;;
; ReadDisk
;
; Inputs:       eax     = LBA sector to read
;               cx      = number of sectors to read (limit to 64 or less)
;               es:bx   = destination address (always read to offset 0)
; Assumptions:  1 - assumes request will not cause overflow of es (limit on # sectors)
;               2 - assumes int13 extensions available
;               3 - LBA is limited to 32-bit values.  If the disk is > 2 TB, we have a problem

ReadDisk PROC NEAR
    pushad
    mov     dl, [BootDrv]           ; set the drive
                
    pushd   00
    push    eax                     ; push 64-bit sector address (top half always null)

    push    es
    pushw   00                      ; push transfer address

    push    cx                      ; # sectors
    pushw   0010h                   ; this request packet is 16 bytes
    mov     ah,42h                  ; extended read
    mov     si,sp                   ; ds:si = address of params
    int     13h                     ; perform the read

    add     sp, 10h                 ; clean the stack and return
    popad
    ret
ReadDisk ENDP

;;;;;;;;;;;;;;;;;;;;
; Error Routines (these are jump points that never return)

PartitionNotFoundError:
    mov     al, "P"        
    jmp     PrintError
FileNotFoundError:
    mov     al, "F"
    jmp     PrintError
HWUnsupportedError:
    mov     al, "H"
PrintError:
    mov     bx, 07h                 ; normal attribute
    mov     ah, 0eh                 ; default print 1 char
    mov     cx, 6
    mov     si, offset ErrorMsg
    int     10h
printnext:
    lodsb
    or      al, al
    jz      infloop
    int     10h
    jmp     printnext
infloop:
    jmp     infloop

;;;;;;;;;;;;;;;;;;;;
; String Constants

    ErrorMsg    DB  " Error "
    Stage2File  DB  "SINGLDR    "   ; spaces are important for FAT file name determination.  Compare all 11 bytes!
    DB  0
        
;;;;;;;;;;;;;;;;;;;;
; Boot Sector Signature

    ORG     510
    DW      0AA55h
    
end start
