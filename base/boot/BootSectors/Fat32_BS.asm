;; ----------------------------------------------------------------------------
;;
;;  Copyright (c) Microsoft Corporation.  All rights reserved.
;;
;; ----------------------------------------------------------------------------

;;;;;;;;;;;;;;;;;;;;
; Concerns
;  1 - there is no error checking on the int13 calls
;  2 - we assume that the disk is FAT32, and that the parameters in the BPB are correct.

;;;;;;;;;;;;;;;;;;;;
; Constants

BootSecOrigin       EQU     07c00h      ; the BIOS always puts the boot sector here
EndOfClusterMarker  EQU     0FFFFFF8h   ; End of cluster is here or higher

; a little trickery here:  Inside the Boot Sector data structure, there several bytes that we never use.
; whether the real file system uses them or not, we don't need them, and we could use the space for locals.

FirstDataSector     EQU     BPBReserved2
LBAStart            EQU     BPBReserved2+4

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

;;; Example BPB and BS for Singularity, assuming a 1GB disk.  Installers must NEVER copy these 87 bytes - use what the HD has...
BPB:
    OemName         DB  'SINGULAR'
    BytesPerSector  DW  512         ; used by boot loader
    SecsPerClust    DB  8           ; used by boot loader
    ReservedSecs    DW  32          ; used by boot loader
    NumFats         DB  2           ; used by boot loader
    NumDirEntries   DW  0
    TotalSectors    DW  0
    MediaByte       DB  0F8H
    NumFatSecs      DW  0
    SecPerTrack     DW  03fh
    NumHeads        DW  64
    HiddenSecs      DD  03fh
    BigTotalSecs    DD  1ffdc1h
    BigNumFatSecs   DD  7feh        ; used by boot loader
    ExtFlags        DW  0
    BPBReserved1    DW  0
    RootStrtClus    DD  2           ; used by boot loader
    FSInfoSec       dw  1
    BkUpBootSec     dw  6
    BPBReserved2    DD  3 DUP (0)   ; used (by another name)
    BootDrv         DB  80h         ; used by boot loader
    BSReserved1     DB  0h
    ExtBootSig      DB  41
    SerialNum       DD  0
    VolumeLabel     DB  'SINGULARITY'
    FileSysType     DB  'FAT32   '

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

    jc      PartitionNotFoundError  ; CF is set on error
    cmp     bx,0aa55h
    jne     PartitionNotFoundError  ; BX != 0xaa55 on error
    test    cl,1
    jz      PartitionNotFoundError  ; bit 0 off on error

Step5:    ; Find the first FAT16 partition in the MBR and store the starting LBA offset.
    xor     eax, eax
    mov     bx, 4000h
    mov     es, bx
    mov     cx, 1
    call    ReadDisk                ; load the MBR to 4000:0000

    mov     cx, 4                   ; check up to 4 entries in the partition table
    mov     di, 446                 ; the offset of the table within the MBR

    mov     eax, 00ch               ; 00ch is the signature for a Fat32 LBA-accessible partition
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
    movzx   ecx, [NumFats]
    mov     eax, [BigNumFatSecs]
    mul     ecx                     ; assume overflow is impossible here
    mov     cx, [ReservedSecs]
    add     eax, ecx
    mov     [FirstDataSector], eax

Step7:    ; Search the Root Directory for SINGLDR, find its starting cluster

    ; calc # of directory entries in a cluster
    xor     ax, ax
    mov     al, [SecsPerClust]
    mul     [BytesPerSector]
    shr     ax, 4
    push    ax                      ; save this for later as BytesPerCluster/16
    shr     ax, 1                   ; BytesPerCluster/32 = # FAT directory entries that fit in a cluster
    push    ax                      ; we will use this to init a counter

    ; set up ES for a disk transfer
    mov     ax, 4000h
    mov     es, ax
    mov     eax, [RootStrtClus]     ; eax has the current cluster to read

LoadNextCluster:                    ; eax holds the cluster to read
    call    ReadCluster

    ; set a counter for how many directory entries we will check
    pop     bx
    push    bx                      ; sadly, this is cheaper than "mov bx, [bp-2]"
    xor     di, di                  ; prep for comparison between [ds:si] (search string) and [es:di] (sector data)

CompareDirEntries:
    mov     si, OFFSET Stage2File   ; [ds:si] points to the string we are looking for...
    mov     cx, 11                  ; we are looking for an 11-character file name
    repe    cmpsb
    je      FoundMatch              ; jump on match
    add     di, cx
    add     di, 21                  ; ready to test the next one, but first make sure we aren't at the last entry!
    dec     bx
    jnz     CompareDirEntries

FindNextCluster:
    call    CalcNextCluster
    cmp     eax, EndOfClusterMarker ; if this is the end of the cluster chain, we are totally sunk - file not found
    jae     FileNotFoundError
    jmp     LoadNextCluster

FoundMatch:
    pop     ax                      ; remove our temp var from the stack

                                    ; es:[di] points to 12th byte of the 32-byte 
                                    ; directory entry for the 2nd stage boot loader file
    mov     ax, es:[di+9]           ; read high 16 bits of the cluster
    shl     eax, 16
    mov     ax, es:[di+15]          ; read low 16 bits of the cluster

Step8:    ; Load the file whose first cluster is eax to 57c0:0000

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
    cmp     eax, EndOfClusterMarker
    jb      DoRead

Step9:    ; Transfer Control to the boot loader file, which we stored at 5000:7c00

    movzx   edx, [BootDrv]
    push    edx                     ; SINGLDR will need to know the boot drive #
    pushd   04803h                  ; H3 boot signature = HD, Fat32
    
    db      09Ah                    ; emit a long jump to 5000:7c00
    dd      50007c00h

    mov     al, "*"
    jmp     PrintError
        
;;;;;;;;;;;;;;;;;;;;
; CalcNextCluster
;
; Inputs:       eax     = current cluster
;               es      = target segment for disk read (es:00)
; Operation:    Read the FAT, lookup the value for the cluster in eax, and return its low 28 bits

CalcNextCluster PROC NEAR
    shl     eax, 2
    xor     edx, edx
    movzx   ecx, [BytesPerSector]
    div     ecx                     ; edx has remainder, eax has quotient
    push    edx                     ; save remainder for later - it is the offset
    mov     dx, [ReservedSecs]
    add     eax, edx
    add     eax, [LBAStart]         ; eax has the sector to read

    ; Call ReadDisk for 1 sector to es:0000
    mov     cx, 1
    call    ReadDisk

    ; read cluster# at the offset
    pop     ebx                     ; pop the offset
    mov     eax, es:[ebx]           ; get the value, put it in eax
    and     eax, 0FFFFFFFh          ; make it a 28-bit value
    ret
CalcNextCluster ENDP

;;;;;;;;;;;;;;;;;;;;
; ReadCluster
;
; Inputs:       eax     = cluster number to read
;               es      = segment into which we will read (at es:0000)
; Operation:    Read a cluster from the HD, using ReadDisk as a subroutine

ReadCluster PROC NEAR
    pushad

    ; compute the sector that starts the cluster
    sub     eax, 2
    movzx   ecx, [SecsPerClust]     ; cx = sectors to load (this always read full clusters)
    mul     ecx
    add     eax, [FirstDataSector]
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
;               es      = destination segment (always read to offset 0)
; Assumptions:  1 - assumes request will not cause overflow of es (limit on # sectors)
;               2 - assumes int13 extensions available
;               3 - LBA is limited to 32-bit values.  If the disk is > 2 TB, we have a problem

ReadDisk PROC NEAR
    pushad
    mov     dl, [BootDrv]           ; set the drive
                
    pushd   00
    push    eax                     ; push 64-bit sector address (top half always null)

    push    es
    pushw   00                      ; push transfer address (offset always 0)

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

    jmp     PrintError
FileNotFoundError:
    mov     al, "F"
    jmp     PrintError
PartitionNotFoundError:
    mov     al, "P"        
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
    ErrorMsg    DB  " Err "
    Stage2File  DB  "SINGLDR    "   ; spaces are important for FAT file name determination.  Compare all 11 bytes!
    DB  0

;;;;;;;;;;;;;;;;;;;;
; Boot Sector Signature

    ORG     510
    DW      0AA55h

end start
