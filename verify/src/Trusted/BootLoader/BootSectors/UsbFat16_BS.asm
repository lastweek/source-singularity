;; ----------------------------------------------------------------------------
;;
;;  Copyright (c) Microsoft Corporation.  All rights reserved.
;;
;; ----------------------------------------------------------------------------

;;;;;;;;;;;;;;;;;;;;
; Concerns
;  1 - there is no error checking on the int13 calls
;  2 - we assume that the disk is FAT16, and that the parameters in the BPB are correct.
;  3 - There is a risk that the LBA->CHS conversion will overflow

;;;;;;;;;;;;;;;;;;;;
; Constants

BootSecOrigin       EQU     07c00h      ; the BIOS always puts the boot sector here
EndOfClusterMarker  EQU     0FFF8h      ; End of cluster is here or higher

; a little trickery here:  Inside the Boot Sector data structure, there several bytes that we never use.
; whether the real file system uses them or not, we don't need them, and we could use the space for locals.

FirstDataSector     EQU     OemName
RootDirSectors      EQU     OemName+2
RootDirStart        EQU     OemName+4

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

    ; standard boot loader procedcure is to jump over the BPB and BS data structures, then nop
    jmp short bootloader
    nop

;;; Example BPB and BS for Singularity, assuming a 64MB disk.  Installers must NEVER copy these 59 bytes - use what the HD has...
BPB:
    OemName         DW      'IS'        ; setting up the first 8 bytes like this lets us address them in other ways
                    DB      'NGULAR'
    BytesPerSector  DW      512
    SecsPerClust    DB      4
    ReservedSecs    DW      4
    NumFats         DB      2
    RootDirEntries  DW      512
    TotalSectors    DW      0
    MediaByte       DB      0F8H
    NumFatSecs      DW      00fah
    SecPerTrack     DW      03fh
    NumHeads        DW      00FFh
    HiddenSecs      DD      020h
    BigTotalSecs    DD      03e7e0h
    BootDrv         DB      00h
    BSReserved1     DB      0h
    ExtBootSig      DB      29h
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

Step2:    ; Save the boot drive (dl holds it on boot)
    mov     [BootDrv], dl
    mov     al, dl
    
Step3:    ; Clear the Screen
    mov     ax, 02h
    int     010h

Step4:    ; Compute the First Data Sector of the FAT
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


Step5:    ; Search the Root Directory for 'SINGLDR ', find its starting cluster

    mov     dx, [RootDirSectors]    ; set counter for # sectors in root dir

    mov     ax, 4000h
    mov     es, ax                  ; set up ES for a disk transfer

    movzx   eax, [RootDirStart]     ; compute true first sector of root dir

LoadNextSector:
    xor     bx,bx
    call    ReadDiskCHS             ; read sector eax to es:bx

    mov     bx, [BytesPerSector]    ; set a counter for how many directory entries we will check (32 bytes per entry)
    xor     di, di                  ; prep for comparison between [ds:si] (search string) and [es:di] (sector data)

CompareDirEntries:
    mov     si, OFFSET Stage2File   ; [ds:si] points to the string we are looking for...
    mov     cx, 11                  ; we are matching an 11-character file name
    repe    cmpsb
    je      FoundMatch
    add     di, cx
    add     di, 21                  ; move to next dir entry, but first make sure we aren't at the last entry!
    sub     bx, 32
    jnz     CompareDirEntries;

    inc     eax                     ; prep to read next entry
    dec     edx
    jz      FileNotFoundError
    jmp     LoadNextSector

FoundMatch:
                                    ; es:[di] points to 12th byte of the 32-byte 
                                    ; directory entry for the 2nd stage boot loader file
    mov     ax, es:[di+15]          ; read the cluster at offset 26


Step6:    ; Load the file whose first cluster is ax to 57c0:0000

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

Step7:    ; Transfer Control to the boot loader file, which we stored at 5000:7c00

    movzx   edx, [BootDrv]
    push    edx                     ; SINGLDR will need to know the boot drive #
    pushd   05544h                  ; UD boot signature (UsbDisk)

    db      09ah                    ; emit a long jump to 5000:7c00
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
    add     ax, [ReservedSecs]      ; eax has the sector to read

    ; Call ReadDiskCHS to load sector eax at es:bx
    xor     bx, bx
    call    ReadDiskCHS

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
    xor     bx, bx                  ; initially write to es:0000
    and     eax, 0FFFFh             ; clear top half of eax for safety.
    sub     eax, 2
    movzx   ecx, [SecsPerClust]     ; cx = sectors to load (this always read full clusters)
    mul     ecx
    add     ax, [FirstDataSector]   ; eax holds the sector to read
LoadSector:
    call    ReadDiskCHS
    add     bx, [BytesPerSector]
    inc     eax
    dec     cx
    jnz     LoadSector

    popad
    ret
ReadCluster ENDP

;;;;;;;;;;;;;;;;;;;;
; ReadDiskCHS   read one sector as indicated by eax to es:bx
;
; Inputs:       eax     = LBA sector to read
;               es:bx   = destination address
;
; Assumptions:  1 - assumes LBA is not beyond CHS representation

ReadDiskCHS PROC NEAR
    pushad

    xor     edx, edx                ; edx:eax = absolute sector number
    movzx   ecx, [SecPerTrack]      ; ecx = sectors per track
    div     ecx                     ; eax = track, edx = sector within track (0-62)
    inc     dl                      ; dl = sector within track (1-63)
    mov     cl, dl                  ; cl = sector within track
    mov     edx, eax
    shr     edx, 16                 ; dx:ax = track
    div     [NumHeads]              ; ax = cylinder (0-1023), dx = head (0-255)
    xchg    dl, dh                  ; dh = head
    mov     dl, [BootDrv]           ; dl = int13 unit #
    mov     ch, al                  ; ch = bits 0-7 of cylinder
    shl     ah, 6
    or      cl, ah                  ; bits 6-7 of cl = bits 8-9 of cylinder
    mov     ax, 201h                ; read 1 sector
    int     13h

    popad
    ret
ReadDiskCHS ENDP

;;;;;;;;;;;;;;;;;;;;
; Error Routines (these are jump points that never return)

FileNotFoundError:
    mov     al, "F"
    jmp     PrintError
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

    ErrorMsg    DB  " Error"
    Stage2File  DB  "SINGLDR    "   ; spaces are important for FAT file name determination.  Compare all 11 bytes!
    DB 0
        
;;;;;;;;;;;;;;;;;;;;
; Boot Sector Signature

    ORG     510
    DW      0AA55h
    
end start
