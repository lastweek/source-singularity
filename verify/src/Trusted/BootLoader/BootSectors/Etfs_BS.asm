;;
;;  Copyright (c) Microsoft Corporation.  All rights reserved.
;;

;;;;;;;;;;;;;;;;;;;;
; Concerns
;  1 - there is no error checking on the int13 calls
;  2 - we assume that the block size is 2048 bytes
;  3 - this cannot handle large root directories (>64KB)

;;;;;;;;;;;;;;;;;;;;
; Constants

BootSecOrigin       EQU     07c00h      ; the BIOS puts the boot sector at 07c0h:0000 == 0000:7c00h
StackOffset         EQU     -12         ; we will put the stack a small bit below it (we hardly use the stack, so it is safe...)

;;;;;;;;;;;;;;;;;;;;
; Macros

JMPF16 MACRO SEG:REQ,OFF:REQ
        db      0eah
        dw      OFF
        dw      SEG
ENDM        

        
;;;;;;;;;;;;;;;;;;;;
; Directives

.model tiny
.686p

;;;;;;;;;;;;;;;;;;;;
; Begin Code segment

_TEXT SEGMENT use16 ; 16-bit code segment
.code
ORG     0h                          ; ETFS puts us at 07c0h:0000

start:
    JMPF16  07c0h,OFFSET Step1
        
Step1:    ; set stack and data segments
    mov     cx, cs
    mov     ss, cx
    mov     sp, BootSecOrigin + StackOffset
    mov     es, cx
    mov     ds, cx
    mov     bp, sp

Step2:    ; Save the boot drive (dl holds it on boot)
    mov     [CDDrive], dl

Step3:    ; Clear the Screen
    mov     ax, 02h
    int     010h

        ;; Configure GS to point to the text-mode video console.
    mov     ax, 0b800h
    mov     gs, ax

        ;; Write 'A' to position 0.
    mov     ax, 04f41h
    mov     gs:[0], ax
       
        ;; Write 'B' to position 1.
    mov     ax, 04f42h
    mov     gs:[2], ax
       
Step4:    ; Load the PVD to get the Logical Block Size
    mov     eax, 10h                ; the PVD is in the 16th block
    mov     bx, 2000h
    mov     es, bx                  ; transfer address = 2000:0000
    mov     cx, 1
    call    ReadDisk
    mov     ax, es:128              ; block size is at offset 128
    mov     [BlockSize], ax

        ;; Write 'C' to position 2.
    mov     ax, 04f43h
    mov     gs:[4], ax
       
Step5:    ; Find the Joliet SVD, and then find the Root Directory Information
    mov     eax, 10h                ; start with the PVD, even though it will fail
GetNextVD:
    push    eax
    mov     cx, 1
    call    ReadDisk
    mov     si, OFFSET SVDesc       ; [ds:si] points to the desired first 6 bytes of this VD
    xor     di, di                  ; [es:di] points to the start of what we just read
    mov     cx, 6
    repe    cmpsb
    je      FoundSVD
    mov     al, es:0000h
    cmp     al, 0FFh                ; is this the last Volume Descriptor?
    je      SVDError
    pop     eax
    inc     eax
    jmp     GetNextVD               ; try another VD

FoundSVD:                           ; need to make sure this is a Joliet SVD - we need 025h, 02Fh, 045h in [88,89,90]
    mov     si, OFFSET JolietSig    ; [ds:si] points to the Joliet Signature
    mov     di, 88                  ; [es:di] points to the escape sequence field of the current SVD
    mov     cx, 3
    repe    cmpsb
    je      FoundJoliet
    pop     eax
    inc     eax
    jmp     GetNextVD

FoundJoliet:
        ;; Write 'D' to position 3.
    mov     ax, 04f44h
    mov     gs:[6], ax
       
    mov     eax, es:158             ; now get the rootstart and rootsize fields
    mov     [RootStart], eax
    mov     eax, es:166
    mov     [RootSize], eax

Step6:    ; Load the Root Directory (SVD), and search it for SINGLDR
    movzx   ebx, [BlockSize]
    mov     edx, 0
    div     ebx                     ; eax has # blocks in root directory.  Round up if necessary:
    cmp     edx, 0
    je      ReadyToLoad
    add     eax, 1
ReadyToLoad:                        ; we're going to assume that the root directory will not be bigger than 64K
    mov     ecx, eax
    mov     eax, [RootStart]
    call    ReadDisk

    xor     ebx, ebx                ; bx will hold the start of the current entry
CheckEntry:
    mov     di, bx
    add     di, 25                  ; let's check the file flags - should be 00
    mov     al, es:[di]
    cmp     al, 0
    jne     PrepNextEntry
                                    ; file flags are good.  now check the file identifier:
    mov     si, OFFSET Stage2FileSize
    xor     cx, cx
    mov     cl, ds:[si]             ; first byte is file name length
    add     cx, 2                   ; add two because we check the length byte of the directory entry and the padding byte, too
    add     di, 7                   ; now es:di points to the file length/name field, and ds:si has our desired content
    repe    cmpsb
    je      FoundEntry

PrepNextEntry:
    xor     cx, cx                  ; increment bx by adding the byte value in es:[bx]
    mov     cl, es:[bx]             ; if es:[bx]==0 and ebx!= [RootSize], then we are in a padding zone
    cmp     cx, 0                   ; designed to prevent a directory entry from spilling over a block.
    jne     LoadNext                ; Should this be the case, we will increment bx until es:[bx] is not null
    inc     bx
    jmp     PrepNextEntry

LoadNext:
    add     bx, cx
    cmp     ebx, [RootSize]
    jl      CheckEntry
    jmp     FileNotFoundError

FoundEntry:
        ;; Write 'E' to position 5.
    mov     ax, 04f45h
    mov     gs:[8], ax
       
    mov     eax, es:[bx+2]
    mov     [FileStart], eax
    mov     eax, es:[bx+10]
    mov     [FileSize], eax
    
Step7:    ; Load the file to 57c0:0000
    mov     cx, 057c0h
    mov     es, cx
    movzx   ebx, [BlockSize]
    mov     edx, 0
    div     ebx                     ; eax has # blocks in root directory
    cmp     edx, 0                  ; on carry, there will be one more block
    je      ReadyToLoadFile
    add     eax, 1

ReadyToLoadFile:
    mov     ecx, eax
    mov     eax, [FileStart]
    call    ReadDisk

        ;; Write 'F' to position 6.
    mov     ax, 04f46h
    mov     gs:[10], ax
        
Step8:    ; Now we need to set up the stack for SINGLDR and do a jump
    xor     cx, cx                  ; Always point the stack to 0000:7c00h - 12
    mov     ss, cx
    mov     sp, BootSecOrigin + StackOffset

    movzx   edx, [CDDrive]
    push    edx                     ; SINGLDR will need to know the boot drive #
    pushd   04344h                  ; CD boot signature
    pushw   offset infloop          ; return address = "infloop", which is the infinite loop
    push    cs
    
        ;; Write 'G' to position 7.
    mov     ax, 04f47h
    mov     gs:[12], ax
        
    db      0EAh                    ; emit a long jump to 5000:7c00
    dd      50007c00h

;;;;;;;;;;;;;;;;;;;;
; ReadDisk
;
; Inputs:       eax     = Block Number
;               cx      = number of blocks to read (warning: cx > 32 will cause overflow)
;               es      = destination segment
; Assumptions:  1 - assumes request will not cause overflow of es:00 (limit on # sectors)
;               2 - assumes int13 extensions available

ReadDisk PROC NEAR
    pushad
    mov     dl, [CDDrive]           ; set the drive
                
    pushd   00
    push    eax                     ; push 64-bit block number (top half always null)

    push    es
    pushw   00h                     ; push transfer address

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

SVDError:
    mov     si, offset SvdFailMsg      
    call    PrintString
@@: 
    jmp @b
        
FileNotFoundError:
    mov     si, offset FileNotFoundMsg
    call    PrintString
@@: 
    jmp @b
        
PrintString:
psnext:
    lodsb
    or  al, al
    jz  done

;;; Write directly to memory.
    mov     ah, 047h
    mov     bx, [Cursor]
    mov     gs:[bx], ax
    add     bx, 2
    mov     [Cursor], bx
        
    mov     bx, 07h                 ; normal attribute
    mov     ah, 0eh                 ; default print 1 char
    int 10h
    jmp psnext
done:
    ret        

infloop:
    jmp     infloop
        
;;;;;;;;;;;;;;;;;;;;
; Global Vars

    RootStart       DD  0
    RootSize        DD  0
    CDDrive         DB  0
    BlockSize       DW  0
    FileStart       DD  0
    FileSize        DD  0
    Cursor          DW  640
    
;;;;;;;;;;;;;;;;;;;;
; String Constants

    SVDesc          DB  02h, "CD001"
    JolietSig       DB  25h, 2fh, 45h                               ; this is the value of the escape sequence for a Joliet CD 
                                                                    ;   we'll use it as the signature...
    Stage2FileSize  DB  OFFSET Stage2FilePad - OFFSET Stage2File
    Stage2File      DB  0,"l",0,"o",0,"a",0,"d",0,"e",0,"r"         ; in unicode, this is how our filename will appear
    Stage2FilePad   DB  0
    SvdFailMsg      DB  10,13,"SVD Failed",0
    FileNotFoundMsg DB  10,13,"File not found",0  

;;;;;;;;;;;;;;;;;;;;
; Boot Sector Signature
    ORG     510
    DW      0AA55h

end start
