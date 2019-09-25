;*******************************************************************************
;memset.asm - set a section of memory to all one byte
;
;       Copyright (c) Microsoft Corporation. All rights reserved.
;
;Purpose:
;       contains the memset() routine
;
;*******************************************************************************

.code

;***
;char *memset(dst, value, count) - sets "count" bytes at "dst" to "value"
;
;Purpose:
;       Sets the first "count" bytes of the memory starting
;       at "dst" to the character value "value".
;
;       Algorithm:
;       char *
;       memset (dst, value, count)
;               char *dst;
;               char value;
;               unsigned int count;
;               {
;               char *start = dst;
;
;               while (count--)
;                       *dst++ = value;
;               return(start);
;               }
;
;Entry:
;       char *dst - pointer to memory to fill with value
;       char value - value to put in dst bytes
;       int count - number of bytes of dst to fill
;
;Exit:
;       returns dst, with filled bytes
;
;Uses:
;
;Exceptions:
;
;*******************************************************************************

        public  memset
memset proc
;
; On entry:  rcx=dest, rdx=value, r8=count
;
        test    r8,r8           ; 0?
        jz      short toend     ; if so, nothing to do

        xor     rax,rax         
        mov     al,dl           ; al = value
        mov     rdx,r8          ; rdx = "count"
        mov     r8,rcx          ; scroll away dest for return

; Align address on qword boundary

        push    rdi             ; preserve rdi
        mov     rdi,rcx         ; rdi = dest pointer

        cmp     rdx,8           ; if it's less then 8 bytes
        jb      tail            ; tail needs rdi and rdx to be initialized

        neg     rcx
        and     rcx,7           ; ecx = # bytes before dword boundary
        jz      short qwords    ; jump if address already aligned

        sub     rdx,rcx         ; edx = adjusted count (for later)
adjust_loop:
        mov     [rdi],al
        add     rdi,1
        sub     rcx,1
        jnz     adjust_loop

qwords:
; set all 8 bytes of eax to [value]
        mov     rcx,rax         ; rcx=0/0/0/0/0/0/0/value
        shl     rax,8           ; rax=0/0/0/0/0/0/value/0

        add     rax,rcx         ; rax=0/0/0/0/0/0/0/val/val

        mov     rcx,rax         ; rcx=0/0/0/0/0/0/0/val/val

        shl     rax,10h         ; rax=0/0/0/0/val/val/0/0

        add     rax,rcx         ; rax = all 4 bytes = [value]
        
        mov     rcx,rax         ; rcx =          0/0/0/0/val/val/val/val
        shl     rax,20h         ; rax = val/val/val/val/0/0/0/0/
        
        add     rax,rcx         ; rax = val/val/val/val/val/val/val/val
        

; Set qword-sized blocks
        mov     rcx,rdx         ; move original count to ecx
        and     rdx,7           ; prepare in edx byte count (for tail loop)
        shr     rcx,3           ; adjust ecx to be dword count
        jz      tail            ; jump if it was less then 4 bytes

        rep     stosq
main_loop_tail:
        test    rdx,rdx         ; if there is no tail bytes,
        jz      finish          ; we finish, and it's time to leave
; Set remaining bytes

tail:
        mov     [rdi],al        ; set remaining bytes
        add     rdi,1

        sub     rdx,1           ; if there is some more bytes
        jnz     tail            ; continue to fill them

; Done
finish:
        mov     rax,r8          ; return dest pointer
        pop     rdi             ; restore edi

        ret

toend:
        mov     rax,rcx         ; return dest pointer

        ret

memset  endp

        end
