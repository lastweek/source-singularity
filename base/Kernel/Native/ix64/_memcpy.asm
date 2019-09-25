;*******************************************************************************
;memcpy.asm - contains memcpy and memmove routines
;
;       Copyright (c) Microsoft Corporation. All rights reserved.
;
;Purpose:
;       memcpy() copies a source memory buffer to a destination buffer.
;       Overlapping buffers are not treated specially, so propogation may occur.
;       memmove() copies a source memory buffer to a destination buffer.
;       Overlapping buffers are treated specially, to avoid propogation.
;
;*******************************************************************************

.code
        
include hal.inc

;***
;memcpy - Copy source buffer to destination buffer
;
;Purpose:
;       memcpy() copies a source memory buffer to a destination memory buffer.
;       This routine does NOT recognize overlapping buffers, and thus can lead
;       to propogation.
;       For cases where propogation must be avoided, memmove() must be used.
;
;       Algorithm:
;
;       void * memcpy(void * dst, void * src, size_t count)
;       {
;               void * ret = dst;
;
;               /*
;                * copy from lower addresses to higher addresses
;                */
;               while (count--)
;                       *dst++ = *src++;
;
;               return(ret);
;       }
;
;memmove - Copy source buffer to destination buffer
;
;Purpose:
;       memmove() copies a source memory buffer to a destination memory buffer.
;       This routine recognize overlapping buffers to avoid propogation.
;       For cases where propogation is not a problem, memcpy() can be used.
;
;   Algorithm:
;
;       void * memmove(void * dst, void * src, size_t count)
;       {
;               void * ret = dst;
;
;               if (dst <= src || dst >= (src + count)) {
;                       /*
;                        * Non-Overlapping Buffers
;                        * copy from lower addresses to higher addresses
;                        */
;                       while (count--)
;                               *dst++ = *src++;
;                       }
;               else {
;                       /*
;                        * Overlapping Buffers
;                        * copy from higher addresses to lower addresses
;                        */
;                       dst += count - 1;
;                       src += count - 1;
;
;                       while (count--)
;                               *dst-- = *src--;
;                       }
;
;               return(ret);
;       }
;
;
;Entry:
;       void *dst = pointer to destination buffer
;       const void *src = pointer to source buffer
;       size_t count = number of bytes to copy
;
;Exit:
;       Returns a pointer to the destination buffer in AX/DX:AX
;
;Uses:
;       CX, DX
;
;Exceptions:
;*******************************************************************************

%       public  memcpy
;; memcopy (dst,src,count)

memcpy  proc ;;frame
        ;;PrologPush  rbp          ; create ebp chain entry
        ;;SetFramePointer rbp      ; set new ebp
        ;;.endprolog
        
;;spin:   jmp     spin        
        ;;mov  [esp+8], rcx       ; spill dest 
        
        push    rdi             ;U - save rdi
        push    rsi             ;V - save rsi

        mov     r9,rcx          ; save off dst in scratch reg

        mov     rsi,rdx         ;U - rsi = source

        mov     rdi,rcx         ;U - rdi = dest
        mov     rcx,r8          ;V - rdx = number of bytes to move
        
        cmp     r8,2h
        jnz     hack
;spin:   jmp     spin
hack:        
;
; Check for overlapping buffers:
;       If (dst <= src) Or (dst >= src + Count) Then
;               Do normal (Upwards) Copy
;       Else
;               Do Downwards Copy to avoid propagation
;

        mov     rax,r8         ;V - rax = byte count...

        mov     rdx,r8          ;U - rdx = byte count...
        add     rax,rsi         ;V - rax = point past source end

        cmp     rdi,rsi         ;U - dst <= src ?
        jbe     CopyUp          ;V - yes, copy toward higher addresses

        cmp     rdi,rax         ;U - dst < (src + count) ?
        jb      CopyDown        ;V - yes, copy toward lower addresses

;
; Copy toward higher addresses.
;
;
; The algorithm for forward moves is to align the destination to a dword
; boundary and so we can move dwords with an aligned destination.  This
; occurs in 3 steps.
;
;   - move x = ((4 - Dest & 3) & 3) bytes
;   - move y = ((L-x) >> 2) dwords
;   - move (L - x - y*4) bytes
;

CopyUp:
        test    rdi,11b         ;U - destination dword aligned?
        jnz     short CopyLeadUp ;V - if we are not dword aligned already, align

        shr     rcx,2           ;U - shift down to dword count
        and     rdx,11b         ;V - trailing byte count

        cmp     rcx,8           ;U - test if small enough for unwind copy
        jb      short CopyUnwindUp ;V - if so, then jump

        rep     movsd           ;N - move all of our dwords

        lea     r10, TrailUpVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

;
; Code to do optimal memory copies for non-dword-aligned destinations.
;

; The following length check is done for two reasons:
;
;    1. to ensure that the actual move length is greater than any possiale
;       alignment move, and
;
;    2. to skip the multiple move logic for small moves where it would
;       be faster to move the bytes with one instruction.
;

        align   8
CopyLeadUp:

        mov     rax,rdi         ;U - get destination offset
        mov     rdx,11b         ;V - prepare for mask

        sub     rcx,4           ;U - check for really short string - sub for adjust
        jb      ByteCopyUp ;V - branch to just copy bytes

        and     rax,11b         ;U - get offset within first dword
        add     rcx,rax         ;V - update size after leading bytes copied

        lea     r10,LeadUpVec
        jmp     [rax*8-8 + r10] ;N - process leading bytes

        align   8
ByteCopyUp:
        lea     r10, TrailUpVec
        jmp     [rcx*8+32 + r10] ;N - process just bytes

        align   8
CopyUnwindUp:
        lea     r10,UnwindUpVec
        jmp     [rcx*8 + r10] ;N - unwind dword copy

        align   8
LeadUpVec       dq     LeadUp1, LeadUp2, LeadUp3

        align   8
LeadUp1:
        and     rdx,rcx         ;U - trailing byte count
        mov     al,[rsi]        ;V - get first byte from source

        mov     [rdi],al        ;U - write second byte to destination
        mov     al,[rsi+1]      ;V - get second byte from source

        mov     [rdi+1],al      ;U - write second byte to destination
        mov     al,[rsi+2]      ;V - get third byte from source

        shr     rcx,2           ;U - shift down to dword count
        mov     [rdi+2],al      ;V - write third byte to destination

        add     rsi,3           ;U - advance source pointer
        add     rdi,3           ;V - advance destination pointer

        cmp     rcx,8           ;U - test if small enough for unwind copy
        jb      short CopyUnwindUp ;V - if so, then jump

        rep     movsd           ;N - move all of our dwords


        ;;jmp     TrailUpVec[rdx*4] ;N - process trailing bytes
        lea     r10, TrailUpVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

        align   8
LeadUp2:
        and     rdx,rcx         ;U - trailing byte count
        mov     al,[rsi]        ;V - get first byte from source

        mov     [rdi],al        ;U - write second byte to destination
        mov     al,[rsi+1]      ;V - get second byte from source

        shr     rcx,2           ;U - shift down to dword count
        mov     [rdi+1],al      ;V - write second byte to destination

        add     rsi,2           ;U - advance source pointer
        add     rdi,2           ;V - advance destination pointer

        cmp     rcx,8           ;U - test if small enough for unwind copy
        jb      CopyUnwindUp    ;V - if so, then jump

        rep     movsd           ;N - move all of our dwords

        ;jmp     qword ptr TrailUpVec[rdx*4] ;N - process trailing bytes
        lea     r10, TrailUpVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

        align   8
LeadUp3:
        and     rdx,rcx         ;U - trailing byte count
        mov     al,[rsi]        ;V - get first byte from source

        mov     [rdi],al        ;U - write second byte to destination
        add     rsi,1           ;V - advance source pointer

        shr     rcx,2           ;U - shift down to dword count
        add     rdi,1           ;V - advance destination pointer

        cmp     rcx,8           ;U - test if small enough for unwind copy
        jb      CopyUnwindUp ;V - if so, then jump

        rep     movsd           ;N - move all of our dwords

        ;jmp     qword ptr TrailUpVec[rdx*4] ;N - process trailing bytes
        lea     r10, TrailUpVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

        align   8
UnwindUpVec     dq      UnwindUp0, UnwindUp1, UnwindUp2, UnwindUp3
                dq      UnwindUp4, UnwindUp5, UnwindUp6, UnwindUp7

UnwindUp7:
        mov     eax,[rsi+rcx*4-28] ;U - get dword from source
                                   ;V - spare
        mov     [rdi+rcx*4-28],eax ;U - put dword into destination
UnwindUp6:
        mov     eax,[rsi+rcx*4-24] ;U(entry)/V(not) - get dword from source
                                   ;V(entry) - spare
        mov     [rdi+rcx*4-24],eax ;U - put dword into destination
UnwindUp5:
        mov     eax,[rsi+rcx*4-20] ;U(entry)/V(not) - get dword from source
                                   ;V(entry) - spare
        mov     [rdi+rcx*4-20],eax ;U - put dword into destination
UnwindUp4:
        mov     eax,[rsi+rcx*4-16] ;U(entry)/V(not) - get dword from source
                                   ;V(entry) - spare
        mov     [rdi+rcx*4-16],eax ;U - put dword into destination
UnwindUp3:
        mov     eax,[rsi+rcx*4-12] ;U(entry)/V(not) - get dword from source
                                   ;V(entry) - spare
        mov     [rdi+rcx*4-12],eax ;U - put dword into destination
UnwindUp2:
        mov     eax,[rsi+rcx*4-8] ;U(entry)/V(not) - get dword from source
                                  ;V(entry) - spare
        mov     [rdi+rcx*4-8],eax ;U - put dword into destination
UnwindUp1:
        mov     eax,[rsi+rcx*4-4] ;U(entry)/V(not) - get dword from source
                                  ;V(entry) - spare
        mov     [rdi+rcx*4-4],eax ;U - put dword into destination

        lea     rax,[rcx*4]     ;V - compute update for pointer

        add     rsi,rax         ;U - update source pointer
        add     rdi,rax         ;V - update destination pointer
UnwindUp0:
        ;jmp     qword ptr TrailUpVec[rdx*4] ;N - process trailing bytes
        lea     r10, TrailUpVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

;-----------------------------------------------------------------------------

        align   8
TrailUpVec      dq      TrailUp0, TrailUp1, TrailUp2, TrailUp3

        align   8
TrailUp0:
        mov     rax, r9         ;U - return pointer to destination
        pop     rsi             ;V - restore rsi
        pop     rdi             ;U - restore rdi
                                ;V - spare
        ret

        align   8
TrailUp1:
        mov     al,[rsi]        ;U - get byte from source
                                ;V - spare
        mov     [rdi],al        ;U - put byte in destination
        mov     rax,r9          ;V - return pointer to destination
        pop     rsi             ;U - restore rsi
        pop     rdi             ;V - restore rdi
        ret

        align   8
TrailUp2:
        mov     al,[rsi]        ;U - get first byte from source
                                ;V - spare
        mov     [rdi],al        ;U - put first byte into destination
        mov     al,[rsi+1]      ;V - get second byte from source
        mov     [rdi+1],al      ;U - put second byte into destination
        mov     rax,r9          ;V - return pointer to destination
        pop     rsi             ;U - restore rsi
        pop     rdi             ;V - restore rdi
        ret

        align   8
TrailUp3:
        mov     al,[rsi]        ;U - get first byte from source
                                ;V - spare
        mov     [rdi],al        ;U - put first byte into destination
        mov     al,[rsi+1]      ;V - get second byte from source
        mov     [rdi+1],al      ;U - put second byte into destination
        mov     al,[rsi+2]      ;V - get third byte from source
        mov     [rdi+2],al      ;U - put third byte into destination
        mov     rax,r9          ;V - return pointer to destination
        pop     rsi             ;U - restore rsi
        pop     rdi             ;V - restore rdi
        ret

;-----------------------------------------------------------------------------
;-----------------------------------------------------------------------------
;-----------------------------------------------------------------------------

;
; Copy down to avoid propogation in overlapping buffers.
;
        align   8
CopyDown:
        lea     rsi,[rsi+rcx-4] ;U - point to 4 bytes before src buffer end
        lea     rdi,[rdi+rcx-4] ;V - point to 4 bytes before dest buffer end
;
; See if the destination start is dword aligned
;

        test    rdi,11b         ;U - test if dword aligned
        jnz     short CopyLeadDown ;V - if not, jump

        shr     rcx,2           ;U - shift down to dword count
        and     rdx,11b         ;V - trailing byte count

        cmp     rcx,8           ;U - test if small enough for unwind copy
        jb      short CopyUnwindDown ;V - if so, then jump

        std                     ;N - set direction flag
        rep     movsd           ;N - move all of our dwords
        cld                     ;N - clear direction flag back

        ;jmp     qword ptr TrailDownVec[rdx*4] ;N - process trailing bytes
        lea     r10, TrailDownVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

        align   8
CopyUnwindDown:
        neg     rcx             ;U - negate dword count for table merging
                                ;V - spare

        ;jmp     qword ptr UnwindDownVec[rcx*4+28] ;N - unwind copy
        lea     r10,UnwindDownVec
        jmp     [rcx*8+56 + r10] ;N - unwind copy

        align   8
CopyLeadDown:

        mov     rax,rdi         ;U - get destination offset
        mov     rdx,11b         ;V - prepare for mask

        cmp     rcx,4           ;U - check for really short string
        jb      short ByteCopyDown ;V - branch to just copy bytes

        and     rax,11b         ;U - get offset within first dword
        sub     rcx,rax         ;U - to update size after lead copied

        ;jmp     qword ptr LeadDownVec[rax*8-8] ;N - process leading bytes
        lea     r10,LeadDownVec
        jmp     [rax*8-8 + r10] ;N - process leading bytes

        align   8
ByteCopyDown:
        ;jmp     qword ptr TrailDownVec[rcx*8] ;N - process just bytes
        lea     r10, TrailDownVec
        jmp     [rcx*8 + r10] ;N - process just bytes

        align   8
LeadDownVec     dq      LeadDown1, LeadDown2, LeadDown3

        align   8
LeadDown1:
        mov     al,[rsi+3]      ;U - load first byte
        and     rdx,rcx         ;V - trailing byte count

        mov     [rdi+3],al      ;U - write out first byte
        sub     rsi,1           ;V - point to last src dword

        shr     rcx,2           ;U - shift down to dword count
        sub     rdi,1           ;V - point to last dest dword

        cmp     rcx,8           ;U - test if small enough for unwind copy
        jb      CopyUnwindDown ;V - if so, then jump

        std                     ;N - set direction flag
        rep     movsd           ;N - move all of our dwords
        cld                     ;N - clear direction flag

        ;jmp     qword ptr TrailDownVec[rdx*4] ;N - process trailing bytes
        lea     r10, TrailDownVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

        align   8
LeadDown2:
        mov     al,[rsi+3]      ;U - load first byte
        and     rdx,rcx         ;V - trailing byte count

        mov     [rdi+3],al      ;U - write out first byte
        mov     al,[rsi+2]      ;V - get second byte from source

        shr     rcx,2           ;U - shift down to dword count
        mov     [rdi+2],al      ;V - write second byte to destination

        sub     rsi,2           ;U - point to last src dword
        sub     rdi,2           ;V - point to last dest dword

        cmp     rcx,8           ;U - test if small enough for unwind copy
        jb      CopyUnwindDown ;V - if so, then jump

        std                     ;N - set direction flag
        rep     movsd           ;N - move all of our dwords
        cld                     ;N - clear direction flag

        ;jmp     qword ptr TrailDownVec[rdx*4] ;N - process trailing bytes
        lea     r10, TrailDownVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

        align   8
LeadDown3:
        mov     al,[rsi+3]      ;U - load first byte
        and     rdx,rcx         ;V - trailing byte count

        mov     [rdi+3],al      ;U - write out first byte
        mov     al,[rsi+2]      ;V - get second byte from source

        mov     [rdi+2],al      ;U - write second byte to destination
        mov     al,[rsi+1]      ;V - get third byte from source

        shr     rcx,2           ;U - shift down to dword count
        mov     [rdi+1],al      ;V - write third byte to destination

        sub     rsi,3           ;U - point to last src dword
        sub     rdi,3           ;V - point to last dest dword

        cmp     rcx,8           ;U - test if small enough for unwind copy
        jb      CopyUnwindDown  ;V - if so, then jump

        std                     ;N - set direction flag
        rep     movsd           ;N - move all of our dwords
        cld                     ;N - clear direction flag

        ;jmp     qword ptr TrailDownVec[rdx*4] ;N - process trailing bytes
        lea     r10, TrailDownVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

;------------------------------------------------------------------

        align   8
UnwindDownVec   dq     UnwindDown7, UnwindDown6, UnwindDown5, UnwindDown4
                dq      UnwindDown3, UnwindDown2, UnwindDown1, UnwindDown0

UnwindDown7:
        mov     rax,[rsi+rcx*4+28] ;U - get dword from source
                                   ;V - spare
        mov     [rdi+rcx*4+28],rax ;U - put dword into destination
UnwindDown6:
        mov     rax,[rsi+rcx*4+24] ;U(entry)/V(not) - get dword from source
                                   ;V(entry) - spare
        mov     [rdi+rcx*4+24],rax ;U - put dword into destination
UnwindDown5:
        mov     rax,[rsi+rcx*4+20] ;U(entry)/V(not) - get dword from source
                                   ;V(entry) - spare
        mov     [rdi+rcx*4+20],rax ;U - put dword into destination
UnwindDown4:
        mov     rax,[rsi+rcx*4+16] ;U(entry)/V(not) - get dword from source
                                   ;V(entry) - spare
        mov     [rdi+rcx*4+16],rax ;U - put dword into destination
UnwindDown3:
        mov     rax,[rsi+rcx*4+12] ;U(entry)/V(not) - get dword from source
                                   ;V(entry) - spare
        mov     [rdi+rcx*4+12],rax ;U - put dword into destination
UnwindDown2:
        mov     rax,[rsi+rcx*4+8] ;U(entry)/V(not) - get dword from source
                                   ;V(entry) - spare
        mov     [rdi+rcx*4+8],rax ;U - put dword into destination
UnwindDown1:
        mov     rax,[rsi+rcx*4+4] ;U(entry)/V(not) - get dword from source
                                  ;V(entry) - spare
        mov     [rdi+rcx*4+4],rax ;U - put dword into destination

        lea     rax,[rcx*4]     ;V - compute update for pointer

        add     rsi,rax         ;U - update source pointer
        add     rdi,rax         ;V - update destination pointer
UnwindDown0:
        ;jmp     qword ptr TrailDownVec[rdx*4] ;N - process trailing bytes
        lea     r10, TrailDownVec
        jmp     [rdx*8 + r10] ;N - process trailing bytes

;-----------------------------------------------------------------------------

        align   8
TrailDownVec    dq      TrailDown0, TrailDown1, TrailDown2, TrailDown3

        align   8
TrailDown0:
        mov     rax,r9          ;U - return pointer to destination
                                ;V - spare
        pop     rsi             ;U - restore rsi
        pop     rdi             ;V - restore rdi
        ret

        align   8
TrailDown1:
        mov     al,[rsi+3]      ;U - get byte from source
                                ;V - spare
        mov     [rdi+3],al      ;U - put byte in destination
        mov     rax,r9          ;V - return pointer to destination
        pop     rsi             ;U - restore rsi
        pop     rdi             ;V - restore rdi
        ret

        align   8
TrailDown2:
        mov     al,[rsi+3]      ;U - get first byte from source
                                ;V - spare
        mov     [rdi+3],al      ;U - put first byte into destination
        mov     al,[rsi+2]      ;V - get second byte from source
        mov     [rdi+2],al      ;U - put second byte into destination
        mov     rax,r9          ;V - return pointer to destination
        pop     rsi             ;U - restore rsi
        pop     rdi             ;V - restore rdi
        ret

        align   8
TrailDown3:
        mov     al,[rsi+3]      ;U - get first byte from source
                                ;V - spare
        mov     [rdi+3],al      ;U - put first byte into destination
        mov     al,[rsi+2]      ;V - get second byte from source
        mov     [rdi+2],al      ;U - put second byte into destination
        mov     al,[rsi+1]      ;V - get third byte from source
        mov     [rdi+1],al      ;U - put third byte into destination
        mov     rax,r9          ;V - return pointer to destination
        pop     rsi             ;U - restore rsi
        pop     rdi             ;V - restore rdi
        ret

memcpy   endp


memmove proc \
        dst:ptr byte, \
        src:ptr byte, \
        count:DWORD

        jmp memcpy
        
memmove endp
        end

