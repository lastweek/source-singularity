;++
;
; Copyright (c) Microsoft Corporation
;
; Module Name:
;
;     blioport.asm
;
; Abstract:
;
;     This module implements IO port access routines for the boot loader.
;
; Environment:
;
;     Boot loader.
;
;--

include bl.inc

.code

;++
;
; UCHAR
; BlRtlReadPort8(
;     USHORT Port
;     )
;
; Routine Description:
;
;   This function reads from the specified 8-bit port.
;
; Arguments:
;
;   Port        - Supplies the port to read from.
;
; Return Value:
;
;   Value read from the port.
;
;--

?BlRtlReadPort8@@YAEG@Z proc

        mov     dx, cx
        in      al, dx
        ret

?BlRtlReadPort8@@YAEG@Z endp

;++
;
; ULONG
; BlRtlReadPort32(
;     USHORT Port
;     )
;
; Routine Description:
;
;   This function reads from the specified 32-bit port.
;
; Arguments:
;
;   Port        - Supplies the port to read from.
;
; Return Value:
;
;   Value read from the port.
;
;--

?BlRtlReadPort32@@YAKG@Z proc

        mov     dx, cx
        in      eax, dx
        ret

?BlRtlReadPort32@@YAKG@Z endp

;++
;
; VOID
; BlRtlWritePort8(
;     USHORT Port,
;     UCHAR Value
;     )
;
; Routine Description:
;
;   This function writes to the specified 8-bit port.
;
; Arguments:
;
;   Port        - Supplies the port to write to.
;
;   Value       - Supplies the value to write.
;
;--

?BlRtlWritePort8@@YAXGE@Z proc

        mov     al, dl
        mov     dx, cx
        out     dx, al
        ret

?BlRtlWritePort8@@YAXGE@Z endp

;++
;
; VOID
; BlRtlWritePort32(
;     USHORT Port,
;     ULONG Value
;     )
;
; Routine Description:
;
;   This function writes to the specified 32-bit port.
;
; Arguments:
;
;   Port        - Supplies the port to write to.
;
;   Value       - Supplies the value to write.
;
;--

?BlRtlWritePort32@@YAXGK@Z proc

        mov     eax, edx
        mov     dx, cx
        out     dx, eax
        ret

?BlRtlWritePort32@@YAXGK@Z endp

end
