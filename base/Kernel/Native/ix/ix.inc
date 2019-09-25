;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Copyright (c) Microsoft Corporation.   All rights reserved.
;
; Include file for intel/amd assembly files.
;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Standard x86/x64 asm file setup

ifdef ISA_IX86
        
.686p
.mmx
.xmm
.model flat

assume ds:flat
assume es:flat
assume ss:flat
assume fs:nothing
assume gs:nothing

endif

.code

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; General purpose utility macros

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DEFINED is a generic utility macro which tests if an identifier is defined
DEFINED MACRO SYM:REQ
        IFDEF SYM
                EXITM <-1>
        ELSE
                EXITM <0>
        ENDIF
ENDM

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; REPLACE is a generic utility macro which replaces FIND with REPL in STRING 
; (if it occurs)

REPLACE MACRO STRING:REQ, FIND:REQ, REPL:REQ
        LOCAL   len, pos, start, end
        len = @SizeStr(FIND)
        pos = @InStr(,STRING,FIND)
        IF pos NE 0
                start   TEXTEQU @SubStr(STRING,1,pos-1)
                if pos+len-1 LT @SizeStr(STRING)
                        end     TEXTEQU @SubStr(STRING,pos+len)
                else
                        end     TEXTEQU <>
                endif
                EXITM @CatStr(%start, REPL, %end)
        else
                EXITM <STRING>
        endif                
ENDM

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

SINGLE_THREADED          equ 0
EXCLUDED                 equ 0

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;  Typedefs & Constants
;
UINT8  TYPEDEF BYTE
UINT16 TYPEDEF WORD
UINT32 TYPEDEF DWORD
UINT64 TYPEDEF QWORD
UINT128 STRUCT 16
        _lo             UINT64          ?
        _hi             UINT64          ?
UINT128 ENDS

;
X86_EFLAG_IF            equ     0200h

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; X86/X64 portability names (P = pointer)
;

ifdef ISA_IX86

PAX     equ     eax
PBX     equ     ebx
PCX     equ     ecx
PDX     equ     edx
PSI     equ     esi
PDI     equ     edi
PBP     equ     ebp
PSP     equ     esp
PIP     equ     eip

PSEG    equ     fs

dp      EQU     dd

PWORD   TYPEDEF DWORD

PUSHFP  equ     pushfd
IRETP   equ     iretd

elseifdef ISA_IX64

PAX     equ     rax
PBX     equ     rbx
PCX     equ     rcx
PDX     equ     rdx
PSI     equ     rsi
PDI     equ     rdi
PBP     equ     rbp
PSP     equ     rsp
PIP     equ     rip

PSEG    equ     gs

dp      EQU     dq

PWORD   TYPEDEF QWORD

PUSHFP  equ     pushfq
IRETP   equ     iretq

endif

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 32/64 register conversion

;; Note InStr step in the logic is to deal with possible parens which seem to 
;; make their way into the REG argument sometimes.  Unfortunately the logic doesn't
;; current work with non --x registers.  Oh well.

REG32 MACRO REG:REQ
        EXITM <@CatStr(e, @SubStr(REG,@InStr(,REG,x)+@InStr(,REG,X)-1,2))>
        ENDM
        
REG64 MACRO REG:REQ
        EXITM <@CatStr(r, @SubStr(REG,@InStr(,REG,x)+@InStr(,REG,X)-1,2))>
        ENDM

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SYMFIX fixes mangled symbols to be the 64-bit version if we are compiling 64 bit.
; Specifically this looks for @@SI and replaces with @@SA, and replaces PAU with PEAU (up to twice.)

SYMFIX MACRO SYM:REQ
        LOCAL   TEMP
ifdef ISA_IX64       
TEMP    TEXTEQU REPLACE(SYM,<@@SI>,<@@SA>)      ; __fastcall -> __cdecl
TEMP    TEXTEQU REPLACE(%TEMP,<@@YI>,<@@YA>)    ; __fastcall -> __cdecl
TEMP    TEXTEQU REPLACE(%TEMP,<@@A>,<@@EA>)     ; (ptr) -> __ptr64
TEMP    TEXTEQU REPLACE(%TEMP,<PAU>,<PEAU>)     ; * --> * __ptr64
TEMP    TEXTEQU REPLACE(%TEMP,<PAU>,<PEAU>)     ; * --> * __ptr64
TEMP    TEXTEQU REPLACE(%TEMP,<PAU>,<PEAU>)     ; * --> * __ptr64
TEMP    TEXTEQU REPLACE(%TEMP,<PAV>,<PEAV>)     ; * --> * __ptr64
TEMP    TEXTEQU REPLACE(%TEMP,<PAV>,<PEAV>)     ; * --> * __ptr64
        EXITM TEMP
else
        EXITM <SYM>
endif
        ENDM

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SYMEXT fixes an external data symbol

SYMEXT MACRO SYM:REQ
ifdef ISA_IX64       
        EXITM <SYM>
else
        EXITM <@CatStr(<_>,SYM)>
endif
        ENDM

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;  Bartok Types
;

uint8 TYPEDEF BYTE
uint16 TYPEDEF WORD
uint32 TYPEDEF DWORD
uint64 TYPEDEF QWORD

int8 TYPEDEF BYTE
int16 TYPEDEF WORD
int32 TYPEDEF DWORD
int64 TYPEDEF QWORD

bool TYPEDEF BYTE
bartok_char TYPEDEF WORD

intptr TYPEDEF PWORD
uintptr TYPEDEF PWORD

uintPtr STRUCT SIZEOF uintptr
        value  uintptr ?
uintPtr ENDS

intPtr STRUCT SIZEOF intptr
        value  intptr ?
intPtr ENDS

PTR_uintptr TYPEDEF PTR uintptr



