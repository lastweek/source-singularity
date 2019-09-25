OBJ = ..\..\..\..\obj\Trusted\BootLoader
BUILD = ..\..\..\..\..\base\build

AS = $(BUILD)\x86_x86\ml.exe
CC = $(BUILD)\x86_x86\cl.exe
LINK = $(BUILD)\x86_x86\link.exe
AS16 = $(BUILD)\x86_x86\ml.exe
LINK16 = $(BUILD)\x86_x86\link16.exe
BLGEN = $(BUILD)\x86_x86\blgen.exe

ASM = \
	_x86\blcrtasm.asm \
	_x86\blidt.asm \
	_x86\blioport.asm \
	_x86\bllegacy.asm \
	_x86\blutilasm.asm

SRC = \
	_blacpi.cpp \
	_blcdrom.cpp \
	_blcom.cpp \
	_blentry.cpp \
	_blfat.cpp \
	_blflash.cpp \
	_blkd.cpp \
	_blkd1394.cpp \
	_blkdcom.cpp \
	_blmm.cpp \
	_blmps.cpp \
	_blpci.cpp \
	_blpecoff.cpp \
	_blpnp.cpp \
	_blpool.cpp \
	_blpxe.cpp \
	_blsingularity.cpp \
	_blsmap.cpp \
	_blstring.cpp \
	_bltrap.cpp \
	_blutil.cpp \
	_blvesa.cpp \
	_blvideo.cpp

ASM_OBJS = $(ASM:.asm=.obj)
SRC_OBJS = $(SRC:.cpp=.obj)

OBJS = $(ASM_OBJS:_=..\..\..\..\obj\Trusted\BootLoader\) \
       $(SRC_OBJS:_=..\..\..\..\obj\Trusted\BootLoader\)

all: $(OBJ)\x86 $(OBJ)\loader

$(OBJ)\x86:
  mkdir $(OBJ)\x86

{x86}.asm{$(OBJ)\x86}.obj:
	$(AS) /nologo /c /DBOOT_X86 /I. /Fl$*.lst /Fo$*.obj $<

.cpp{$(OBJ)}.obj:
	$(CC) /nologo /c /DBOOT_X86 /GF /Gy /Gr /Zi /Od /Oy- /GS- /Gs65536 /FAsc /Fa$*.cod /Fo$*.obj /Fd$*.pdb $<
	
$(OBJ)\blentry16.obj: blentry16.asm bl.inc
	$(AS16) /nologo /DBOOT_X86 /AT /omf /c /I. /Fl$(OBJ)\blentry16.lst /Fo$(OBJ)\blentry16.obj blentry16.asm

$(OBJ)\blentry16.com: $(OBJ)\blentry16.obj
	$(LINK16) /nologo /TINY $(OBJ)\blentry16.obj,$(OBJ)\blentry16.com,$(OBJ)\blentry16.map,,,/ONERROR:NOEXE /NOLOGO

$(OBJ)\bl.exe: $(OBJS)
	$(LINK) /nologo /debug /out:$(OBJ)\bl.exe /pdb:$(OBJ)\bl.pdb $(OBJS) /nodefaultlib /entry:BlEntry /subsystem:native /base:0x40000 /fixed /ignore:4078 /ignore:4254 /merge:.rdata=.data /merge:.data=.text

$(OBJ)\loader: $(OBJ)\bl.exe $(OBJ)\blentry16.com
	$(BLGEN) $(OBJ)\blentry16.com $(OBJ)\bl.exe $(OBJ)\loader

clean:
	cd $(OBJ)
	del *.com *.map *.lst *.obj *.cod *.pdb *.exe loader
	cd x86
	del *.lst *.obj

