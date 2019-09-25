##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\Mkasm\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS=$(CFLAGS) /I..\inc\
    -DWIN32 -DNT /Fd$(OBJDIR)\mkasm.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\lib /subsystem:console

LIBS=\
    kernel32.lib    \
    libcmt.lib        \

##############################################################################

.SUFFIXES: .cpp .obj

{.}.cpp{$(OBJDIR)}.obj:
    $(HOST_CC) /c /nologo $(CFLAGS) /Fo$@ $<

##############################################################################

all: $(OBJDIR) $(OBJDIR)\mkasm.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\mkasm.exe
    $(SDEDIT) ..\..\build\mkasm.*
    $(COPY) $(OBJDIR)\mkasm.exe ..\..\build
    $(COPY) $(OBJDIR)\mkasm.pdb ..\..\build

##############################################################################

clean:
    @-del /q $(OBJDIR)\mkasm.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

##############################################################################

test: $(OBJDIR) $(OBJDIR)\mkasm.exe
    $(OBJDIR)\mkasm /o:test.asm /b /l /n:Microsoft.Singularity /c:Shell /f:Logo /a slide1.bmp slide2.bmp slide3.bmp
    ml /c test.asm

test1: $(OBJDIR) $(OBJDIR)\mkasm.exe $(OBJDIR)\test.exe
    $(OBJDIR)\mkasm -o:$(OBJDIR)\test.asm -r:TEST $(OBJDIR)\test.exe

$(OBJDIR)\mkasm.exe : $(OBJDIR)\mkasm.obj
    @echo Linking $@
    link $(HOST_LINKFLAGS) /out:$@ $(OBJDIR)\mkasm.obj $(LIBS)

$(OBJDIR)\test.exe : $(OBJDIR)\mkasm.obj
    @echo Linking $@
    link $(HOST_LINKFLAGS) /out:$@ $(OBJDIR)\mkasm.obj $(LIBS) \
        /base:0x60000 /fixed /ignore:4078,4096 \
        /merge:.rdata=.data /merge:.bss=.data /merge:.data=.text


$(OBJDIR)\mkasm.obj : mkasm.cpp

################################################################# End of File.
