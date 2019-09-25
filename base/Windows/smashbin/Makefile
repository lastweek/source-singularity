##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\smashbin\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS = $(CFLAGS) \
    /I..\inc /I..\..\boot\include \
    /DWIN32 /DNT /Fd$(OBJDIR)\smashbin.pdb \

HOST_LINKFLAGS = $(HOST_LINKFLAGS) \
    /nologo /nod /libpath:..\lib\x86 /fixed:no /subsystem:console

LIBS = \
    kernel32.lib    \
    libcmt.lib        \

##############################################################################

.SUFFIXES: .cpp .obj

{.}.cpp{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

##############################################################################

all: $(OBJDIR) $(OBJDIR)\smashbin.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\smashbin.exe
    $(SDEDIT) ..\..\build\smashbin.exe
    $(SDEDIT) ..\..\build\smashbin.pdb
    $(COPY) $(OBJDIR)\smashbin.exe ..\..\build
    $(COPY) $(OBJDIR)\smashbin.pdb ..\..\build

##############################################################################

clean:
    @-del /q $(OBJDIR)\smashbin.* *.exe *.dmp *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

##############################################################################

$(OBJDIR)\smashbin.exe : $(OBJDIR)\smashbin.obj
    @echo Linking $@
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

$(OBJDIR)\smashbin.obj : smashbin.cpp

################################################################# End of File.
