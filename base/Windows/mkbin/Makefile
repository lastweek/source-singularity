##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\mkbin\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS = $(CFLAGS) \
    /I..\inc /I..\..\boot\include \
    /DWIN32 /DNT /Fd$(OBJDIR)\mkbin.pdb \

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

all: $(OBJDIR) $(OBJDIR)\mkbin.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\mkbin.exe
    $(SDEDIT) ..\..\build\mkbin.exe
    $(SDEDIT) ..\..\build\mkbin.pdb
    $(COPY) $(OBJDIR)\mkbin.exe ..\..\build
    $(COPY) $(OBJDIR)\mkbin.pdb ..\..\build

##############################################################################

clean:
    @-del /q $(OBJDIR)\mkbin.* *.exe *.dmp *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

##############################################################################

$(OBJDIR)\mkbin.exe : $(OBJDIR)\mkbin.obj
    @echo Linking $@
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

$(OBJDIR)\mkbin.obj : mkbin.cpp

################################################################# End of File.
