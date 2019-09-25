##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\mkarmraw\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS = $(CFLAGS) \
    /I..\inc /I..\..\boot\include \
    /DWIN32 /DNT /Fd$(OBJDIR)\mkarmraw.pdb \

HOST_LINKFLAGS = $(HOST_LINKFLAGS) \
    /nologo /nod /libpath:..\lib /fixed:no /subsystem:console

LIBS = \
    kernel32.lib    \
    libcmt.lib        \

##############################################################################

.SUFFIXES: .cpp .obj

{.}.cpp{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

##############################################################################

all: $(OBJDIR) $(OBJDIR)\mkarmraw.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\mkarmraw.exe
    $(SDEDIT) ..\..\build\mkarmraw.exe
    $(SDEDIT) ..\..\build\mkarmraw.pdb
    $(COPY) $(OBJDIR)\mkarmraw.exe ..\..\build
    $(COPY) $(OBJDIR)\mkarmraw.pdb ..\..\build

##############################################################################

clean:
    @-del /q $(OBJDIR)\mkarmraw.* *.exe *.dmp *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

##############################################################################

test: $(OBJDIR) $(OBJDIR)\mkarmraw.exe
	copy test.exe x.exe
    $(OBJDIR)\mkarmraw.exe x.exe
	dumpbin /disasm x.exe | head -30

$(OBJDIR)\mkarmraw.exe : $(OBJDIR)\mkarmraw.obj
    @echo Linking $@
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

$(OBJDIR)\mkarmraw.obj : mkarmraw.cpp

################################################################# End of File.
