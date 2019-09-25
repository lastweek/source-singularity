##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\DumpWav\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS=$(CFLAGS) /W4 /I..\inc \
    -DWIN32 -DNT $(CPPFLAGS)  /Fd$(OBJDIR)\dumpwav.pdb

HOST_LINKFLAGS= $(HOST_LINKFLAGS) /nod /libpath:..\lib /subsystem:console

LIBS=\
    kernel32.lib    \
    libcmt.lib        \


##############################################################################

.SUFFIXES: .cpp .obj

{.}.cpp{obj}.obj:
    $(CC) /c /nologo $(CFLAGS) /Fo$@ $<

##############################################################################

all: $(OBJDIR) $(OBJDIR)\dumpwav.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\dumpwav.exe
    $(COPY) $(OBJDIR)\dumpwav.exe ..\..\build
    $(COPY) $(OBJDIR)\dumpwav.pdb ..\..\build

##############################################################################

clean:
    @-del /q $(OBJDIR)\dumpwav.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

##############################################################################

test: $(OBJDIR)\dumpwav.exe doit

doit: c:\*.wav c:\windows\media\*.wav
    $(OBJDIR)\dumpwav.exe $**

$(OBJDIR)\dumpwav.exe : $(OBJDIR)\dumpwav.obj
    @echo Linking $@
    link $(HOST_LINKFLAGS) /out:$@ $(OBJDIR)\dumpwav.obj $(LIBS)

$(OBJDIR)\dumpwav.obj : dumpwav.cpp

################################################################# End of File.
