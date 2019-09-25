##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\RunAll\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

##############################################################################

all: $(OBJDIR) $(OBJDIR)\runall.exe

$(OBJDIR):
    mkdir $(OBJDIR)

clean:
    @-del /q $(OBJDIR)\runall.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

install: $(OBJDIR) $(OBJDIR)\runall.exe
    $(SDEDIT) ..\..\build\runall.*
    $(COPY) $(OBJDIR)\runall.exe ..\..\build
    $(COPY) $(OBJDIR)\runall.pdb ..\..\build

##############################################################################

CFLAGS=$(CFLAGS) /I..\inc /WX /W3 /Fd$(OBJDIR)\runall.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\lib\x86 /subsystem:console

LIBS=\
    kernel32.lib \
    user32.lib \
    libcmt.lib

##############################################################################

{.}.c{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

##########################################################################

$(OBJDIR)\runall.obj: runall.c

OBJS = \
    $(OBJDIR)\runall.obj \

$(OBJDIR)\runall.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)
