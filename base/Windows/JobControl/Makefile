##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\JobControl\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

##############################################################################

all: $(OBJDIR) $(OBJDIR)\jobcontrol.exe

$(OBJDIR):
    mkdir $(OBJDIR)

clean:
    @-del /q $(OBJDIR)\jobcontrol.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

install: $(OBJDIR) $(OBJDIR)\jobcontrol.exe
    $(SDEDIT) ..\..\build\jobcontrol.*
    $(COPY) $(OBJDIR)\jobcontrol.exe ..\..\build
    $(COPY) $(OBJDIR)\jobcontrol.pdb ..\..\build

##############################################################################

CFLAGS=$(CFLAGS) /I..\inc /WX /W3 /Fd$(OBJDIR)\jobcontrol.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\lib\x86 /subsystem:console

LIBS=\
    kernel32.lib \
    user32.lib \
    libcmt.lib

##############################################################################

{.}.c{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

##########################################################################

$(OBJDIR)\jobcontrol.obj: jobcontrol.c

OBJS = \
    $(OBJDIR)\jobcontrol.obj \

$(OBJDIR)\jobcontrol.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)
