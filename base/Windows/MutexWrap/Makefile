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

all: $(OBJDIR) $(OBJDIR)\mutexwrap.exe

$(OBJDIR):
    mkdir $(OBJDIR)

clean:
    @-del /q $(OBJDIR)\mutexwrap.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

install: $(OBJDIR) $(OBJDIR)\mutexwrap.exe
    $(SDEDIT) ..\..\build\mutexwrap.*
    $(COPY) $(OBJDIR)\mutexwrap.exe ..\..\build
    $(COPY) $(OBJDIR)\mutexwrap.pdb ..\..\build

##############################################################################

CFLAGS=$(CFLAGS) /I..\inc /WX /W3 /Fd$(OBJDIR)\mutexwrap.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\lib /subsystem:console

LIBS=\
    kernel32.lib \
    libcmt.lib

##############################################################################

{.}.c{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

##########################################################################

$(OBJDIR)\mutexwrap.obj: mutexwrap.c

OBJS = \
    $(OBJDIR)\mutexwrap.obj \

$(OBJDIR)\mutexwrap.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)
