##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\Benchmarks\CreateProcess\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS= $(CFLAGS) /Ox /I..\..\inc

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\..\lib /subsystem:console

LIBS=\
     user32.lib     \
     kernel32.lib   \
     libcmt.lib     \

##############################################################################

all: $(OBJDIR) \
     $(OBJDIR)\CreateProcess.exe \
     $(OBJDIR)\Child.exe \
     $(OBJDIR)\MinProcess.exe

clean:
    @-del /q $(OBJDIR)\CreateProcess.* $(OBJDIR)\Child.* $(OBJDIR)\MinProcess.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

$(OBJDIR):
    -mkdir $(OBJDIR)

{.}.c{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

$(OBJDIR)\CreateProcess.obj: CreateProcess.c

$(OBJDIR)\Child.obj: Child.c

$(OBJDIR)\MinProcess.obj: MinProcess.c

OBJS = \
    $(OBJDIR)\CreateProcess.obj \

$(OBJDIR)\CreateProcess.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

$(OBJDIR)\Child.exe: $(OBJDIR)\Child.obj
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

$(OBJDIR)\MinProcess.exe: $(OBJDIR)\MinProcess.obj
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

################################################################# End of File.
