##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\Benchmarks\Hello\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS=$(CFLAGS) /Od /I..\..\inc \
    /Fd$(OBJDIR)\Hello.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\..\lib /subsystem:console

LIBS=\
     user32.lib     \
     kernel32.lib   \
     libcmt.lib     \

##############################################################################

all: $(OBJDIR) $(OBJDIR)\Hello.exe

clean:
    @-del /q $(OBJDIR)\Hello.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

$(OBJDIR):
    -mkdir $(OBJDIR)

{.}.c{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

$(OBJDIR)\Hello.obj: Hello.c

OBJS = \
    $(OBJDIR)\Hello.obj \

$(OBJDIR)\Hello.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

################################################################# End of File.
