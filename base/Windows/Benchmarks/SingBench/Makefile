##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\Benchmarks\SingBench\Makefile
#
##############################################################################

OBJROOT=..\..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS=$(CFLAGS) /I..\..\inc \
    /Fd$(OBJDIR)\SingBench.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS)/nod /libpath:..\..\lib /subsystem:console

LIBS=\
     user32.lib     \
     kernel32.lib   \
     libcmt.lib     \

##############################################################################

all: $(OBJDIR) $(OBJDIR)\SingBench.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

clean:
    @-del /q $(OBJDIR)\SingBench.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

{.}.c{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

$(OBJDIR)\SingBench.obj: SingBench.c

OBJS = \
    $(OBJDIR)\SingBench.obj \

$(OBJDIR)\SingBench.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

##############################################################################
