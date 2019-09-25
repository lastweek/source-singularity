##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\Benchmarks\gulp\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS=$(CFLAGS) /Ox /I..\inc \
    /Fd$(OBJDIR)\gulp.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\lib /subsystem:console

LIBS=\
     user32.lib     \
     kernel32.lib   \
     libcmt.lib     \
     ws2_32.lib     \
##############################################################################

all: $(OBJDIR) $(OBJDIR)\gulp.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

clean:
    @-del /q $(OBJDIR)\gulp.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

{.}.c{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

$(OBJDIR)\gulp.obj: gulp.c

OBJS = \
    $(OBJDIR)\gulp.obj \

$(OBJDIR)\gulp.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

##############################################################################
