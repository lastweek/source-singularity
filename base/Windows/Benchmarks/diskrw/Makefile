##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\Benchmarks\diskrw\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CDEBUGFLAGS=/nologo /W3 /WX /Zi /Gy /Od /I..\..\inc \
    /Fd$(OBJDIR)\diskrw.pdb

CFLAGS=$(CFLAGS) /Ox /I..\..\inc \
    /Fd$(OBJDIR)\diskrw.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\..\lib /subsystem:console
LINKDEBUGFLAGS=$(HOST_LINKFLAGS) /debug

LIBS=\
     user32.lib     \
     kernel32.lib   \
     advapi32.lib   \
     libcmt.lib     \

##############################################################################

all: $(OBJDIR) $(OBJDIR)\diskrw.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

clean:
    @-del /f /q $(OBJDIR)\diskrw.* *~ 2> nul
    -rmdir $(OBJDIR) 2>nul
    -rmdir $(OBJROOT) 2>nul

{.}.cpp{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

##########################################################################
#
# Build this version of the BMonitor
#

$(OBJDIR)\diskrw.obj: diskrw.cpp srandom.hpp

OBJS = \
    $(OBJDIR)\diskrw.obj \

$(OBJDIR)\diskrw.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

##############################################################################

test: $(OBJDIR) $(OBJDIR)\diskrw.exe
    $(OBJDIR)\diskrw.exe /r /m:10 /b:512 c:

################################################################# End of File.
