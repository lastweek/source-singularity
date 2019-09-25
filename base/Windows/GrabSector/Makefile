##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\GrabSector\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

##############################################################################

all: $(OBJDIR) $(OBJDIR)\grabsector.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

clean:
    @-del /q $(OBJDIR)\grabsector.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

install: $(OBJDIR) $(OBJDIR)\grabsector.exe
    $(SDEDIT) ..\..\build\grabsector.*
    $(COPY) $(OBJDIR)\grabsector.exe ..\..\build
    $(COPY) $(OBJDIR)\grabsector.pdb ..\..\build

##############################################################################

CFLAGS=$(CFLAGS) /I..\inc \
    /Fd$(OBJDIR)\grabsector.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\lib\x86 /subsystem:console

LIBS=\
     user32.lib     \
     kernel32.lib   \
     advapi32.lib   \
     libcmt.lib     \

##############################################################################


{.}.cpp{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

##########################################################################

$(OBJDIR)\grabsector.obj: grabsector.cpp

OBJS = \
    $(OBJDIR)\grabsector.obj \

$(OBJDIR)\grabsector.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)
