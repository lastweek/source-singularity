##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS=$(CFLAGS) /I..\inc \
    /Fd$(OBJDIR)\bootd.pdb

HOST_LINKFLAGS=$(HOST_LINKFLAGS) /nod /libpath:..\lib\x86 /subsystem:console

LIBS=\
     user32.lib     \
     kernel32.lib   \
     ws2_32.lib     \
     iphlpapi.lib   \
     libcmt.lib     \

##############################################################################

all: $(OBJDIR) $(OBJDIR)\bootd.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\bootd.exe
    $(SDEDIT) $(BUILDIR)\bootd.*
    $(COPY) $(OBJDIR)\bootd.exe $(BUILDIR)
    $(COPY) $(OBJDIR)\bootd.pdb $(BUILDIR)

clean:
    @-del /q $(OBJDIR)\bootd.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

test: $(OBJDIR) $(OBJDIR)\bootd.exe
    cd "$(MAKEDIR)\obj"
    boottest.cmd
    @cd "$(MAKEDIR)"


{.}.cpp{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

##########################################################################
#
# Build this version of the BMonitor
#

$(OBJDIR)\bootd.obj: bootd.cpp socksr.h dhcpd.h hashtab.h
$(OBJDIR)\socksr.obj: socksr.cpp socksr.h
$(OBJDIR)\hashtab.obj: hashtab.cpp hashtab.h
$(OBJDIR)\dhcpd.obj : dhcpd.cpp dhcpd.h socksr.h
$(OBJDIR)\tftpd.obj : tftpd.cpp tftpd.h socksr.h

OBJS = \
    $(OBJDIR)\dhcpd.obj \
    $(OBJDIR)\tftpd.obj \
    $(OBJDIR)\socksr.obj \
    $(OBJDIR)\bootd.obj \

$(OBJDIR)\bootd.exe: $(OBJS)
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

################################################################# End of File.
