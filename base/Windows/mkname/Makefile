##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\Mkname\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CFLAGS= $(CFLAGS) /I..\inc\
    /DWIN32 /DNT /Fd$(OBJDIR)\mkname.pdb \

HOST_LINKFLAGS= $(HOST_LINKFLAGS) /nod /libpath:..\lib /fixed:no /subsystem:console

LIBS=\
    kernel32.lib    \
    libcmt.lib        \

##############################################################################

.SUFFIXES: .cpp .obj

{.}.cpp{$(OBJDIR)}.obj:
    cl /c $(CFLAGS) /Fo$@ $<

##############################################################################

all: $(OBJDIR) $(OBJDIR)\mkname.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\mkname.exe
    $(SDEDIT) $(BUILDIR)\mkname.*
    $(COPY) $(OBJDIR)\mkname.exe $(BUILDIR)
    $(COPY) $(OBJDIR)\mkname.pdb $(BUILDIR)

##############################################################################

clean:
    @-del /q $(OBJDIR)\mkname.* *.exe pxe.com.1 *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

##############################################################################

test: $(OBJDIR) $(OBJDIR)\mkname.exe
    $(OBJDIR)\mkname /o:pxe.com.1 $(OBJDIR)\mkname.exe

$(OBJDIR)\mkname.exe : $(OBJDIR)\mkname.obj
    @echo Linking $@
    link $(HOST_LINKFLAGS) /out:$@ $** $(LIBS)

$(OBJDIR)\mkname.obj : mkname.cpp

################################################################# End of File.
