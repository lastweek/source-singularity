##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\SyscallBuilder\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CSCFLAGS = /nologo $(CSFLAGS) /warn:2 

##############################################################################

all: $(OBJDIR) $(OBJDIR)\SyscallBuilder.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\SyscallBuilder.exe
    $(SDEDIT) ..\..\build\SyscallBuilder.*
    $(COPY) $(OBJDIR)\SyscallBuilder.exe ..\..\build
    $(COPY) $(OBJDIR)\SyscallBuilder.pdb ..\..\build

##############################################################################

clean:
    @-del /q $(OBJDIR)\SyscallBuilder.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

##############################################################################

REFERENCES = /reference:System.Xml.dll /reference:System.dll

SOURCE_FILES = SyscallBuilder.cs

##############################################################################

$(OBJDIR)\SyscallBuilder.exe: $(SOURCE_FILES)
    $(CSC) $(CSCFLAGS) $(REFERENCES) /out:$(OBJDIR)\SyscallBuilder.exe $**
