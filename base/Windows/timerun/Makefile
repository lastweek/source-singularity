##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\timerun\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CSCFLAGS = /nologo $(CSFLAGS) /warn:2 /unsafe

##############################################################################

all: $(OBJDIR) $(OBJDIR)\timerun.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

copy: $(OBJDIR) $(OBJDIR)\timerun.exe
    $(COPY) $(OBJDIR)\timerun.exe ..\..\build
    $(COPY) $(OBJDIR)\timerun.pdb ..\..\build


install: $(OBJDIR) $(OBJDIR)\timerun.exe
    $(SDEDIT) ..\..\build\timerun.*
    $(COPY) $(OBJDIR)\timerun.exe ..\..\build
    $(COPY) $(OBJDIR)\timerun.pdb ..\..\build


##############################################################################

clean:
    @-del /q $(OBJDIR)\timerun.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

##############################################################################

REFERENCES = \
    /reference:System.Xml.dll \
    /reference:System.dll \


SOURCE_FILES = \
    timerun.cs \
    ..\WindowsInteropLib\Kernel32.cs \
        

##############################################################################

$(OBJDIR)\timerun.exe: $(SOURCE_FILES) Makefile
    $(CSC) $(CSCFLAGS) $(REFERENCES) /out:$(OBJDIR)\timerun.exe $(SOURCE_FILES)

##############################################################################
