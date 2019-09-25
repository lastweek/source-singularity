##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\mkmsil\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CSCFLAGS = /nologo $(CSFLAGS) /warn:2 

##############################################################################

all: $(OBJDIR) $(OBJDIR)\mkmsil.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\mkmsil.exe

##############################################################################

clean:
    @-del /q $(OBJDIR)\mkmsil.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul

##############################################################################

test: $(OBJDIR) $(OBJDIR)\mkmsil.exe
    $(OBJDIR)\mkmsil ..\..\shell\$(OBJDIR)\shell.dll

##############################################################################

REFERENCES=\

SOURCE_FILES=\
    mkmsil.cs \

$(OBJDIR)\mkmsil.exe : $(SOURCE_FILES)
    $(CSC) $(CSCFLAGS) $(REFERNCES) /out:$(OBJDIR)\mkmsil.exe $(SOURCE_FILES)

################################################################# End of File.
