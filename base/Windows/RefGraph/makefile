##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\RefGraph\Makefile
#
##############################################################################

OBJROOT=..\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

CSCFLAGS = /nologo $(CSFLAGS) /warn:2 /warnaserror+

SGC = sgc

SGCFLAGS = /nologo $(CSFLAGS) /warn:2 /warnaserror+ \
     /r:$(BUILDIR)\sgc\system.compiler.dll \

##############################################################################

all: $(OBJDIR) $(OBJDIR)\refgraph.exe

$(OBJDIR):
    -mkdir $(OBJDIR)

install: $(OBJDIR) $(OBJDIR)\refgraph.exe
    $(SDEDIT) $(BUILDIR)\refgraph.exe
    $(SDEDIT) $(BUILDIR)\refgraph.pdb
    $(COPY) $(OBJDIR)\refgraph.exe $(BUILDIR)
    $(COPY) $(OBJDIR)\refgraph.pdb $(BUILDIR)

!IF ("$(FRAMEWORK_VERSION)" == "v2")
SOURCE_FILES = \
    refgraph8.sg \
!ELSE
SOURCE_FILES = \
    refgraph.sg \
!ENDIF

$(OBJDIR)\refgraph.exe: $(SOURCE_FILES)
    $(SGC) $(SGCFLAGS) /out:$(OBJDIR)\refgraph.exe $**

##############################################################################

clean:
    @-del /q $(OBJDIR)\RefGraph.* *~ 2>nul
    @-rmdir $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul
