##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Windows\Makefile
#
##############################################################################

OBJROOT=.\obj
!INCLUDE "$(SINGULARITY_ROOT)/Makefile.inc"

# There is a subset of directories that are just for internal
# use and these are conditionalized below.  We also use
# nmake_dirs to simplify variable numbers of sub-directories to
# build.  Note: the build of nmake_dirs needs to be done
# independently of running nmake_dirs so it handled on its own
# in the standard target rules : all, install, clean.

!IF ("$(SINGULARITY_INTERNAL)" == "Yes")
INTERNAL_SUBDIRS =			\
    $(MAKEDIR)\DbgDbg 			\
    $(MAKEDIR)\pfilter 			\
    $(MAKEDIR)\PowerSwitchService 	\
    $(MAKEDIR)\sdizepdb
!ELSE
INTERNAL_SUBDIRS =
!ENDIF

SUBDIRS=				\
    $(MAKEDIR)\bootd    		\
    $(MAKEDIR)\distrobuilder    	\
    $(MAKEDIR)\grabsector    		\
    $(MAKEDIR)\jobcontrol    		\
    $(MAKEDIR)\mkasm    		\
    $(MAKEDIR)\mkcontagmap    		\
    $(MAKEDIR)\mkmani    		\
    $(MAKEDIR)\mutexwrap    		\
    $(MAKEDIR)\nib    			\
    $(MAKEDIR)\substitute    		\
    $(MAKEDIR)\mkpxecom    		\
    $(MAKEDIR)\ProfMap    		\
    $(MAKEDIR)\RefGraph    		\
    $(MAKEDIR)\rialto    		\
    $(MAKEDIR)\RunAll    		\
    $(MAKEDIR)\RunParallel    		\
    $(MAKEDIR)\setvhdboot    		\
    $(MAKEDIR)\singx86    		\
    $(MAKEDIR)\spg    			\
    $(MAKEDIR)\SyscallBuilder    	\
    $(MAKEDIR)\MpSyscallBuilder    	\
    $(MAKEDIR)\Verifier    		\
    $(INTERNAL_SUBDIRS)

all: $(OBJDIR)
    @nmake_dirs $(SUBDIRS)
    cd $(MAKEDIR)\nmake_dirs
    @$(MAKE) /NOLOGO /$(MAKEFLAGS)
    @cd "$(MAKEDIR)"

$(OBJDIR):
    @if not exist $(OBJDIR) mkdir $(OBJDIR)

# Please keep directories sorted by alphabetical order where possible.
clean:
    @nmake_dirs $(SUBDIRS) /nmake clean
    cd $(MAKEDIR)\nmake_dirs
    @$(MAKE) /NOLOGO /$(MAKEFLAGS) clean
    -rmdir /q /s $(OBJDIR) 2>nul
    @-rmdir $(OBJROOT) 2>nul
    -rmdir /q /s "$(MAKEDIR)\SimpleParseGen" 2>nul
    @-del *~ 2> nul

# Please keep directories sorted by alphabetical order where possible.
realclean:
    -rmdir /q /s $(OBJROOT) 2>nul
    @-del /s *~ 2> nul

# Please keep directories sorted by alphabetical order where possible.
install:
    @nmake_dirs $(SUBDIRS) /nmake install
    cd $(MAKEDIR)\nmake_dirs
    @$(MAKE) /NOLOGO /$(MAKEFLAGS) install
    @cd "$(MAKEDIR)"

################################################################# End of File.
