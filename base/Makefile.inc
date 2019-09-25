##############################################################################
#
#   Microsoft Research Singularity
#
#   Copyright (c) Microsoft Corporation.  All rights reserved.
#
#   File:   Makefile.inc
#
#   Note:
#
#   This top-level file is included by all Makefile's in the project and
#   contains all configurable options.  All options are overrideable
#   through environment variables.
#
#   Configuration Options
#       ASMP_SYSCALL_BUILDER -- Specify asymmetric system call stub generator
#       BARTOK     -- Specify a particular bartok compiler
#       BUILDTYPE  -- Specify build type (Debug|Release)
#       COLLECTOR_KERNEL  -- Specify garbage collector for kernel
#                              (Concurrent|MarkSweep|Semispace)
#       COLLECTOR_APP     -- Specify garbage collector for applications
#                              (Concurrent|MarkSweep|Semispace)
#       PLATFORM   -- Specify host platform (LegacyPC|ApicPC|ApicMP|Apic64|CEPC)
#       SCHEDULER  -- Specify scheduler type (Affinity|Rialto|Min|Robin|Laxity)
#       SYSCALL_BUILDER -- Specify system call stub generator
#       OBJROOT    -- Specify directory in which to place objects (optional)
#       PAGING     -- Specify page translation (On|Off)
#
#   Resulting NMAKE macros passed to Makefiles
#       OBJRELDIR  -- relative path of full qualify object directory
#       OBJKRNDIR  -- relative path of full qualify object directory for kernel
#       OBJDIR     -- relative path of object directory from source directory
#       KOBJDIR    -- relative path of kernel object directory from source directory
#       PRIDIR     -- relative path of private object directory from source directory
#       CSFLAGS    -- flags passed to c# compilers
#       SGFLAGS    -- flags passed to Sing# compilers
#
#       BASEDIR    -- Root of Singularity source tree
#       BOOTDIR    -- Directory containing compiled boot assemblies.
#       KERNDIR    -- Directory containing compiled kernel assemblies.
#       KABIDIR    -- Directory containing compiled kernel ABI libraries.
#       DISTDIR    -- Directory containing compiled distribution files.
#       DRIVDIR    -- Directory containing compiled driver assemblies.
#       CONSDIR    -- Directory containing compiled contract assemblies.
#       ILLSDIR    -- Directory containing compiled ILL assemblies.
#       LIBSDIR    -- Directory containing compiled library assemblies.
#       APPSDIR    -- Directory containing compiled application assemblies.
#       SERVDIR    -- Directory containing compiled service assemblies.
#       WINSDIR    -- Directory containing compiled Windows assemblies.
#       OPTSDIR    -- Directory containing the system options definitions.
#       BUILDIR    -- Directory containing the build tools.
#
##############################################################################

.SUFFIXES : .c .exe .x86 .cs .il .ill .dll .obj .asm .cpp .h .manifest .options

###############################################################################
# Configuration option handling - sets defaults and checks values

# ASMP_SYSCALL_BUILDER = "MpSyscallBuilder"

DEFAULT_ASMP_SYSCALL_BUILDER = "MpSyscallBuilder"

!IF !DEFINED(ASMP_SYSCALL_BUILDER)
ASMP_SYSCALL_BUILDER = $(DEFAULT_ASMP_SYSCALL_BUILDER)
!ENDIF

# BARTOK = "bartok"

!IF ("$(PLATFORM)" == "Apic64")
DEFAULT_BARTOK = $(SINGULARITY_ROOT)\build\x86_x64\bartok\bartok.exe
!ELSE
DEFAULT_BARTOK = $(SINGULARITY_ROOT)\build\x86_x86\bartok\bartok.exe
!ENDIF

!IF !DEFINED(BARTOK)
BARTOK = $(DEFAULT_BARTOK)
!ENDIF

# BUILDTYPE = "Debug"* | "Release"

DEFAULT_BUILDTYPE=Debug

!IF !DEFINED(BUILDTYPE)
BUILDTYPE=$(DEFAULT_BUILDTYPE)
!ENDIF

!IF ("$(BUILDTYPE)" != "Debug") && \
        ("$(BUILDTYPE)" != "Release") && \
        ("$(BUILDTYPE)" != "Prototype")
!ERROR BUILDTYPE must either be unset, or set to one of "Debug", "Release", or "Prototype".
!endif

# COLLECTOR_KERNEL|_APP = "AdaptiveCopying" | "Concurrent"* | "MarkSweep" | "Semispace" |
#             "Sliding"
DEFAULT_COLLECTOR_KERNEL=Concurrent
DEFAULT_COLLECTOR_APP=MarkSweep

!IF !DEFINED(COLLECTOR_KERNEL)
COLLECTOR_KERNEL=$(DEFAULT_COLLECTOR_KERNEL)
!ENDIF

!IF !DEFINED(COLLECTOR_APP)
COLLECTOR_APP=$(DEFAULT_COLLECTOR_APP)
!ENDIF

!IF ("$(COLLECTOR_KERNEL)" != "AdaptiveCopying" && \
     "$(COLLECTOR_KERNEL)" != "Concurrent" && \
     "$(COLLECTOR_KERNEL)" != "MarkSweep" && \
     "$(COLLECTOR_KERNEL)" != "Semispace" && \
     "$(COLLECTOR_KERNEL)" != "Sliding")
!ERROR COLLECTOR_KERNEL must either be unset, or set to one of "AdaptiveCopying" or "Concurrent" or "MarkSweep" or "Semispace" or "Sliding"
!ENDIF

!IF ("$(COLLECTOR_APP)" != "AdaptiveCopying" && \
     "$(COLLECTOR_APP)" != "Concurrent" && \
     "$(COLLECTOR_APP)" != "MarkSweep" && \
     "$(COLLECTOR_APP)" != "Semispace" && \
     "$(COLLECTOR_APP)" != "Sliding")
!ERROR COLLECTOR_APP must either be unset, or set to one of "AdaptiveCopying" or "Concurrent" or "MarkSweep" or "Semispace" or "Sliding"
!ENDIF

# PLATFORM = "LegacyPC"* | "ApicPC"

DEFAULT_PLATFORM=LegacyPC

!IF !DEFINED(PLATFORM)
PLATFORM=$(DEFAULT_PLATFORM)
!ENDIF

!IF ("$(PLATFORM)" != "LegacyPC" && \
     "$(PLATFORM)" != "ApicPC" && \
     "$(PLATFORM)" != "ApicMP" && \
     "$(PLATFORM)" != "Apic64" && \
     "$(PLATFORM)" != "CEPC")
!ERROR PLATFORM must either be unset, or set to one of "LegacyPC" or "ApicPC" or "ApicMP" or "Apic64" or "CEPC".
!endif

!IF "$(PLATFORM)" == "ApicMP" && !DEFINED(MAX_CPU)
MAX_CPU=4
!endif

!IF "$(PLATFORM)" == "Apic64" && !DEFINED(MAX_CPU)
MAX_CPU=4
!endif

# SCHEDULER = "Affinity" | "Rialto"* | "Robin" | "Laxity" | "Min"

DEFAULT_SCHEDULER=Min

!IF !DEFINED(SCHEDULER)
SCHEDULER=$(DEFAULT_SCHEDULER)
!ENDIF

!IF ("$(SCHEDULER)" != "Rialto") && ("$(SCHEDULER)" != "Robin") && ("$(SCHEDULER)" != "Laxity") && ("$(SCHEDULER)" != "Min") && ("$(SCHEDULER)" != "Affinity")
!ERROR SCHEDULER must either be unset, or set to one of "Affinity", "Rialto", "Robin", "Laxity", or "Min".
!endif

# SYSCALL_BUILDER = SyscallBuilder

DEFAULT_SYSCALL_BUILDER = SyscallBuilder

!IF !DEFINED(SYSCALL_BUILDER)
SYSCALL_BUILDER = $(DEFAULT_SYSCALL_BUILDER)
!ENDIF

DEFAULT_PAGING_FLAG=

###############################################################################
# Resulting NMAKE macros

CSC = csc

SGFLAGS = /disable:nullparametervalidation

AFLAGS = /nologo /Zi /Cp /DSINGULARITY=1
CFLAGS = /D_CRT_SECURE_NO_DEPRECATE /nologo /W3 /WX /Gy /Zi /Oy- /GS- /DSINGULARITY=1 $(CC_FLAGS_64)

#
# Enable optimizations only on release builds.
#
# AIFIX: Building with optimizations disabled does not work!
#

!IF ("$(BUILDTYPE)" == "Release")
CFLAGS = $(CFLAGS) /O2
!ELSE
# CFLAGS = $(CFLAGS) /Od
CFLAGS = $(CFLAGS) /O2
!ENDIF

#
#  HOST_LINKFLAGS is for the machine we are building on
#  used to build the windows components
#  We always want debug symbols, thus the /debug flag.
#
HOST_LINKFLAGS = /NOLOGO /INCREMENTAL:NO /machine:X86 /DEBUG /DEBUGTYPE:CV
HOST_CC = cl

!IF "$(PLATFORM)" == "Apic64"
BARTOK_FLAGS = /x64 $(BARTOK_FLAGS)
BARTOK_FLAGS = /IrImproveTypes=false $(BARTOK_FLAGS)
!ENDIF

LINKFLAGS = /NOLOGO /INCREMENTAL:NO /machine:$(MACHINE)
LINKFLAGS64 = /NOLOGO /INCREMENTAL:NO /machine:x64

CPPFLAGS = $(CFLAGS)

# Workaround for bug in Bartok drop @5063
BARTOK_FLAGS=$(BARTOK_FLAGS) /IrPeepholeNull=false

!IF ("$(BUILDTYPE)" == "Debug")
BARTOK_FLAGS = $(BARTOK_FLAGS)
CSFLAGS = /debug /d:DEBUG /d:TRACING /d:WAYPOINTS /d:MONITORING /d:CHANNEL_COUNT
CPPFLAGS = /DDEBUG
LINKDFLAGS = /DEBUG /DEBUGTYPE:CV
CFLAGS = $(CFLAGS) /DDEBUG
LINKFLAGS = $(LINKFLAGS) /DEBUG /DEBUGTYPE:CV
LINKFLAGS64 = $(LINKFLAGS64) /DEBUG /DEBUGTYPE:CV
AFLAGS = $(AFLAGS) /DDEBUG=1
!ELSE IF ("$(BUILDTYPE)" == "Prototype")
BARTOK_FLAGS = $(BARTOK_FLAGS) /minopt /IrSimpleInliner=false
CSFLAGS = /debug /d:DEBUG /d:TRACING /d:WAYPOINTS /d:MONITORING /d:CHANNEL_COUNT
CFLAGS = $(CFLAGS) /DDEBUG
LINKFLAGS = $(LINKFLAGS) /DEBUG /DEBUGTYPE:CV
LINKFLAGS64 = $(LINKFLAGS64) /DEBUG /DEBUGTYPE:CV
AFLAGS = $(AFLAGS) /DDEBUG=1
!ELSE IF ("$(BUILDTYPE)" == "Release")
BARTOK_FLAGS = $(BARTOK_FLAGS)
CSFLAGS = /debug /d:CHANNEL_COUNT
#CSFLAGS = /debug /d:WAYPOINTS
SGFLAGS = $(SGFLAGS) # /disable:ac,dc,gcc,ic
CFLAGS = $(CFLAGS)
LINKFLAGS = $(LINKFLAGS) /DEBUG /DEBUGTYPE:CV
LINKFLAGS64 = $(LINKFLAGS64) /DEBUG /DEBUGTYPE:CV
AFLAGS = $(AFLAGS)
!ENDIF

#### THREAD_TIME_ACCOUNTING = 1
!IF DEFINED(THREAD_TIME_ACCOUNTING)
AFLAGS = $(AFLAGS) /DTHREAD_TIME_ACCOUNTING=1
CFLAGS = $(CFLAGS) /DTHREAD_TIME_ACCOUNTING=1
CSFLAGS = $(CSFLAGS) /d:THREAD_TIME_ACCOUNTING
SGFLAGS = $(SGFLAGS)
!ENDIF

!IF DEFINED(SAMPLE_PC)
CSFLAGS = $(CSFLAGS) /d:SAMPLE_PC
SGFLAGS = $(SGFLAGS) /d:SAMPLE_PC
!endif

!IF ("$(PLATFORM)" == "EnlightenedPC")
CSFLAGS = $(CSFLAGS) /d:HACKS_FOR_S
SGFLAGS = $(SGFLAGS) /d:HACKS_FOR_S
CFLAGS = $(CFLAGS) /DHACKS_FOR_S
AFLAGS = $(AFLAGS) /DHACKS_FOR_S=1
!ENDIF

!IF "$(PLATFORM)" == "Apic64"
CC_FLAGS_64 = /DISA_X64=1 /DPTR_SIZE_64=1
AFLAGS = $(AFLAGS) /DISA_X64=1 /DPTR_SIZE_64=1
CPPFLAGS=$(CPPFLAGS) /DISA_X64=1 /DPTR_SIZE_64=1 /DUSE_64=1
CSFLAGS=$(CSFLAGS) /D:ISA_X64  /D:PTR_SIZE_64  /D:USE_64
AS = $(SINGULARITY_ROOT)\build\x86_x64\ml64.exe
CC = $(SINGULARITY_ROOT)\build\x86_x64\cl.exe
CFLAGS = $(CFLAGS) /DISA_X64 /DPTR_SIZE_64 /DUSE_64
ARCH_DIR=x64
MACHINE=x64
SING_DEF_FILE=singularity64.V1.def
LINK = $(SINGULARITY_ROOT)\build\x86_x64\link.exe
AS   = $(SINGULARITY_ROOT)\build\x86_x64\ml64.exe
LIB  = $(SINGULARITY_ROOT)\build\x86_x64\lib.exe
!ELSE
MACHINE=x86
AS=ml
LINK=link
LIB=lib
ARCH_DIR=.
SING_DEF_FILE=singularity.V1.def
!ENDIF

!IF ("$(PAGING)" == "On")
PAGING_FLAG = .Paging
AFLAGS = $(AFLAGS) /DPAGING=1
CFLAGS = $(CFLAGS) /DPAGING
CSFLAGS = $(CSFLAGS) /d:PAGING
SGFLAGS = $(SGFLAGS) /d:PAGING
!ELSE
PAGING_FLAG =
!ENDIF

#
# Only cross reference binaries with source depot on internal
# builds.  The source depot is not available outside of
# Microsoft.
#
!IF ("$(SINGULARITY_INTERNAL)" == "Yes")
SDIZEPDB = sdizepdb.exe
SDEDIT = sd edit
!ELSE
SDIZEPDB = @rem sdizepdb
SDEDIT = attrib -r
!ENDIF
COPYCMD = copy /y 1>nul

#
# In case a makefile does not define SGCFLAGS in terms of SGFLAGS
# (I found that the Contracts directory does not.)
# (Alternatively, we could change SGCFLAGS in the App makefiles to SGFLAGS)
#
SGCFLAGS = $(SGFLAGS)

OBJKRNDIR=$(BUILDTYPE).$(MACHINE).$(PLATFORM).$(SCHEDULER).$(COLLECTOR_KERNEL)$(PAGING_FLAG)
OBJRELRUNTIMEDIR=$(BUILDTYPE).$(MACHINE).$(COLLECTOR_APP)$(PAGING_FLAG)

#OBJRELDIR=$(BUILDTYPE).$(COLLECTOR_APP)$(PAGING_FLAG)
OBJRELDIR=$(BUILDTYPE).$(MACHINE).$(COLLECTOR_APP)$(PAGING_FLAG)

OBJMACHINERELDIR=$(BUILDTYPE).$(MACHINE)$(PAGING_FLAG)
OBJOPT=$(BUILDTYPE).$(COLLECTOR_APP)

# If the user has not defined OBJDIR, then try to discover it.
# Makefiles exist somewhere between a declarative language and
# a Turing-complete language...  without looping, this is the
# best we can do.  This allows us to write per-component
# Makefiles that do not specify OBJROOT.
!IF !DEFINED(OBJROOT)
!IF EXIST("..\Makefile.computeDeps")
OBJROOT=obj
!ELSEIF EXIST("..\..\Makefile.computeDeps")
OBJROOT=..\obj
!ELSEIF EXIST("..\..\..\Makefile.computeDeps")
OBJROOT=..\..\obj
!ELSEIF EXIST("..\..\..\..\Makefile.computeDeps")
OBJROOT=..\..\..\obj
!ELSEIF EXIST("..\..\..\..\..\Makefile.computeDeps")
OBJROOT=..\..\..\..\obj
!ELSEIF EXIST("..\..\..\..\..\..\Makefile.computeDeps")
OBJROOT=..\..\..\..\..\obj
!ELSEIF EXIST("..\..\..\..\..\..\..\Makefile.computeDeps")
OBJROOT=..\..\..\..\..\..\obj
!ELSEIF EXIST("..\..\..\..\..\..\..\..\Makefile.computeDeps")
OBJROOT=..\..\..\..\..\..\..\obj
!ELSEIF EXIST("..\..\..\..\..\..\..\..\..\Makefile.computeDeps")
OBJROOT=..\..\..\..\..\..\..\..\obj
!ELSEIF EXIST("..\..\..\..\..\..\..\..\..\..\Makefile.computeDeps")
OBJROOT=..\..\..\..\..\..\..\..\..\obj
!ELSE
!ERROR Unable to find ...\Makefile.computeDeps - please edit the hack in Makefile.computeDeps
!ENDIF
!ENDIF

KOBJDIR=$(OBJROOT)\$(OBJKRNDIR)
KPRIDIR=$(OBJROOT)\$(OBJKRNDIR)\private

OBJDIR=$(OBJROOT)\$(OBJRELDIR)

OBJARCHDIR = $(OBJROOT)\$(OBJMACHINERELDIR)
PRIDIR=$(OBJROOT)\$(OBJRELRUNTIMEDIR)\private
BINDIR=$(OBJROOT)\$(OBJRELRUNTIMEDIR)

HAL_DLL=Hal.$(PLATFORM).dll

###############################################################################
# Directories for publishing and retrieving compiled assemblies.

BASEDIR=$(SINGULARITY_ROOT)
BOOTDIR=$(BASEDIR)\Boot\obj\$(OBJKRNDIR)
KERNDIR=$(BASEDIR)\Kernel\obj\$(OBJKRNDIR)
#KABIDIR=$(BASEDIR)\Kernel\obj\$(OBJRELDIR)
KABIDIR=$(BASEDIR)\Kernel\obj\$(OBJMACHINERELDIR)
DISTDIR=$(BASEDIR)\Distro\obj\$(OBJKRNDIR).$(OBJRELDIR)
DRIVDIR=$(BASEDIR)\Drivers\obj\$(OBJRELDIR)
CONSDIR=$(BASEDIR)\Contracts\obj\$(OBJRELDIR)
ILLSDIR=$(BASEDIR)\Interfaces\obj\$(OBJRELDIR)
LIBSDIR=$(BASEDIR)\Libraries\obj\$(OBJRELDIR)
APPSDIR=$(BASEDIR)\Applications\obj\$(OBJRELDIR)
APPSBINDIR=$(BASEDIR)\Applications\obj\$(OBJRELRUNTIMEDIR)
SERVDIR=$(BASEDIR)\Services\obj\$(OBJRELDIR)
WINSDIR=$(BASEDIR)\Windows\obj\$(OBJRELDIR)
BUILDIR=$(BASEDIR)\Build
OPTSDIR=$(BASEDIR)\Options

################################################################# binaries
#

ILASM=$(BUILDIR)\ilasm.exe
ILDASM=$(BUILDIR)\ildasm.exe
COPY=copy 1>nul /y

#
################################################################# End of File.
