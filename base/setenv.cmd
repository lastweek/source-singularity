@echo off

if /I "%ScriptDebug%" EQU "Yes" (
   @echo on
)

@rem @setlocal enableextensions

rem This needs to be defined before invoking goto usage.
set _EXIT_CMD=exit /b

if .==.%1 goto good
if ".%1"=="./?" goto usage

:good
rem Save path when first run. Need to use goto in case the path contains parens.
if defined SINGULARITY_SAVED_PATH goto SINGULARITY_SAVED_PATH_set
set SINGULARITY_SAVED_PATH=%PATH%
:SINGULARITY_SAVED_PATH_set

rem Set source directory
set SINGULARITY_ROOT=%~dp0
if .%SINGULARITY_ROOT:~-1%==.\ (
   set SINGULARITY_ROOT=%SINGULARITY_ROOT:~0,-1%
)

rem Set default object output directory.
set SINGULARITY_OBJROOT=%SINGULARITY_ROOT%.obj

rem Clear no defaults variable.  Needs to be reset after missing default
rem causes an error.
set NO_SINGULARITY_DEFAULTS=

rem Clear the codegen variable.  It will be reset by the default codegen
rem variable that should still be in the environment or will be set by a
rem platform option.
set CODE_GENERATOR=
set CODE_GENERATOR_BUILD=
set CODE_GENERATOR_RUNTIME=

:parse

if /I .%1==./release (
  set Configuration=Release
  shift /1
  goto parse
)

if /I .%1==./debug (
  set Configuration=Debug
  shift /1
  goto parse
)

if /I .%1==./terminate (
  set _EXIT_CMD=exit
  shift /1
  goto parse
)

if /I .%1==./prototype (
  set Configuration=Prototype
  shift /1
  goto parse
)

if /I .%1==./apicup (
  set PLATFORM=ApicPC
  set PROCESSOR=x86
  shift /1
  goto parse
)

if /I .%1==./apic (
  set PLATFORM=ApicMP
  set PROCESSOR=x86
  shift /1
  goto parse
)

if /I .%1==./mp (
  set PLATFORM=ApicMP
  set PROCESSOR=x86
  shift /1
  goto parse
)

if /I .%1==./apic64 (
  set PLATFORM=Apic64
  set PROCESSOR=x64
  shift /1
  goto parse
)

rem Temporarily disabled until ARM support is ready
rem if /I .%1==./omap3430 (
rem   set PLATFORM=Omap3430
rem   set PROCESSOR=arm
rem   set COLLECTOR_KERNEL=MarkSweep
rem   set COLLECTOR_APP=MarkSweep
rem   set CODE_GENERATOR=PHXBRIDGE
rem   shift /1
rem   goto parse
rem )

rem Temporarily disabled until ARM support is ready
rem if /I .%1==./smdk2410 (
rem   set PLATFORM=Smdk2410
rem   set PROCESSOR=arm
rem   set COLLECTOR_KERNEL=MarkSweep
rem   set COLLECTOR_APP=MarkSweep
rem   set CODE_GENERATOR=PHXBRIDGE
rem   shift /1
rem   goto parse
rem )

if /I .%1==./kms (
  set COLLECTOR_KERNEL=MarkSweep
  shift /1
  goto parse
)

if /I .%1==./kcc (
  set COLLECTOR_KERNEL=Concurrent
  shift /1
  goto parse
)

if /I .%1==./kss (
  set COLLECTOR_KERNEL=Semispace
  shift /1
  goto parse
)

if /I .%1==./knl (
  set COLLECTOR_KERNEL=Null
  shift /1
  goto parse
)

if /I .%1==./pms (
  set COLLECTOR_APP=MarkSweep
  shift /1
  goto parse
)

rem Currently broken - see internal bug 60
rem if /I .%1==./pcc (
rem   set COLLECTOR_APP=Concurrent
rem   shift /1
rem   goto parse
rem )

rem Currently broken - see internal bug 63
rem if /I .%1==./pss (
rem   set COLLECTOR_APP=Semispace
rem   shift /1
rem   goto parse
rem )

if /I .%1==./pnl (
  set COLLECTOR_APP=Null
  shift /1
  goto parse
)

rem Currently broken - see internal bug 75
rem if /I .%1==./paging (
rem   set PAGING=On
rem   shift /1
rem   goto parse
rem )

if /I .%1==./nopaging (
  set PAGING=Off
  shift /1
  goto parse
)

if /I .%1==./affinity (
  set SCHEDULER=Affinity
  shift /1
  goto parse
)

if /I .%1==./noaffinity (
  set SCHEDULER=Min
  shift /1
  goto parse
)

if /I .%1==./objdir (
  set SINGULARITY_OBJROOT=%~f2
  shift /1
  shift /1
  goto parse
)

if /I .%1==./fullpaths (
  set ShowFullPaths=true
  shift /1
  goto parse
)

if /I .%1==./nofullpaths (
  set ShowFullPaths=false
  shift /1
  goto parse
)

if /I .%1==./failearly (
  set StopOnFirstFailure=true
  shift /1
  goto parse
)

if /I .%1==./nofailearly (
  set StopOnFirstFailure=false
  shift /1
  goto parse
)

if /I .%1==./skipapps (
  set DistroSkipApps=true
  shift /1
  goto parse
)

if /I .%1==./noskipapps (
  set DistroSkipApps=false
  shift /1
  goto parse
)

if /I .%1==./skipkernel (
  set DistroSkipKernel=true
  shift /1
  goto parse
)

if /I .%1==./noskipkernel (
  set DistroSkipKernel=false
  shift /1
  goto parse
)

rem Currently broken - see internal bug 61
rem if /I .%1==./parallel (
rem  set BuildInParallel=true
rem  shift /1
rem  goto parse
rem )

if /I .%1==./noparallel (
  set BuildInParallel=false
  shift /1
  goto parse
)

if /I .%1==./bartok (
  set CODE_GENERATOR=BARTOK
  shift /1
  goto parse
)

rem Currently broken - see internal bug 65
rem if /I .%1==./phxbridge (
rem   set CODE_GENERATOR=PHXBRIDGE
rem   shift /1
rem   goto parse
rem )

if /I .%1==./codegenDBG (
  set CODE_GENERATOR_BUILD=DEBUG
  shift /1
  goto parse
)

if /I .%1==./codegenTST (
  set CODE_GENERATOR_BUILD=TEST
  shift /1
  goto parse
)

if /I .%1==./codegenREL (
  set CODE_GENERATOR_BUILD=RELEASE
  shift /1
  goto parse
)

if /I .%1==./codegenCLR (
  set CODE_GENERATOR_RUNTIME=CLR
  shift /1
  goto parse
)

if /I .%1==./codegenSH1 (
  set CODE_GENERATOR_RUNTIME=SELFHOST1
  shift /1
  goto parse
)

if /I "%1" == "/distro" (
  set SINGULARITY_DISTRO_NAME=%2
  shift /1
  shift /1
  goto parse
)

if /I "%1" == "/nodistro" (
  set SINGULARITY_DISTRO_NAME=
  shift /1
  goto parse
)

rem Currently broken - see internal bug 7
rem if /I "%1" == "/linkedstacks" (
rem   set SINGULARITY_LINKED_STACKS=true
rem   shift /1
rem   goto parse
rem )

if /I "%1" == "/nolinkedstacks" (
  set SINGULARITY_LINKED_STACKS=false
  shift /1
  goto parse
)

if /I "%1" == "/stackchecks" (
  set SINGULARITY_STACK_CHECKS=true
  shift /1
  goto parse
)

if /I "%1" == "/nostackchecks" (
  set SINGULARITY_STACK_CHECKS=false
  shift /1
  goto parse
)

rem Use goto in case %SINGULARITY_SAVED_PATH% contains parens
if /I not .%1==./clean goto noclean

  set SINGULARITY_ROOT=
  set SINGULARITY_OBJROOT=
  set SINGULARITY_INTERNAL=
  set SINGULARITY_DISTRO_SUFFIX=
  set SINGULARITY_DISTRO_NAME=
  set SINGULARITY_BUILD_SETTINGS=
  set PATH=%SINGULARITY_SAVED_PATH%
  set SINGULARITY_SAVED_PATH=
  set Configuration=
  set PLATFORM=
  set PROCESSOR=
  set BUILDTYPE=
  set COLLECTOR_KERNEL=
  set COLLECTOR_APP=
  set PAGING=
  set PAGING_FLAG=
  set GENERATE_ABI_SHIM=
  set SCHEDULER=
  set ShowFullPaths=
  set StopOnFirstFailure=
  set DistroSkipApps=
  set DistroSkipKernel=
  set BuildInParallel=
  set SINGULARITY_PATH=
  set CODE_GENERATOR=
  set CODE_GENERATOR_BUILD=
  set CODE_GENERATOR_RUNTIME=
  set SINGULARITY_LINKED_STACKS=
  set SINGULARITY_STACK_CHECKS=
  set DEFAULT_CODE_GENERATOR=
  set KERNEL_GC=
  set SINGULARITY_BUILD_ISO=
  set SINGULARITY_DISTRO_PATH=
  set TITLE=
  echo.Environment cleaned.
  title CLEAN

  rem This cleans the _EXIT_CMD variable while still being able to
  rem execute its contents.
  (
    set _EXIT_CMD=
    %_EXIT_CMD% 0
  )

:noclean

if /I .%1==./nodefaults (
  set GENERATE_ABI_SHIM=Off
  set NO_SINGULARITY_DEFAULTS=Yes
  shift /1
  goto parse
)

if /I .%1==./notitle (
  set NO_SINGULARITY_WINDOW_TITLE=Yes
  shift /1
  goto parse
)

if /I .%1==./vs (
  set _create_vs_targets=On
  shift /1
  goto parse
)

if /I .%1==./iso (
  set SINGULARITY_BUILD_ISO=true
  shift /1
  goto parse
)

if /I .%1==./noiso (
  set SINGULARITY_BUILD_ISO=false
  shift /1
  goto parse
)

setlocal
set ARG=.%1
if %ARG:~0,2%==./ (
  echo.Unrecognized option "%1"
  %_EXIT_CMD% 2
)
endlocal

:finished

set TITLE=

if "%SINGULARITY_DISTRO_NAME%" == "" (
  set SINGULARITY_DISTRO_NAME=BVT
)
set SINGULARITY_DISTRO_PATH=%SINGULARITY_ROOT%\Distro\%SINGULARITY_DISTRO_NAME%.proj
if not exist "%SINGULARITY_DISTRO_PATH%" (
  echo.
  echo *** WARNING: You have selected '%SINGULARITY_DISTRO_NAME%' as the current distro project,
  echo *** but there is no such file '%SINGULARITY_DISTRO_PATH%'.
  echo.
)

if .%Configuration%==.Release (
  rem
) else if .%Configuration%==.Debug (
  rem
) else if .%Configuration%==.Prototype (
  rem
) else (
  if .%NO_SINGULARITY_DEFAULTS%==.Yes (
    echo.Missing or invalid 'Configuration' value: "%Configuration%"
    %_EXIT_CMD% 1
  )
  set Configuration=Debug
)

if .%SINGULARITY_BUILD_ISO%==.true (
  rem
) else if .%SINGULARITY_BUILD_ISO%==.false (
  rem
) else (
  if .%NO_SINGULARITY_DEFAULTS%==.Yes (
    echo.Missing or invalid 'SINGULARITY_BUILD_ISO' value: "%SINGULARITY_BUILD_ISO%"
    %_EXIT_CMD% 1
  )
  set SINGULARITY_BUILD_ISO=true
)

if .%SINGULARITY_LINKED_STACKS%==.true (
  rem Currently broken - see internal bug 7
  rem
  rem set TITLE=%TITLE% Pcc
  echo.SINGULARITY_LINKED_STACKS value "%SINGULARITY_LINKED_STACKS%" is not currently available.
  %_EXIT_CMD% 1
) else if .%SINGULARITY_LINKED_STACKS%==.false (
  rem
) else (
  rem if .%NO_SINGULARITY_DEFAULTS%==.Yes (
  rem   echo.Missing or invalid 'SINGULARITY_LINKED_STACKS' value: "%SINGULARITY_LINKED_STACKS%"
  rem   %_EXIT_CMD% 1
  rem )
  set SINGULARITY_LINKED_STACKS=false
)

if .%SINGULARITY_STACK_CHECKS%==.true (
  rem
) else if .%SINGULARITY_STACK_CHECKS%==.false (
  rem
) else (
  if .%NO_SINGULARITY_DEFAULTS%==.Yes (
    echo.Missing or invalid 'SINGULARITY_STACK_CHECKS' value: "%SINGULARITY_STACK_CHECKS%"
    %_EXIT_CMD% 1
  )
  set SINGULARITY_STACK_CHECKS=true
)

if .%CODE_GENERATOR_BUILD%==.DEBUG (
  rem
) else if .%CODE_GENERATOR_BUILD%==.TEST (
  rem
) else if .%CODE_GENERATOR_BUILD%==.RELEASE (
  rem
) else if .%CODE_GENERATOR_BUILD%==.CLR (
  rem
) else (
  if .%NO_SINGULARITY_DEFAULTS%==.Yes (
    echo.Missing or invalid 'CODE_GENERATOR_BUILD' value: "%CODE_GENERATOR_BUILD%"
    %_EXIT_CMD% 1
  )
  set CODE_GENERATOR_BUILD=DEBUG
)

call :SetInitialTitle "%SINGULARITY_ROOT%"

set TITLE=%TITLE% %Configuration%

if .%PLATFORM%==.ApicPC (
  rem
) else if .%PLATFORM%==.ApicMP (
  rem
) else if .%PLATFORM%==.Apic64 (
  rem
) else if .%PLATFORM%==.Omap3430 (
  rem
  rem ARM support temporarily removed.
  echo.'Platform' value "%PLATFORM%" is not currently available.
  %_EXIT_CMD% 1
) else if .%PLATFORM%==.Smdk2410 (
  rem
  rem ARM support temporarily removed.
  echo.'Platform' value "%PLATFORM%" is not currently available.
  %_EXIT_CMD% 1
) else (
  if .%NO_SINGULARITY_DEFAULTS%==.Yes (
    echo.Missing or invalid 'Platform' value: "%PLATFORM%"
    %_EXIT_CMD% 1
  )
  set PLATFORM=ApicMP
  set PROCESSOR=x86
  set DEFAULT_CODE_GENERATOR=BARTOK
)
set TITLE=%TITLE% %PLATFORM%

if .%COLLECTOR_KERNEL%==.MarkSweep (
  set KERNEL_GC=Kms
) else if .%COLLECTOR_KERNEL%==.Concurrent (
  set KERNEL_GC=Kcc
) else if .%COLLECTOR_KERNEL%==.Semispace (
  set KERNEL_GC=Kss
  rem
) else if .%COLLECTOR_KERNEL%==.Null (
  set TITLE=%TITLE% Knl
  rem
) else if .%COLLECTOR_KERNEL%==.Null (
  set TITLE=%TITLE% Knl
  rem
) else (
  if .%NO_SINGULARITY_DEFAULTS%==.Yes (
    echo.Missing or invalid COLLECTOR_KERNEL value: "%COLLECTOR_KERNEL"
    %_EXIT_CMD% 1
  )
  set COLLECTOR_KERNEL=Concurrent
  set KERNEL_GC=Kcc
)
set TITLE=%TITLE% %KERNEL_GC%

if .%COLLECTOR_APP%==.MarkSweep (
  rem
) else if .%COLLECTOR_APP%==.Concurrent (
  rem Currently broken - see internal bug 60
  rem
  rem set TITLE=%TITLE% Pcc
  echo.COLLECTOR_APP value "%COLLECTOR_APP%" is not currently available.
  %_EXIT_CMD% 1
) else if .%COLLECTOR_APP%==.Semispace (
  rem Currently broken - see internal bug 63
  rem
  rem set TITLE=%TITLE% Pss
  echo.COLLECTOR_APP value "%COLLECTOR_APP%" is not currently available.
  %_EXIT_CMD% 1
) else if .%COLLECTOR_APP%==.Null (
  rem
  set TITLE=%TITLE% Pnl
) else (
  if .%NO_SINGULARITY_DEFAULTS%==.Yes (
    echo.Missing or invalid COLLECTOR_APP value: "%COLLECTOR_APP%"
    %_EXIT_CMD% 1
  )
  set COLLECTOR_APP=MarkSweep
)
if .%SCHEDULER%==.Min (
  rem
) else if .%SCHEDULER%==.Affinity (
  rem
) else (
  if .%NO_SINGULARITY_DEFAULTS%==.Yes (
    echo.Missing or invalid SCHEDULER value: "%SCHEDULER%"
    %_EXIT_CMD% 1
  )
  set SCHEDULER=Min
)
set TITLE=%TITLE% %SCHEDULER%

if .%PAGING%==.On (
rem Currently broken - see internal bug 75
rem  set PAGING_FLAG=.Paging
rem  set TITLE=%TITLE% Paging
  echo.PAGING value "%PAGING%" is not currently available.
  %_EXIT_CMD% 1
) else if .%PAGING%==.Off (
  set PAGING_FLAG=
) else (
rem Currently only one option - see internal bug 75
rem   if .%NO_SINGULARITY_DEFAULTS%==.Yes (
rem     echo.Missing or invalid PAGING value: "%PAGING%"
rem     %_EXIT_CMD% 1
rem   )
  set PAGING=Off
  set PAGING_FLAG=
)

if not defined CODE_GENERATOR_BUILD set CODE_GENERATOR_BUILD=%DEFAULT_CODE_GENERATOR_BUILD%
if not defined CODE_GENERATOR_RUNTIME set CODE_GENERATOR_RUNTIME=%DEFAULT_CODE_GENERATOR_RUNTIME%

if .%CODE_GENERATOR%==.BARTOK (
  rem
) else if .%CODE_GENERATOR%==.PHXBRIDGE (
  rem Currently broken - see internal bug 65
  rem
  echo.CODE_GENERATOR value "%CODE_GENERATOR%" is not currently available.
  %_EXIT_CMD% 1
) else (
  rem if .%NO_SINGULARITY_DEFAULTS%==.Yes (
  rem   echo.Missing or invalid 'CODE_GENERATOR' value: "%CODE_GENERATOR"
  rem   %_EXIT_CMD% 1
  rem )
  set CODE_GENERATOR=BARTOK
)

if .%CODE_GENERATOR_BUILD%==.DEBUG (
  rem
) else if .%CODE_GENERATOR_BUILD%==.TEST (
  rem
) else if .%CODE_GENERATOR_BUILD%==.RELEASE (
  rem
) else (
rem  if .%NO_SINGULARITY_DEFAULTS%==.Yes (
rem    echo.Missing or invalid CODE_GENERATOR_BUILD value: "%CODE_GENERATOR_BUILD"
rem    %_EXIT_CMD% 1
rem   )
  if .%CODE_GENERATOR%==.BARTOK (
      set CODE_GENERATOR_BUILD=DEBUG
   ) else if .%CODE_GENERATOR%==.PHXBRIDGE (
      set CODE_GENERATOR_BUILD=RELEASE
   )
)

if .%CODE_GENERATOR_RUNTIME%==.CLR (
  rem
) else if .%CODE_GENERATOR_RUNTIME%==.SELFHOST1 (
  rem
) else (
rem   if .%NO_SINGULARITY_DEFAULTS%==.Yes (
rem     echo.Missing or invalid CODE_GENERATOR_RUNTIME value: "%CODE_GENERATOR_RUNTIME%"
rem     %_EXIT_CMD% 1
rem  )
  if .%CODE_GENERATOR%==.BARTOK (
     set CODE_GENERATOR_RUNTIME=CLR
  ) else if .%CODE_GENERATOR%==.PHXBRIDGE (
     if .%CODE_GENERATOR_BUILD%==.RELEASE (
        set CODE_GENERATOR_RUNTIME=SELFHOST1
     ) else if .%CODE_GENERATOR_BUILD%==.TEST (
        set CODE_GENERATOR_RUNTIME=CLR
     ) else if .%CODE_GENERATOR_BUILD%==.DEBUG (
        set CODE_GENERATOR_RUNTIME=CLR
     )
  )
)

if not exist "%SINGULARITY_ROOT%\build\x86_%PROCESSOR%\%CODE_GENERATOR%\%CODE_GENERATOR_BUILD%\%CODE_GENERATOR_RUNTIME%\bartok.exe" (
  echo.Requested compiler does not exist:
  echo "%SINGULARITY_ROOT%\build\x86_%PROCESSOR%\%CODE_GENERATOR%\%CODE_GENERATOR_BUILD%\%CODE_GENERATOR_RUNTIME%\bartok.exe"
  %_EXIT_CMD% 1
)



rem Tread with fear -- the CMD "rules" for escaping characters would
rem make Cthulhu cry.  Notably, how escape characters are interpreted
rem varies, depending on whether or not you are within a ( ) context.
rem Note: We set several variables in Ide.targets, but notably we omit
rem Configuration and Platform.  This is because the VS IDE allows
rem you to select these values.  For the others (GC), there is no way
rem to do this in the IDE.
if "%_create_vs_targets%" == "On" (

  rem Temporarily disable delayed expansion so that the exclamation
  rem points (!'s) are not interpretted as variables
  setlocal DISABLEDELAYEDEXPANSION

  echo Creating %SINGULARITY_ROOT%\Targets\Ide.targets
  (
    echo ^<Project xmlns="http://schemas.microsoft.com/developer/msbuild/2003"^>
    echo ^<!-- Do not directly edit this file.  Use "setenv /vs" to create this file. --^>
    echo ^<!-- DO NOT CHECK IN THIS FILE! --^>
    echo   ^<PropertyGroup^>
    echo     ^<SINGULARITY_ROOT^>%SINGULARITY_ROOT%^</SINGULARITY_ROOT^>
    echo     ^<SINGULARITY_OBJROOT^>%SINGULARITY_OBJROOT%^</SINGULARITY_OBJROOT^>
    echo     ^<COLLECTOR_APP^>%COLLECTOR_APP%^</COLLECTOR_APP^>
    echo     ^<COLLECTOR_KERNEL^>%COLLECTOR_KERNEL%^</COLLECTOR_KERNEL^>
    echo   ^</PropertyGroup^>
    echo ^</Project^>
  ) > "%SINGULARITY_ROOT%\Targets\Ide.targets"

  endlocal
)

if not defined BuildInParallel set BuildInParallel=false

goto :finale

:usage
echo.Usage:
echo.    setenv.cmd [options]
echo.
echo.Summary:
echo.    Configure environment variables for building Singularity.
echo.
echo.Options:
echo.    /objdir=^<dir^>  Specify object directory.
echo.    /distro=^<name^> Specify the distribution to build.  This must be the basename
echo.                   (no extension, no path) of a distro project stored in the Distros
echo.                   directory.  The default is 'BVT'.
echo.
echo.    /prototype     Prototype build (no optimization w/ debug asserts).
echo.    /debug         Debug build (full optimization w/ debug asserts). [default]
echo.    /release       Release build (full optimization w/o debug asserts).
echo.
echo.    /apic          Multi-core 32-bit nForce4 PC.                     [default]
echo.    /apicup        Single-core 32-bit nForce4 PC.
echo.    /apic64        nForce4 64-bit APIC PC.
echo.    /mp            Equivalent to /apic.
rem Temporarily disabled until ARM support is ready
rem echo.    /omap3430      TI OMAP 3430 (Arm)
rem echo.    /smdk2410      Samsung SMDK 2410 (Arm)
echo.
echo.    /kcc           Kernel Concurrent Collector.                       [default]
echo.    /kms           Kernel Mark Sweep Collector.
echo.    /kss           Kernel Semispace Collector.
echo.    /knl           Kernel Null Collector.
echo.
echo.    /pms           Process Mark Sweep Collector.                      [default]
rem Currently broken - see internal bug 60
rem echo.    /pcc           Process Concurrent Collector.
rem Currently broken - see internal bug 63
rem echo.    /pss           Process Semispace Collector.
echo.    /pnl           Process Null Collector.
echo.
echo.    /noaffinity    Use Min Scheduler.                                 [default]
echo.    /affinity      Use Affinity Scheduler.
echo.
rem Currently broken - see internal bug 75
rem echo.    /nopaging      Page translation off.                              [default]
rem echo.    /paging        Page translation on.
rem echo.
rem Currently broken - see internal bug 61
rem echo.    /parallel      Enable MSBuild parallel execution.
rem echo.    /noparallel    Disable MSBuild parallel execution.                [default]
rem echo.
rem Currently broken - see internal bug 7
rem echo.    /[no]linkedstacks Use linked stacks.  (Disabled by default.)
echo.    /[no]stackchecks Enable stack overflow checks.  (Enabled by default.)
echo.

echo.    /clean         Remove Singularity build variables from environment.
echo.
echo.    /nodefaults    Do not use defaults, underspecification is an error.
echo.    /notitle       Do not change the window title.
echo.    /[no]fullpaths Show full paths of source files in compiler errors and warnings.
echo.    /[no]failearly Stop build on first failure; default is to keep building others.
echo.    /[no]skipapps  Prevents distro builder from compiling apps; use with caution.
echo.    /[no]skipkernel Prevents distro builder from compiling kernel; use with caution.
echo.
rem Modified until ARM support is added.
rem echo.    /bartok        Use the BARTOK code generator.                     [default:x86,x64]
rem echo.    /phxbridge     Use the PHXBRIDGE code generator.                  [default:arm]
rem echo.    /bartok        Use the BARTOK code generator.                     [default]
rem echo.    /phxbridge     Use the PHXBRIDGE code generator.
echo.
rem Modified until ARM support is added.
rem echo.    /codegenDBG    Use the DEBUG build of the code generator.         [default:x86,x64]
rem echo.    /codegenTST    Use the TEST build of the code generator.          [default:arm]
echo.    /codegenDBG    Use the DEBUG build of the code generator.         [default]
echo.    /codegenTST    Use the TEST build of the code generator.
echo.    /codegenREL    Use the RELEASE build of the code generator.
echo.
echo.    /codegenCLR    Use the code generator that is built on the CLR.   [default]
echo.    /codegenSH1    Use the code generator this is build on the Bartok
echo.                   runtime.
echo.
echo.    /iso           Distro projects generate a bootable CD-ROM ISO.    [default]
echo.    /noiso         Distro projects do not generate an ISO file.
echo.
echo.    /vs            Write settings to ^%SINGULARITY_ROOT^%\Targets\Ide.targets.
echo.                   This file can be used to build Singularity projects from
echo.                   within Visual Studio 2005.
echo.

%_EXIT_CMD% 1

@rem SetInitialTitle <SingularityRoot>
:SetInitialTitle
   set TITLE=%~n1
   %_EXIT_CMD% 0

:finale

set SINGULARITY_PATH=%SINGULARITY_ROOT%;%SINGULARITY_ROOT%\build;%SINGULARITY_ROOT%\build\x86_%PROCESSOR%

if exist "%SINGULARITY_ROOT%\internal\build" (
    set SINGULARITY_PATH=%SINGULARITY_PATH%;%SINGULARITY_ROOT%\internal\build
)

set PATH=%SINGULARITY_PATH%;%SINGULARITY_SAVED_PATH%;c:\debuggers

set SINGULARITY_DISTRO_SUFFIX=%Configuration%.%CODE_GENERATOR%.%PLATFORM%.%COLLECTOR_APP%.%SCHEDULER%.%COLLECTOR_KERNEL%.%PAGING_FLAG%

set SINGULARITY_BUILD_SETTINGS=%SINGULARITY_OBJROOT%\Settings\%SINGULARITY_DISTRO_SUFFIX%.cmd

set INCLUDE=
set LIB=

if not defined NO_SINGULARITY_WINDOW_TITLE (
  title %TITLE%
)

set NO_SINGULARITY_WINDOW_TITLE=
set NO_SINGULARITY_DEFAULTS=
set _create_vs_targets=

rem BUILDTYPE becomes Configuration in the MSBuild projects.
rem For now, we continue to set BUILDTYPE so that the makefiles still work.
set BUILDTYPE=%Configuration%

echo ** Singularity Build Environment:
echo **   Distribution:       %SINGULARITY_DISTRO_NAME%
echo **   Source Directory:   %SINGULARITY_ROOT%
echo **   Object Directory:   %SINGULARITY_OBJROOT%
echo **   Build Type:         %Configuration%
echo **   Target Platform:    %PLATFORM%
echo **   Target Processor:   %PROCESSOR%
echo **   Code Generator:     %CODE_GENERATOR%
echo **   CodeGen Build:      %CODE_GENERATOR_BUILD%
echo **   CodeGen Runtime:    %CODE_GENERATOR_RUNTIME%
echo **   Kernel Collector:   %COLLECTOR_KERNEL%
echo **   Process Collector:  %COLLECTOR_APP%
echo **   Scheduler:          %SCHEDULER%
rem Currently broken - see internal bug 75
rem echo **   Page Translation:   %PAGING%
echo **   Generate ABI Shim:  %GENERATE_ABI_SHIM%
rem Currently broken - see internal bug 7
rem echo **   Linked Stacks:      %SINGULARITY_LINKED_STACKS%
echo **   Stack Checks:       %SINGULARITY_STACK_CHECKS%
if "%SINGULARITY_BUILD_ISO%" == "true" (
echo **   Generate CD-ROM:    On
) else (
echo **   Generate CD-ROM:    Off
)
if "%StopOnFirstFailure%"    == "true" echo **   Build option:       Stop at the first project failure.     (/failearly)
if "%ShowFullPaths%"         == "true" echo **   Build option:       Show full source file path.            (/fullpaths)
if "%DistroSkipKernel%"      == "true" echo **   Build option:       Kernel will NOT be built.              (/skipkernel)
if "%DistroSkipApps%"        == "true" echo **   Build option:       Apps will NOT be built.                (/skipapps)
if /I "%BuildInParallel%"    == "true" echo **   Build option:       Parallel builds are enabled.           (/parallel)

cd /d %SINGULARITY_ROOT%

@rem
@rem *IMPORTANT* This script is used by the
@rem automated build system and users within command-line sessions.
@rem The final invocation of user supplied command happens at the end
@rem of this script because C#\'s Process class code only gets the exit
@rem code this way or via exit, exit /b does not work.  Exit without
@rem arguments terminates the interpreter.  Exit /b terminates the current
@rem batch script.  The former is not acceptable for general purpose
@rem and the latter stops the automated build system from detecting
@rem errors.
@rem
@rem Using 'shift' on command line arguments
@rem does not affect $* expand arguments thy self.
@rem
if not "%1" == "" call %1 %2 %3 %4 %5 %6 %7 %8 %9


