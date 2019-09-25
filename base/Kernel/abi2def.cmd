@echo off
setlocal ENABLEEXTENSIONS ENABLEDELAYEDEXPANSION
if .==.%1 goto usage
if .%1==./? goto usage

REM
REM Process arguments.
REM

set _OBJS=
set _DEFS=singularity.V999.def
set _SRCH="@Struct_Microsoft_Singularity_V[0-9]*_"
set _DUMPBIN=dumpbin
:parse
if .==.%1 goto good

if /I ./?==./1 (
  shift /1
  goto usage
)
if /I .%1==.-? (
  shift /1
  goto usage
)
if /I .%1==./help (
  shift /1
  goto usage
)
if /I .%1==./version (
  set _SRCH="@Struct_Microsoft_Singularity_V%2_"
  shift /1
  shift /1
  goto parse
)
if /I .%1==./def (
  set _DEFS=%2
  shift /1
  shift /1
  goto parse
)
if /I .%1==./dumpbin (
  set _DUMPBIN=%2
  shift /1
  shift /1
  goto parse
)

set _OBJS=%_OBJS% %1
shift /1
goto parse

:good
rem echo _OBJS=%_OBJS%
rem echo _DEFS=%_DEFS%
rem echo _SRCH=%_SRCH%
rem goto exit
echo EXPORTS > %_DEFS%

set PATH=%PATH%;

set FindStr=%SYSTEMROOT%\system32\findstr
set Sort=%SYSTEMROOT%\system32\sort
set DUMPBIN=%_DUMPBIN%

%DUMPBIN% /symbols %_OBJS% > %SINGULARITY_ROOT%\dumpbin.txt
%DUMPBIN% /symbols %_OBJS% | %FindStr% "External" | %FindStr% -v "\$" | %FindStr% "\?g_[A-z]" | %FindStr% %_SRCH% | substitute.exe ".*(?<x>\?g_[^ ]*).*" "    ${x}" | sort>> %_DEFS%
goto exit

:usage
echo.Usage:
echo.    ABI2DEF.CMD [/VERSION number] [/DEF output] {objs}
echo.
echo.Summary:
echo.    Creates the .DEF for the specified version of the Singularity ABI by
echo.    parsing the symbols exported from the named .obj and .lib files.
echo.    If version isn't specified, create a file for all versions.
echo.
echo.Options:
echo.    /VERSION number        ABI version number.
echo.    /DEF output            Output .def file.
echo.

:exit
