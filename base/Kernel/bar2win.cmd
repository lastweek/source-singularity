@echo off
setlocal ENABLEEXTENSIONS ENABLEDELAYEDEXPANSION
if .==.%1 goto usage
if .%1==./? goto usage

set _IN=
set _OUT=
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

if .==.%_IN% (
    set _IN=%1
    shift /1
    goto parse
)

if .==.%_OUT% (
    set _OUT=%1
    shift /1
    goto parse
)

goto usage

goto parse

:good
rem echo _IN=%_IN%
rem echo _OUT=%_OUT%
rem goto exit

echo #pragma pack(push, 1) > %_OUT%
type %_IN% | substitute.exe "static .*\);" "" | substitute.exe "(?<x>[a-zA-Z_][a-zA-Z0-9_]*) \*\*" "PTR_TYPE /* ${x}** */" | substitute.exe "(?<x>[a-zA-Z_][a-zA-Z0-9_]*) \*" "PTR_TYPE /* ${x}* */" | substitute.exe \bbool\b UCHAR | substitute.exe \bbyte\b UCHAR | substitute \buintptr\b UPTR_TYPE | substitute \bintptr\b SPTR_TYPE | substitute \bintPtr\b SPTR_TYPE | substitute "\buint(?<x>[0-9]*)\b" "UINT${x}" | substitute "\bint(?<x>[0-9]*)\b" "INT${x}" | substitute bartok_char WCHAR | substitute \bUIntPtr\b UPTR_TYPE >> %_OUT%
echo #pragma pack(pop) >> %_OUT%

goto exit

:usage
echo.Usage:
echo.    BAR2WIN.CMD input output
echo.
echo.Summary:
echo.    Converts a header file from bartok-generated format
echo.       to Windows friendly, cross-compilable format
echo.
echo.Arguments:
echo.    input                  Input header file
echo.    output                 Output header file
echo.

:exit
