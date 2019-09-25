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

type %_IN% | substitute.exe -e "EXTERN \|(?<x>.*)\|" "IF :def:|defining ${x}|\n    EXPORT |${x}|\n    ELSE\n    EXTERN |${x}|\n    ENDIF\n" > %_OUT%

goto exit

:usage
echo.Usage:
echo.    bararmfix.CMD input output
echo.
echo.Summary:
echo.    Converts an inc file from bartok-generated format
echo.       to armasm friendly format
echo.
echo.Arguments:
echo.    input                  Input header file
echo.    output                 Output header file
echo.

:exit
