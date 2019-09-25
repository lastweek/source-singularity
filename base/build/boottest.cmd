@echo off

setlocal enableextensions enabledelayedexpansion

set StartVpcFlags=
set DefaultBootType=CD

:parse
if /I .%1==./wait (
    set StartVpcFlags=/wait !StartVpcFlags!
    shift
    goto :parse
)

if /I .%1==./cd (
    set BootType=cd
    shift
    goto :parse
)

if /I .%1==./net (
    set BootType=net
    shift
    goto :parse
)

if not defined BootType (
    set BootType=%DefaultBootType%
)

@rem --------------------------------------------------------------------------
@rem Stage 1 : Check VPC configuration file exists

if "%1"=="" (
    call :Usage "%0"
    exit /b 1
)

if "%~x1" == ".vmc" (
    set VpcConfig=%~1
) else (
    set VpcConfig=%~1.vmc
)
shift

if not exist "%VpcConfig%" (
    echo.Specified Virtual PC image not found:
    echo.  %VpcConfig%
    exit /b 1
)

if not exist "%SINGULARITY_BUILD_SETTINGS%" (
    echo Build configuration settings file not found.  Has a distribution been built?
    exit /b 1
)

echo %BootType%

call "%SINGULARITY_BUILD_SETTINGS%" >nul

if /i "%BootType%" == "net" (
    call :NetworkBoot "%VpcConfig%" %1 %2 %3 %4 %5 %6 %7 %8 %9
    exit /b %ErrorLevel%
) else if /i "%BootType%" == "cd" (
    call :CdBoot "%VpcConfig%"
    exit /b %ErrorLevel%
) else (
    echo No boot type selected.
    exit /b 1
)

rem ---------------------------------------------------------------------------
rem NetworkBoot <vpc image file> [<bootd args...>]
:NetworkBoot

set MacAddress=00-00-00-00-00-00
set MacCount=0
for /F "usebackq skip=1 tokens=4 delims=<> " %%m in (`find "ethernet_card_address" "%VpcConfig%"`) do (
    if !MacCount! EQU 0 (
        set s=%%m
        set MacAddress=!s:~0,2!-!s:~2,2!-!s:~4,2!-!s:~6,2!-!s:~8,2!-!s:~10,2!
    )
    set /a MacCount=!MacCount!+1
)

if !MacCount! EQU 0 (
    echo.Found !MacCount! Mac addresses in %VpcConfig%, but expected 1.
    exit /b 1
) else if !MacCount! GEQ 2 (
    echo.*** Warning found multiple MAC addresses in %VpcConfig%.
    echo.*** Passing !MacAddress! onto to bootd.
)

call :SubstituteIsoInConfigFile "%VpcConfig%" "%SINGULARITY_ROOT%\build\empty.iso"
if ErrorLevel 1 (
    exit /b 1
)

start bootd.exe /dhcp /b:SINGLDR /m:!MacAddress!,10.99.99.2 /tftp /e %_BOOTD_TFTP_DIR% %*
call :StartVpc "!VpcConfig!" !StartVpcFlags!

exit /b %ErrorLevel%

rem ---------------------------------------------------------------------------
rem StartVpc <vpc image file> <startArgs>
:StartVpc

rem VPC has daft command line options. If started once with -startvm
rem it registers the VM and then launches it.  If the hapless user tries
rem to invoke the same command, VPC complains that the VM is already
rem registered.
rem
rem So this scripts checks the location were VPC stores links to
rem known VMC files to see if the VM already exists.  This is annoyingly
rem stupid and fragile, ie if a user creates to .vmc files with the same
rem name.  Details, details, details.

set VpcExe=%ProgramFiles%\Microsoft Virtual PC\Virtual PC.exe
if not exist "%VpcExe%" (
    set _VPCPath=%ProgramFiles(x86)%
    set VpcExe=%ProgramFiles(x86)%\Microsoft Virtual PC\Virtual PC.exe
    echo %VpcExe%
)
if not exist "%VpcExe%" (
    echo Couldn't find Virtual PC.exe
)

if exist "%AppData%\Microsoft\Virtual PC\Virtual Machines\%~n1.lnk" (
    rem User has registered VM already.
    start "" %2 %3 %4 %5 "%VpcExe%" -quiet -singlepc -pc "%~n1" -launch
) else (
    rem A new VM to be started and registered.
    start "" %2 %3 %4 %5 "%VpcExe%" -quiet -singlepc -startvm "%~f1"
)

exit /b 0

rem ---------------------------------------------------------------------------
rem CdBoot <vpc image file>
:CdBoot

call :SubstituteIsoInConfigFile "%~1" "%_BOOT_ISO%"
if ErrorLevel 1 (
    exit /b 1
)

call :StartVpc "%~1"
exit /b %ErrorLevel%

rem ---------------------------------------------------------------------------
rem :SubstituteIsoInConfigFile <ConfigFile> <IsoImage>
:SubstituteIsoInConfigFile

set TmpImage=%TEMP%\%~n1
substitute ">[^>]*[.iso]</" ">%~2</" "%~1" "%TmpImage%"
if ErrorLevel 1 (
    echo Failed to set CD image in vpc configuration file: "%~1"
    exit /b 1
)

copy /y "%TmpImage%" "%~1" >nul
if ErrorLevel 1 (
    echo Failed to copy back updated VMC image.
    exit /b 1
)

exit /b 0

rem ---------------------------------------------------------------------------
rem :Usage <script name>
:Usage
   echo.The purpose of this script is to launch Virtual PC and boot it in
   echo.the specified manner (network boot or CD).
   echo.
   echo. Usage:
   echo.   %~nx0 ^<bootType^> ^<VPC Image^> [ options ]
   echo.
   echo.where ^<boottype^> is either /CD or /Net (case-insensitive)
   echo.and options exist only for network boot.
