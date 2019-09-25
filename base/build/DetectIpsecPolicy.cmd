@echo off
setlocal
set _DEVDRIVE=%~d0%
set __DEVROOT=%~p0%XXXX_XXXX_XXXX
set _DEVROOT=%__DEVROOT:\XXXX_XXXX_XXXX=%
set __DEVROOT=
set _DEVPATH=%_DEVDRIVE%%_DEVROOT%
echo.
echo Note:
echo.  To act as a network boot server, your IPSec policy should be set
echo.  to "SecNet Request Security", not "SecNet Require Security".
echo.
echo Your current policy is:
cscript //nologo %_DEVPATH%\DetectIpsecPolicyScript.vbs
