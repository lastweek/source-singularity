@echo off

call %SINGULARITY_ROOT%\buildcfg.cmd

echo Logging results to %SINGULARITY_ROOT%\bvt.log

start "Singularity BVT Logger" kd.exe -logo %SINGULARITY_ROOT%\bvt.log -k com:pipe,port=\\.\pipe\kd,resets=0,reconnect
call boottest.cmd /wait %1 /dhcp /c:bvt
if not %ErrorLevel% EQU 0 (
    taskkill /IM kd.exe 2>&1 1>nul
    exit /b 1
)

taskkill /IM kd.exe 2>&1 1>nul
findstr /c:"Power-off via APM." %SINGULARITY_ROOT%\bvt.log
@if not ErrorLevel 1 (
@echo ERRORLEVEL=%ERRORLEVEL%
@echo.
@echo.
@echo BVT Succeeded.
@echo.
exit /b 0
) ELSE (
@echo ERRORLEVEL=%ERRORLEVEL%
@echo.
@echo.
@echo BVT Failed.
@echo.
exit /b 1
)

:usage
echo.Usage: %0 ^<VmcFile^>
echo.
echo.Run BVT using specified Virtual PC image file.
exit /b 1
