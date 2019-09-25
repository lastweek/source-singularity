@echo off
rem This script is a wrapper around invoking MSBuild.  It causes MSBuild to record
rem a log file under %SINGULARITY_OBJROOT%.obj\MSBuildLogs.

if /i "%ScriptDebug%" == "Yes" (
   @echo on
)

setlocal ENABLEDELAYEDEXPANSION

@rem Kill windbg if it exists
@rem taskkill /F /FI "IMAGENAME EQ windbg.exe" /FI "WINDOWTITLE EQ %Title%*" 2>NUL 1>&2
@rem -- We shouldn't kill possibly completely unrelated processes.

if exist "%SystemRoot%\Microsoft.Net\Framework64\v3.5\MSBuild.exe" (
    set _msbuild=%SystemRoot%\Microsoft.Net\Framework64\v3.5\MSBuild.exe
    set _ToolsVersion=/tv:3.5
    echo Using 64-bit MSBuild from .NET Framework 3.5
) else if exist "%SystemRoot%\Microsoft.Net\Framework\v3.5\MSBuild.exe" (
    set _msbuild=%SystemRoot%\Microsoft.Net\Framework\v3.5\MSBuild.exe
    set _ToolsVersion=/tv:3.5
    echo Using 32-bit MSBuild from .NET Framework 3.5
) else if exist "%SystemRoot%\Microsoft.Net\Framework\v2.0.50727\MSBuild.exe" (
    set _msbuild=%SystemRoot%\Microsoft.Net\Framework\v2.0.50727\MSBuild.exe
    set _ToolsVersion=
    echo Using 32-bit MSBuild from .NET Framework 2.0
    if /i "%BuildInParallel%" == "true" (
        echo Cannot build in parallel with this version of MSBuild.
        set BuildInParallel=
    )
) else (
    echo ERROR: Could not find MSBuild.exe in any location.
    exit /b 1
)

if /i "%BuildInParallel%" == "true" (
    set _cpu_count=/m:%NUMBER_OF_PROCESSORS%
    for %%x in (%*) do (
        set _arg=%%x
        if /i "!_arg:~0,3!" == "/m:" set _cpu_count=!_arg!
    )
    set _parallel_args= /p:BuildInParallel=true !_cpu_count!
) else (
    set _parallel_args=
)

rem -XXX- This assumes US locale date format.
rem                  01234567890123
rem %DATE% gives us "Fri 03/30/2007"
rem %TIME% gives us "15:49:15.24"
set _date=%DATE%
set _time=%TIME%

rem We want to build a log file name, based on the current date
rem and time.  We can't use %DATE% and %TIME% directly, because
rem they contain characters that we don't want in filenames, and
rem because the sort order of those strings does not match time
rem order.  So we swap things around a bit.  We intentionally
rem leave out the usual time/date separators, because we're using
rem YYYYMMDD format, not the usual US format.

set _timestamp=%_date:~10,4%%_date:~4,2%%_date:~7,2%-%_time:~0,2%%_time:~3,2%%_time:~6,2%%_time:~9,2%
set _timestamp=%_timestamp: =0%
set _logfile=!_timestamp!.log

if not "!SINGULARITY_ROOT!" == "" (
    if "!SINGULARITY_OBJROOT!" == "" set SINGULARITY_OBJROOT=!SINGULARITY_ROOT!.obj
)

if not "!SINGULARITY_OBJROOT!" == "" set _logdir=!SINGULARITY_OBJROOT!\MSBuildLogs

if not "!_logdir!" == "" (
    if not exist "!_logdir!" (
        echo creating log dir - !_logdir!
        mkdir "!_logdir!"
        if ErrorLevel 1 (
            echo Failed to create log directory.
            exit /b 1
        )
    )
)

if not "!_logdir!" == "" set _logfile=%_logdir%\%_logfile%

@rem Write msb arguments to a log file to avoid difficulty of quoting log
@rem file paths that may have spaces in on some Windows variants.
@rem Do NOT move %* to its own line.  In fact, do NOT create any 'echo' line that
@rem can potentially result in empty args, because 'echo' will helpfully print
@rem 'ECHO is [off|on].', rather than echoing an empty line.  Infuriating.

set _msbuild_cmd=!_msbuild! /nologo /v:m %_ToolsVersion% !_parallel_args! /logger:FileLogger,Microsoft.Build.Engine;LogFile=""!_logfile!"";Verbosity=detailed;PerformanceSummary %*
set _msbuild_cmd_double_quoted=!_msbuild! /nologo /v:m %_ToolsVersion% !_parallel_args! /logger:FileLogger,Microsoft.Build.Engine;LogFile=""!_logfile!"";Verbosity=detailed;PerformanceSummary %*

@rem Check if we are in a Windows JobObject and use jobcontrol to put us in
@rem one if not as this will propagate Ctrl-C and can give accounting
@rem information on the build.

jobcontrol.exe query
if %ErrorLevel% EQU 0 (
    set _the_build_cmd=jobcontrol.exe create msb-!_timestamp! /B /T "%_msbuild_cmd_double_quoted%"
) else (
    set _the_build_cmd=%_msbuild_cmd%
)

@rem Do not put any statements between the invocation
@rem of the build command and the capture of its exit code.
@rem echo :::%_the_build_cmd%
%_the_build_cmd%
set exitCode=%ErrorLevel%

(
echo.
echo SINGULARITY_ROOT:     %SINGULARITY_ROOT%
echo Current directory:    %CD%
echo MSBuild args:         %*
echo Invoking user:        %USERNAME%
echo Computer:             %COMPUTERNAME%
echo Date and time:        %_date% %_time%
if /I "%BuildInParallel%" == "true" (
echo Parallel builds:      Enabled
) else (
echo Parallel builds:      Disabled
)
echo MSBuild Result:       ERRORLEVEL = %ERRORLEVEL%
echo.
echo Configuration:        %Configuration%
echo Platform:             %Platform%
echo Paging:               %PAGING%
echo App collector:        %COLLECTOR_APP%
echo Kernel collector:     %COLLECTOR_KERNEL%
) >> "%_logfile%"

if exist "%SINGULARITY_ROOT%\Build\internal\ipy.exe" (
  echo Log file:
  "%SINGULARITY_ROOT%\Build\internal\ipy.exe" "%SINGULARITY_ROOT%\build\rp.py" "%CD%" "%_logFile%"
) else (
  echo.  %_logFile%
  echo.
)

if "%NoMSBColor%"=="1" (
    if %exitCode% EQU 0 (
        xecho /s "Build PASSED"
    ) else (
        xecho /s "Build FAILED"
    )
) else (
    if %exitCode% EQU 0 (
        xecho /s "Build PASSED" /fg 10
    ) else (
        xecho /s "Build FAILED" /fg 12
    )
)
echo.

rem Automated build scripts depend on the exit code
rem in order to detect successful or error hampered execution of MSBuild.

if %exitCode% EQU 0 (
   exit /b 0
) else (
   exit /b 1
)
