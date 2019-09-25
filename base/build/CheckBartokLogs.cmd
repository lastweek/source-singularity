@echo off
setlocal
setlocal ENABLEDELAYEDEXPANSION

@rem Since we can not presently build with warnings as errors
@rem with Bartok we check for warnings in the log that will
@rem cause the developer the grief.

if .%1==. (
    echo Usage: %~n0 logFile1 [logFile2 ...]
    exit /b 1
)

@rem --------------------------------------------------------------------------
@rem First test - unresolved symbols

set failures=0
set errorFile=%TEMP%\CheckBartokLogs.log
del /q %errorFile% 1>nul 2>nul
for /f "usebackq delims==" %%f in (`findstr /m /c:"Unable to resolve" %*`) do (
    echo %%f >> %errorFile%
    set /a failures = !failures! + 1
)

if !failures! NEQ 0 (
    echo The following Bartok logs have unresolved references:
    for /F %%f in (%errorFile%) do (
        echo.    %%f
        for /F "usebackq tokens=7" %%s in (`findstr /c:"Unable to resolve" %%f`) do (
            set t=%%s
            echo.        !t:~0,-1!
        )
    )
    echo.
    echo.*** There are %failures% files with unresolved references. ***
    echo.
    exit /b 1
) else (
    echo.No unresolved references.
)

@rem --------------------------------------------------------------------------
@rem Other tests here...

@rem --------------------------------------------------------------------------
@rem Clean exit
exit /b 0
