@rem A very simple conditional copy script that only does the copy if
@rem the contents of source file is different from the destination file OR
@rem the destination does not exist.
@echo off

setlocal

if "%~1" == "" (
    goto :Usage
)
if "%~2" == "" (
    goto :Usage
)

if not exist "%~2" (
    goto :do_copy "%~1" "%~2"
)

"%SINGULARITY_ROOT%\Build\Cmp.exe" "%~1" "%~2" > nul
if ErrorLevel 1 (
    goto :do_copy "%~1" "%~2"
)

@rem echo No copy made.
exit /b 0

:Usage
   echo "CheckedMove.cmd <source> <destination>"
   exit /b 1

:do_copy
    copy /Y /B "%~1" "%~2" >nul
    exit /b %ErrorLevel%
