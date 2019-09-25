@echo off

@rem This script run the user specified command with a path
@rem normalized to 8.3 representation and with all invalid path
@rem components removed.  This reduces the chance of the 16-bit
@rem tools reporting an out of memory error. If the path is too long
@rem the apps will still fail.
@rem
@rem The existence of this script is depressing, but no one
@rem maintains 16-bit build tools and you need them to build an OS.

setlocal


set newPath=

set components="%Path:;=" "%"
for %%c in (%components%) do (
    if not %c=="" (
        call :GrowNewPath %%c
    )
)
set Path=%newPath:~1%

call %*
goto :EOF

:GrowNewPath
if not exist %1 (
    @rem echo %1 =^> BAD 
    exit /b 0
)
@rem echo %1 =^> %~fs1
set newPath=%newPath%;%~s1%
