@echo off

@rem
@rem This script generates a timestamp suitable for inclusion in a Makefile or
@rem a batch file
@rem
@rem ie for a Makefile:
@rem    timestamp.cmd TIMESTAMP > timestamp.inc
@rem and for a batch script:
@rem    timestamp.cmd set TIMESTAMP > timestamp.inc
@rem

setlocal

if "%*" == "" (
    set OUTFORM=TIMESTAMP
) else (
    set OUTFORM=%*
)

FOR /F "TOKENS=1* DELIMS= " %%A IN ('DATE/T') DO SET DATE=%%B
FOR /F "TOKENS=*" %%A IN ('TIME/T') DO SET TIME=%%A
echo %OUTFORM%=%TIME% on %DATE%
