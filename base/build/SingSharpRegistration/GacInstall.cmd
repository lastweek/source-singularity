@echo off
set FROM=%1
set TO=%2
set PDB=%FROM:~0,-4%.pdb
set ASSEMBLY=%TO:~0,-4%
if exist %2 gacutil /silent /nologo /u "%ASSEMBLY%" /r FILEPATH %2 "%ASSEMBLY%"
copy /y %1 > nul
if exist %PDB% copy /y %PDB% > nul
gacutil /nologo /i %2
if ERRORLEVEL 1 echo ERROR installing %ASSEMBLY% into the Global Assembly Cache
