@echo off
set FROM=%1
set TO=%2
set PDB=%FROM:~0,-4%.pdb
set ASSEMBLY=%TO:~0,-4%
if exist %2 regasm32 /nologo /silent /u %2  
copy /y %1 > nul
if exist %PDB% copy /y %PDB% > nul
regasm32 /nologo /codebase %2
