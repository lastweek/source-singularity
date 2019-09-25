@echo off
set FROM=%1
set TO=%2
set PDB=%FROM:~0,-4%.pdb
set ASSEMBLY=%TO:~0,-4%
copy /y %1 > nul
if exist %PDB% copy /y %PDB% > nul
