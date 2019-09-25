cscript /e:jscript /nologo CleanReg.js

if exist *.dll del /Q *.dll
if exist *.pdb del /Q *.pdb
if exist *.exe del /Q *.exe
if exist 1033 del /Q 1033
