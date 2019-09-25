@echo off
setlocal

rem ###### Remember the current directory ######
set CSI_ROOT=%~d0%~p0%XXXX_XXXX_XXXX
set CSI_ROOT=%CSI_ROOT:\XXXX_XXXX_XXXX=%

echo CSI_ROOT=%CSI_ROOT%

copy lcsc.exe csic.exe
copy lcsc.pdb csic.pdb

pushd %~d0%~p0%\..\..\build
sd edit csic.exe
sd edit csic.pdb
sd edit csic/*

copy /y %CSI_ROOT%\base\*.dll csic | findstr -v copied
copy /y %CSI_ROOT%\base\*.pdb csic | findstr -v copied
copy /y %CSI_ROOT%\bind\*.dll csic | findstr -v copied
copy /y %CSI_ROOT%\bind\*.pdb csic | findstr -v copied
copy /y %CSI_ROOT%\compiler\*.dll csic | findstr -v copied
copy /y %CSI_ROOT%\compiler\*.pdb csic | findstr -v copied
copy /y %CSI_ROOT%\emit\*.dll csic | findstr -v copied
copy /y %CSI_ROOT%\emit\*.pdb csic | findstr -v copied
copy /y %CSI_ROOT%\ilgen\*.dll csic | findstr -v copied
copy /y %CSI_ROOT%\ilgen\*.pdb csic | findstr -v copied
copy /y %CSI_ROOT%\parser\*.dll csic | findstr -v copied
copy /y %CSI_ROOT%\parser\*.pdb csic | findstr -v copied
copy /y %CSI_ROOT%\source\*.dll csic | findstr -v copied
copy /y %CSI_ROOT%\source\*.pdb csic | findstr -v copied
copy /y %CSI_ROOT%\typecheck\*.dll csic | findstr -v copied
copy /y %CSI_ROOT%\typecheck\*.pdb csic | findstr -v copied
copy /y %CSI_ROOT%\debug\bartok.* csic | findstr -v copied
copy /y %CSI_ROOT%\debug\bartok.* csic | findstr -v copied
copy /y %CSI_ROOT%\csic.* . | findstr -v copied

popd
set _FAIL=0
goto exit

:exit
exit /b %_FAIL%
