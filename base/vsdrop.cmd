@ ================================================================================
@ This script will pick up new compilers, libs, and headers from VS
@ ================================================================================

set VS_PATH="c:\program files\microsoft visual studio 8"
set DROP_PATH=%SINGULARITY_ROOT%

sd edit %SINGULARITY_ROOT%\build\Microsoft.VC80.CRT.manifest
sd edit %SINGULARITY_ROOT%\build\Microsoft.VC80.DebugCRT.manifest
sd edit %SINGULARITY_ROOT%\build\msobj80.dll
sd edit %SINGULARITY_ROOT%\build\mspdb80.dll
sd edit %SINGULARITY_ROOT%\build\mspdbcore.dll
sd edit %SINGULARITY_ROOT%\build\mspdbsrv.exe
sd edit %SINGULARITY_ROOT%\build\msvcm80.dll
sd edit %SINGULARITY_ROOT%\build\msvcp80.dll
sd edit %SINGULARITY_ROOT%\build\msvcp80d.dll
sd edit %SINGULARITY_ROOT%\build\msvcr80.dll
sd edit %SINGULARITY_ROOT%\build\msvcr80d.dll
sd edit %SINGULARITY_ROOT%\build\nmake.exe
sd edit %SINGULARITY_ROOT%\build\rc.exe
sd edit %SINGULARITY_ROOT%\build\rcdll.dll

copy /y %VS_PATH%\vc\redist\x86\Microsoft.VC80.CRT\Microsoft.VC80.CRT.manifest %DROP_PATH%\build\
copy /y %VS_PATH%\vc\redist\x86\Microsoft.VC80.CRT\msvcm80.dll %DROP_PATH%\build\
copy /y %VS_PATH%\vc\redist\x86\Microsoft.VC80.CRT\msvcp80.dll %DROP_PATH%\build\
copy /y %VS_PATH%\vc\redist\x86\Microsoft.VC80.CRT\msvcr80.dll %DROP_PATH%\build\
copy /y %VS_PATH%\vc\redist\Debug_NonRedist\x86\Microsoft.VC80.DebugCRT\Microsoft.VC80.DebugCRT.manifest %DROP_PATH%\build\
copy /y %VS_PATH%\vc\redist\Debug_NonRedist\x86\Microsoft.VC80.DebugCRT\msvcp80d.dll %DROP_PATH%\build\
copy /y %VS_PATH%\vc\redist\Debug_NonRedist\x86\Microsoft.VC80.DebugCRT\msvcr80d.dll %DROP_PATH%\build\

copy /y %VS_PATH%\common7\ide\msobj80.dll %DROP_PATH%\build\
copy /y %VS_PATH%\common7\ide\mspdb80.dll %DROP_PATH%\build\
copy /y %VS_PATH%\common7\ide\mspdbcore.dll %DROP_PATH%\build\
copy /y %VS_PATH%\common7\ide\mspdbsrv.exe %DROP_PATH%\build\

copy /y %VS_PATH%\vc\bin\nmake.exe %DROP_PATH%\build\
copy /y %VS_PATH%\vc\bin\rc.exe %DROP_PATH%\build\
copy /y %VS_PATH%\vc\bin\rcdll.dll %DROP_PATH%\build\

sd edit %SINGULARITY_ROOT%\build\x86_x86\c1.dll
sd edit %SINGULARITY_ROOT%\build\x86_x86\c1xx.dll
sd edit %SINGULARITY_ROOT%\build\x86_x86\c2.dll
sd edit %SINGULARITY_ROOT%\build\x86_x86\cl.exe
sd edit %SINGULARITY_ROOT%\build\x86_x86\cl.exe.config
sd edit %SINGULARITY_ROOT%\build\x86_x86\dumpbin.exe
sd edit %SINGULARITY_ROOT%\build\x86_x86\editbin.exe
sd edit %SINGULARITY_ROOT%\build\x86_x86\lib.exe
sd edit %SINGULARITY_ROOT%\build\x86_x86\link.exe
sd edit %SINGULARITY_ROOT%\build\x86_x86\link.exe.config
sd edit %SINGULARITY_ROOT%\build\x86_x86\ml.exe

copy /y %VS_PATH%\vc\bin\c1.dll %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\c1xx.dll %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\c2.dll %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\cl.exe %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\cl.exe.config %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\dumpbin.exe %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\editbin.exe %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\lib.exe %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\link.exe %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\link.exe.config %DROP_PATH%\build\x86_x86\
copy /y %VS_PATH%\vc\bin\ml.exe %DROP_PATH%\build\x86_x86\

sd edit %SINGULARITY_ROOT%\build\x86_x64\c1.dll
sd edit %SINGULARITY_ROOT%\build\x86_x64\c1xx.dll
sd edit %SINGULARITY_ROOT%\build\x86_x64\c2.dll
sd edit %SINGULARITY_ROOT%\build\x86_x64\cl.exe
sd edit %SINGULARITY_ROOT%\build\x86_x64\cl.exe.config
sd edit %SINGULARITY_ROOT%\build\x86_x64\dumpbin.exe
sd edit %SINGULARITY_ROOT%\build\x86_x64\editbin.exe
sd edit %SINGULARITY_ROOT%\build\x86_x64\lib.exe
sd edit %SINGULARITY_ROOT%\build\x86_x64\link.exe
sd edit %SINGULARITY_ROOT%\build\x86_x64\link.exe.config
sd edit %SINGULARITY_ROOT%\build\x86_x64\ml64.exe

copy /y %VS_PATH%\vc\bin\x86_amd64\c1.dll %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\c1xx.dll %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\c2.dll %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\cl.exe %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\cl.exe.config %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\dumpbin.exe %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\editbin.exe %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\lib.exe %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\link.exe %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\link.exe.config %DROP_PATH%\build\x86_x64\
copy /y %VS_PATH%\vc\bin\x86_amd64\ml64.exe %DROP_PATH%\build\x86_x64\

sd edit %SINGULARITY_ROOT%\build\x86_arm\c1.dll
sd edit %SINGULARITY_ROOT%\build\x86_arm\c1xx.dll
sd edit %SINGULARITY_ROOT%\build\x86_arm\c2.dll
sd edit %SINGULARITY_ROOT%\build\x86_arm\cl.exe
sd edit %SINGULARITY_ROOT%\build\x86_arm\lib.exe
sd edit %SINGULARITY_ROOT%\build\x86_arm\link.exe
sd edit %SINGULARITY_ROOT%\build\x86_arm\midl.exe

copy /y %VS_PATH%\vc\ce\bin\x86_arm\c1.dll %DROP_PATH%\build\x86_arm\
copy /y %VS_PATH%\vc\ce\bin\x86_arm\c1xx.dll %DROP_PATH%\build\x86_arm\
copy /y %VS_PATH%\vc\ce\bin\x86_arm\c2.dll %DROP_PATH%\build\x86_arm\
copy /y %VS_PATH%\vc\ce\bin\x86_arm\cl.exe %DROP_PATH%\build\x86_arm\
copy /y %VS_PATH%\vc\ce\bin\x86_arm\lib.exe %DROP_PATH%\build\x86_arm\
copy /y %VS_PATH%\vc\ce\bin\x86_arm\link.exe %DROP_PATH%\build\x86_arm\
copy /y %VS_PATH%\vc\ce\bin\x86_arm\midl.exe %DROP_PATH%\build\x86_arm\

sd edit %SINGULARITY_ROOT%\Windows\Inc\assert.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\crtdefs.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\ctype.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\excpt.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\limits.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\objbase.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\sal.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\stdarg.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\stddef.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\stdio.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\stdlib.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\string.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\swprintf.inl
sd edit %SINGULARITY_ROOT%\Windows\Inc\time.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\time.inl
sd edit %SINGULARITY_ROOT%\Windows\Inc\vadefs.h
sd edit %SINGULARITY_ROOT%\Windows\Inc\wtime.inl

copy /y %VS_PATH%\vc\include\assert.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\crtdefs.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\ctype.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\excpt.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\limits.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\objbase.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\sal.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\stdarg.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\stddef.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\stdio.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\stdlib.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\string.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\swprintf.inl %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\time.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\time.inl %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\vadefs.h %DROP_PATH%\windows\inc\
copy /y %VS_PATH%\vc\include\wtime.inl %DROP_PATH%\windows\inc\

sd edit %SINGULARITY_ROOT%\Windows\Lib\x86\Kernel32.Lib
sd edit %SINGULARITY_ROOT%\Windows\Lib\x86\libcmt.lib
sd edit %SINGULARITY_ROOT%\Windows\Lib\x86\libcmt.pdb
sd edit %SINGULARITY_ROOT%\Windows\Lib\x86\msvcrt.lib
sd edit %SINGULARITY_ROOT%\Windows\Lib\x86\oldnames.lib

copy /y %VS_PATH%\vc\lib\kernel32.lib %DROP_PATH%\windows\lib\x86\
copy /y %VS_PATH%\vc\lib\libcmt.lib %DROP_PATH%\windows\lib\x86\
copy /y %VS_PATH%\vc\lib\libcmt.pdb %DROP_PATH%\windows\lib\x86\
copy /y %VS_PATH%\vc\lib\msvcrt.lib %DROP_PATH%\windows\lib\x86\
copy /y %VS_PATH%\vc\lib\oldnames.lib %DROP_PATH%\windows\lib\x86\

sd edit %SINGULARITY_ROOT%\Windows/Lib\x64\libcmt.lib
sd edit %SINGULARITY_ROOT%\Windows\Lib\x64\libcmt.pdb
sd edit %SINGULARITY_ROOT%\Windows\Lib\x64\msvcrt.lib

copy /y %VS_PATH%\vc\lib\amd64\libcmt.lib %DROP_PATH%\windows\lib\x64\
copy /y %VS_PATH%\vc\lib\amd64\libcmt.pdb %DROP_PATH%\windows\lib\x64\
copy /y %VS_PATH%\vc\lib\amd64\msvcrt.lib %DROP_PATH%\windows\lib\x64\
