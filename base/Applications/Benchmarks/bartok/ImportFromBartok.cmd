@echo.
@echo *** Checking out Bartok MSIL files.
@echo.
sd edit msil\bartok.*
@if errorlevel 1 goto exit

@echo.
@echo *** Copying files from Bartok enlistment.
@echo.

@if exist c:\othercode\act\bartok\obj\sing-debug-x86-x86\nul (
   copy c:\othercode\act\bartok\obj\sing-debug-x86-x86\bartok.* msil
   @if errorlevel 1 goto exit
)

@if exist c:\act\bartok\obj\sing-debug-x86-x86\nul (
   copy c:\act\bartok\obj\sing-debug-x86-x86\bartok.* msil
   @if errorlevel 1 goto exit
)

@if exist c:\home\act-dev7\bartok\obj\sing-debug-x86-x86\nul (
   copy c:\home\act-dev7\bartok\obj\sing-debug-x86-x86\bartok.* msil
   @if errorlevel 1 goto exit
)

@echo.
@echo *** Deleting unused files.
@echo.
del msil\bartok.tryallextension.* 2>nul
