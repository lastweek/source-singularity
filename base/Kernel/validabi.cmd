@echo off
if .==.%1 goto usage
if .%1==./? goto usage

echo VALIDABI: Checking for object references.
findstr Class_ %*
if %ERRORLEVEL%==0 (
echo ERROR: Object references are illegal in the Singularity ABI.
exit /b 999
)

echo VALIDABI: Checking for member functions.
findstr /c:"?m_" %*
if %ERRORLEVEL%==0 (
echo ERROR: Member functions are illegal in the Singularity ABI.
exit /b 999
)

echo VALIDABI: Checking for exported const fields.
findstr /c:"?c_" %*
if %ERRORLEVEL%==0 (
echo ERROR: Exported constant values are illegal in the Singularity ABI.
exit /b 999
)

echo VALIDABI: Checking for fields.
findstr /c:"?s_" %*
if %ERRORLEVEL%==0 (
echo ERROR: Exported global variables are illegal in the Singularity ABI.
exit /b 999
)

echo VALIDABI: ABI successfully validated.
exit /b 0
goto exit

:usage
echo.Usage:
echo.    VALIDABI.CMD [abifile}
echo.
echo.Summary:
echo.    Check the .DEF file for violations of the follwing ABI invariants:
echo.        * Object references never cross the ABI boundary.
echo.        * Member functions are never exported as ABI functions.
echo.        * Constant values are never exported in the ABI.
echo.        * Global variables are never exported in the ABI.
echo.
echo.    Returns 0 if the ABI is valid.
echo.    Returns 999 if the ABI is invalid.
echo.

:exit
