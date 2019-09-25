@echo off

rem To use this script, first build TestAmlParser.csproj, then simply run it.
rem It is an end-to-end ACPI resource enumeration test based on data from real
rem machines. Logs are placed in %SINGULARITY_ROOT%\Windows\acpi\automated_test_logs

mkdir "%SINGULARITY_ROOT%\Windows\acpi\automated_test_logs" 2> NUL

echo Testing Dell Precision 380...
"%SINGULARITY_OBJROOT%\Windows\Prototype.ApicMP\TestAmlParser.exe" "/tracefile=%SINGULARITY_ROOT%\Windows\acpi\TestFiles\DellPrecision380\read_write_trace.txt" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\DellPrecision380\ACPI.DSDT.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\DellPrecision380\ACPI.SSDT.st_ex.dmp" > "%SINGULARITY_ROOT%\Windows\acpi\automated_test_logs\DellPrecision380.log"
IF ERRORLEVEL 1 goto error

echo Testing Dell Precision 490...
"%SINGULARITY_OBJROOT%\Windows\Prototype.ApicMP\TestAmlParser.exe" "/tracefile=%SINGULARITY_ROOT%\Windows\acpi\TestFiles\DellPrecision490\read_write_trace.txt" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\DellPrecision490\ACPI.DSDT.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\DellPrecision490\ACPI.SSDT.st_ex.dmp" > "%SINGULARITY_ROOT%\Windows\acpi\automated_test_logs\DellPrecision490.log"
IF ERRORLEVEL 1 goto error

echo Testing HP XW 4400...
"%SINGULARITY_OBJROOT%\Windows\Prototype.ApicMP\TestAmlParser.exe" "/tracefile=%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPXW4400\read_write_trace.txt" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPXW4400\ACPI.DSDT.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPXW4400\ACPI.SSDT.DSDT_HW.dmp" > "%SINGULARITY_ROOT%\Windows\acpi\automated_test_logs\HPXW4400.log"
IF ERRORLEVEL 1 goto error

echo Testing HP Compaq with TPM...
"%SINGULARITY_OBJROOT%\Windows\Prototype.ApicMP\TestAmlParser.exe" "/tracefile=%SINGULARITY_ROOT%\Windows\acpi\TestFiles\CompaqTPM\read_write_trace.txt" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\CompaqTPM\ACPI.DSDT.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\CompaqTPM\ACPI.SSDT.PROJECT.dmp" > "%SINGULARITY_ROOT%\Windows\acpi\automated_test_logs\CompaqTPM.log"
IF ERRORLEVEL 1 goto error

echo Testing AMD with Infineon TPM...
"%SINGULARITY_OBJROOT%\Windows\Prototype.ApicMP\TestAmlParser.exe" "/tracefile=%SINGULARITY_ROOT%\Windows\acpi\TestFiles\AMDTPM\read_write_trace.txt" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\AMDTPM\ACPI.DSDT.dmp" > "%SINGULARITY_ROOT%\Windows\acpi\automated_test_logs\AMDTPM.log"
IF ERRORLEVEL 1 goto error

echo Testing HP Compaq d530 CMT...
"%SINGULARITY_OBJROOT%\Windows\Prototype.ApicMP\TestAmlParser.exe" "/tracefile=%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\read_write_trace.txt" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.DSDT.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.PROJECT.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.CORE_PNP.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.CORE_UTL.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.VILLTBL1.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.LGCYLITE.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.UART2.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.FLOPPY.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.APIC.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.PNP_PRSS.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.UR2_PRSS.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.FPY_PRSS.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.S3.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.CORE_S3.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.L08.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\HPD530CMT\ACPI.SSDT.FINIS.dmp" > "%SINGULARITY_ROOT%\Windows\acpi\automated_test_logs\HPD530CMT.log"
IF ERRORLEVEL 1 goto error

echo Testing XPC...
"%SINGULARITY_OBJROOT%\Windows\Prototype.ApicMP\TestAmlParser.exe" "/tracefile=%SINGULARITY_ROOT%\Windows\acpi\TestFiles\XPC\read_write_trace.txt" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\XPC\ACPI.DSDT.dmp" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\XPC\ACPI.SSDT.POWERNOW.dmp" > "%SINGULARITY_ROOT%\Windows\acpi\automated_test_logs\XPC.log"
IF ERRORLEVEL 1 goto error

echo Testing Virtual PC...
"%SINGULARITY_OBJROOT%\Windows\Prototype.ApicMP\TestAmlParser.exe" "/tracefile=%SINGULARITY_ROOT%\Windows\acpi\TestFiles\VirtualPC\read_write_trace.txt" "%SINGULARITY_ROOT%\Windows\acpi\TestFiles\VirtualPC\ACPI.DSDT.dmp" > "%SINGULARITY_ROOT%\Windows\acpi\automated_test_logs\VirtualPC.log"
IF ERRORLEVEL 1 goto error

echo.
echo All tests successful.
goto end
:error
echo Encountered errors.
:end
