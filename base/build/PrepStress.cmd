@echo off

if /I "%ScriptDebug%" EQU "Yes" (
   @echo on
)

@rem The purpose of this script is to either bootstrap or update a directory for the purpose
@rem of executing stress on a Stress Runner machine.
@rem
@rem Simply create a local stress directory (c:\stress), put this script in it, and execute
@rem it.
@rem
@rem You can update this script by taking a new one from Source Depot and then re-executing
@rem it, at some date in the future.
@rem
@rem It is very simple, so you can just do all these steps by hand if you prefer (like
@rem explicitly executing the AT command to schedule a stress run).

set LocalStressDir=c:\Stress

md %LocalStressDir%
copy %SINGULARITY_ROOT%\build\SizeCompare.exe %LocalStressDir%
copy %SINGULARITY_ROOT%\build\internal\CheckinWizard\x86\smartmail.exe %LocalStressDir%
copy %SINGULARITY_ROOT%\build\buildtracker\scripts\StressMail.cmd %LocalStressDir%

copy %SINGULARITY_ROOT%\build\buildtracker\scripts\StressMandelbrot.cmd %LocalStressDir%
copy %SINGULARITY_ROOT%\build\buildtracker\scripts\StressWeb.cmd %LocalStressDir%

echo Use the AT command to set up regular stress launches.  To manually launch:
echo    Mandelbrot: cmd.exe /c %LocalStressDir%\StressMandelbrot.cmd
echo    WebStress:  cmd.exe /c %LocalStressDir%\StressWeb.cmd

