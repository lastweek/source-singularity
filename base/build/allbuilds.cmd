@echo off

@rem --------------------------------------------------------------------------
@rem A script to run through the standard build steps of the
@rem automated build system.  The script runs in the developers
@rem singularity directory and usually copies the source tree to a
@rem temporary directory and runs through the builds there.
@rem
@rem This will detect build failures across the tested
@rem configurations, but will not detect revision control failures,
@rem such as failing to add files to the repository.
@rem --------------------------------------------------------------------------

setlocal
setlocal EnableExtensions
if ERRORLEVEL 1 (
    echo Failed to enable externsions.
    exit /b 1
)

set FAILONCE=
set INPLACE=
set NOCLEAN=
set NOPURGE=

:parse
if /I .%1==./failonce (
    set FAILONCE=1
    shift /1
    goto :parse
)

if /I .%1==./inplace (
    set INPLACE=1
    set NOPURGE=1
    shift /1
    goto :parse
)

if /I .%1==./noclean (
    set NOCLEAN=1
    shift /1
    goto :parse
)

if /I .%1==./nopurge (
    set NOPURGE=1
    shift /1
    goto :parse
)

if /I NOT ".%1" == "." (
    echo "oops: %1"
    goto :usage
)

if not defined SINGULARITY_ROOT (
    if exist .\build\sgc.exe (
        set SINGULARITY_ROOT=%CD%
    ) else (
        echo "SINGULARITY_ROOT not defined."
        exit /b 2
    )
)

if "%time:~0,1%" == " " (
    set TIMESTAMP=0%Time:~1,1%%Time:~3,2%%Time:~6,2%
) else (
    set TIMESTAMP=%Time:~0,2%%Time:~3,2%%Time:~6,2%
)
set DATESTAMP=%Date:~12,2%%Date:~4,2%%Date:~7,2%-%TIMESTAMP%

if defined INPLACE (
    set WORKDIR=%SINGULARITY_ROOT%
) else (
    call :cleanup_state %Temp%
    set WORKDIR=%Temp%\Sing%DATESTAMP%
    @rem cmd.exe is unable to expand %WORKDIR% in
    @rem the next command.  Delayed expansion does not help either.
    call :populate_workdir %Temp%\Sing%DATESTAMP%
    if ERRORLEVEL 1 goto :cleanup
)

pushd %WORKDIR%
if ERRORLEVEL 1 (
    @rem If we fail, halt to avoid deleting the 
    @rem original sources.  This is mainly useful if debugging with a
    @rem partial build.
    echo.Failed to change to work directory.
    exit /b 1
)

@rem for %%i in ("/legacy /kcc /pms /prototype" ) do (
for %%i in ( "/legacy /kms /pms /release" "/legacy /kcc /pms /debug" "/legacy /kms /pms /debug" "/legacy /kss /pms /debug" "/apic /kms /pms /release" "/legacy /kms /pms /debug /paging" ) do (
    call :do_build %%i
    if ERRORLEVEL 1 (
        if defined FAILONCE goto :done
    )
)

goto :done

@rem cleanup_state <directory>
@rem
@rem Remove all directories under <directory> that have name like Sing*
@rem in the belief that earlier passes of this script have generated them.
@rem
:cleanup_state
    echo.Cleaning up former working directories under:
    echo.     %1
    for /d %%d in (%1\Sing*) do (
        rmdir /q/s %%d 2>nul
    )
    exit /b 0

@rem populate_workdir <directory>
@rem
@rem Creates specified directory and copies Singularity source
@rem tree beneath it.
@rem
:populate_workdir
    mkdir %1
    if ERRORLEVEL 1 (
        echo Halted.  Could not make work directory %1.
        exit /b 2
    )
    echo.Copying files to work directory:
    echo.    %1
    set COPYLOG=.\copy.log
    xcopy /s /e %SINGULARITY_ROOT% %1 1>%COPYLOG% 2>&1
    if ERRORLEVEL 1 (
        echo "Failed: consult error log %COPYLOG%"
        exit /b 1
    )
    del %COPYLOG% >nul
    exit /b 0

@rem do_build <quoted_setenv_args>
@rem
@rem Unquotes arguments for setenv and then runs nmake.
@rem NB By default realclean makefile target is exercised before the all
@rem target.  If NOCLEAN is defined, it stops realclean from being
@rem exercised.
@rem
:do_build
    @echo off
    setlocal
    set SE_ARGS=%1
    set SE_ARGS=%SE_ARGS:~1,-1%
    set LOGFILE=%TEMP%\%DATESTAMP%_%SE_ARGS: =_%
    set LOGFILE=%LOGFILE:/=%.txt

    echo Running build with %SE_ARGS%
    if defined NOCLEAN (
        set TARGETS=all
    ) else (
        set TARGETS=realclean all
    )

    for %%t in (%TARGETS%) do (
        @rem it would be nice to tee the output here, but the errorlevel
        @rem output appears to become that of the tee program rather than
        @rem the status of the pipe (this is an absymal scripting
        @rem environment).  We need wrapper process that manages the pipe
        @rem and traps the error and reports it back.
        start "nmake %%t" /WAIT cmd.exe /c ".\setenv.cmd /notitle %SE_ARGS% nmake %%t 1>%LOGFILE% 2>&1"
        if ERRORLEVEL 1 (
            echo.    Failed trying to run nmake %%t - Consult %LOGFILE%.
            exit /b 2
        )
    )
    echo.    Passed.
    exit /b 0

:usage
echo.Usage:
echo.    allbuilds.cmd [options]
echo.
echo.Summary:
echo.    Run standard builds using source in current tree.
echo.
echo.    By default a work directory is created and the current source tree
echo.is copied underneath it.  Clean builds of all the standard configurations
echo.are then performed in the work directory.
echo.
echo.Options:
echo.    /failonce   Stop builds after first failure.
echo.    /inplace    Perform builds in place (implicit /nopurge to keep source tree).
echo.    /noclean    Do not run 'nmake realclean' between builds.
echo.    /nopurge    Keep work directory in event of failure.
echo.

exit /b 1

:done
popd

:cleanup

@rem VC8 starts up a pdb server that will stick around for a couple of
@rem minutes keeping files open in the work directory.
taskkill /F /IM mspdbsrv.exe 1>nul 2>&1

@rem Be really careful before erasing work directory.
if not defined INPLACE (
    if not defined NOPURGE (
        rmdir /s/q %WORKDIR%
    )
)

