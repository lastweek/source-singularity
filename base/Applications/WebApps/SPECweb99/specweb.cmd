cd %SINGULARITY_ROOT%
nmake
if errorlevel 1 goto exit
cd %SINGULARITY_ROOT%\Applications\Cadgen99
nmake
if errorlevel 1 goto exit
cd %SINGULARITY_ROOT%\Applications\Upfgen99
nmake
if errorlevel 1 goto exit
cd %SINGULARITY_ROOT%\Applications\Network
nmake
if errorlevel 1 goto exit
cd %SINGULARITY_ROOT%\Applications\WebApps
nmake
if errorlevel 1 goto exit
cd %SINGULARITY_ROOT%\Applications\Cassini
nmake
if errorlevel 1 goto exit
cd %SINGULARITY_ROOT%\Applications\Benchmarks\Perfcnt
nmake
if errorlevel 1 goto exit
cd %SINGULARITY_ROOT%\Distro
nmake
if errorlevel 1 goto exit
cd %SINGULARITY_ROOT%
