echo 
set config=%Configuration%.x86.%COLLECTOR_APP%

set apps=%SINGULARITY_ROOT%.obj\Apps\%config%
set lib=%SINGULARITY_ROOT%.obj\Libraries\%config%
set run=%SINGULARITY_ROOT%.obj\AppRuntime\%config%
set runnative=%SINGULARITY_ROOT%.obj\AppRuntimeNative\%config%
set sys= %SINGULARITY_ROOT%.obj\Kernel\Prototype.x86.ApicPC.Min.MarkSweep.msil
set dest=%SINGULARITY_ROOT%\Distro\Files\HelloTest
set assemblies=%SINGULARITY_ROOT%\Distro\Files\assemblies
set native=%SINGULARITY_ROOT%\Distro\Files\native

mkdir %dest%
mkdir %assemblies%
mkdir %native%

for %%i in ( Directory.Contracts.dll Io.Contracts.dll Singularity.V1.dll System.Console.dll) do (
   copy %lib%\%%i  %assemblies%
)

for %%i in (ILHelpers.dll Corlibsg.dll Corlib.dll Microsoft.SingSharp.Runtime.dll System.Compiler.Runtime.dll) do (
   copy %run%\%%i  %assemblies%
)

for %%i in (native.lib Singularity.V1.lib) do (
   copy %runnative%\%%i  %native%
)

copy %apps%\hello.exe %dest%

copy %apps%\hello.manifest %dest%\hello.mani
