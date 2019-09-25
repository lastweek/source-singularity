. .\env.ps1

$ROOT="."

. $ROOT\def.ps1 $args

$NMAKE = "$(ls $BUILD\nmake.exe)"
$MSBUILD="C:/Windows/Microsoft.NET/Framework/v4.0.30319/MSBuild.exe"

ensureDir("$OBJROOT")
ensureDir("$BINROOT")

# Cygwin make helpfully passes along an argument that NMAKE doesn't understand
$Env:MAKEFLAGS = ""

echo "Building NuBuild"
runShell "cd tools\NuBuild; & `"$MSBUILD`" NuBuild.sln"

ensureDir("$OBJROOT\Checked\BootLoader\SingLdrPc")
ensureDir("$OBJROOT\Checked\BootLoader\x86")
ensureDir("$OBJROOT\Checked\BootLoader\tpm")

echo "Building Bootloader"
runShell "cd src\Checked\BootLoader\SingLdrPc; & `"$NMAKE`" /nologo OBJ=..\..\..\..\obj$BUILD_SUFFIX\Checked\BootLoader" pxe-loader
