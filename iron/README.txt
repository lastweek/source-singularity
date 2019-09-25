This directory contains experimental verified Ironclad code.
See http://research.microsoft.com/ironclad for more details.

The build process requires PowerShell.
(included with Windows 7, or downloadable separately)

The build process uses PowerShell scripts, so script execution must be enabled.
(For example, launch "powershell.exe -ExecutionPolicy RemoteSigned".)

To build the tools from a PowerShell prompt, simply type:

  .\build-tools

This will build all of the basic tools, including NuBuild (aka IronBuild),
our distributed verification and build tool.

Then, in PowerShell (or Cygwin for that matter), run:

  ./bin_tools/NuBuild/NuBuild.exe -j 3 BatchDafny src/Dafny/Apps/apps.dfy.batch

to do a high-level Dafny verification using 3-way local parallelism.

You can run:

  ./bin_tools/NuBuild/NuBuild.exe -j 3 IroncladApp src/Dafny/Apps/DafnyCCTest/Main.i.dfy

to verify and build a very simple Ironclad App.  Try pointing it at other files in:
  ./src/Dafny/Apps/*/Main.i.dfy
to build the other apps.

To build a version that actually boots, use "BootableApp" in place of "IroncladApp".

To build a debug version that runs on Windows, use the --windows flag to NuBuild.  This is most useful when accompanied by the --useFramePointer which enables more detailed profiling.
