@rmdir /q /s obj 2>nul
@mkdir obj
@del log 2>nul

bartok.exe /Singularity /verbosity:silence /LinkedStacksRequireExternalBound=true /GCInlineAllocations=false /GCInlineWriteBarrier=false /UseSegmentRegister=true /OmitFramePointer=false /SymbolicDebug=true /DebugInline=true /IrSimpleInliner=false /UnnameTracedPtrs=true /Warnings=true /WholeProgram=true /GenCoffLineNumber=false /MarkSweepGC /minopt /IrSimpleInliner=false /out: obj\kernel.obj /outdir: obj kernel.exe Diagnostics.dll Hypercall.dll Loader.dll Directory.dll Stress.dll IoSystem.dll Hal.LegacyPC.dll System.Compiler.Runtime.dll ILHelpers.dll Microsoft.SingSharp.Runtime.dll Diagnostics.Contracts.dll Hypercall.Contracts.dll Directory.Contracts.dll FileSystem.Contracts.dll Io.Contracts.dll Stress.Contracts.dll Drivers.dll Security.Contracts.dll Security.dll SecurityService.dll
