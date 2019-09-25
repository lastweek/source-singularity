;; trusted assembly language definitions

externdef _$$?callSiteTableCount:NEAR
externdef _$$?returnAddressToCallSiteSetNumbers:NEAR
externdef _$$?callSiteSetCount:NEAR
externdef _$$?codeBaseStartTable:NEAR
externdef _$$?activationDescriptorTable:NEAR
externdef _$$?callSiteSetNumberToIndex:NEAR
externdef _$$?sectionCount:NEAR
externdef _$$?dataSectionEnd:NEAR
externdef _$$?staticDataPointerBitMap:NEAR
externdef _$$?dataSectionBase:NEAR
externdef ?_vtable@String@System@@2UVT$0028Class$0028System_String$0029$003aAllocObject$0029@@A:NEAR
externdef ?_vtable@Vector_uint8@@2UVT$0028System_Byte$005b$005d$003aAllocVector$0029@@A:NEAR
externdef ?g_Main@Kernel@@SIXXZ:NEAR

PUBLIC _$$StackCheck

?STRING_VTABLE EQU ?_vtable@String@System@@2UVT$0028Class$0028System_String$0029$003aAllocObject$0029@@A
?BYTE_VECTOR_VTABLE EQU ?_vtable@Vector_uint8@@2UVT$0028System_Byte$005b$005d$003aAllocVector$0029@@A

?FatalHandler EQU _?FatalHandler
?ErrorHandler EQU _?ErrorHandler
?FaultHandler EQU _?FaultHandler
?InterruptHandler EQU _?InterruptHandler
?KernelEntryPoint EQU ?g_Main@Kernel@@SIXXZ
_?Throw EQU ?g_Throw@NucleusCalls@@SIXXZ
_?AllocObject EQU ?g_AllocateObject@GC@System@@SIPAUObject@2@PAUVTable@2@@Z
_?AllocVector EQU ?g_AllocateVector@GC@System@@SIPAUArray@2@PAUVTable@2@H@Z
_?GarbageCollect EQU ?g_GarbageCollect@NucleusCalls@@SIXXZ
_?GetStackState EQU ?g_GetStackState@NucleusCalls@@SIII@Z
_?ResetStack EQU ?g_ResetStack@NucleusCalls@@SIXI@Z
_?YieldTo EQU ?g_YieldTo@NucleusCalls@@SIXI@Z
_?VgaTextWrite EQU ?g_VgaTextWrite@NucleusCalls@@SIXII@Z
_?TryReadKeyboard EQU ?g_TryReadKeyboard@NucleusCalls@@SIIXZ
_?SendEoi EQU ?g_SendEoi@NucleusCalls@@SIXXZ
_?StartTimer EQU ?g_StartTimer@NucleusCalls@@SIXI@Z
_?PciConfigRead32 EQU ?g_PciConfigRead32@NucleusCalls@@SIIII@Z
_?PciMemSetup EQU ?g_PciMemSetup@NucleusCalls@@SIII@Z
_?PciDmaBuffer EQU ?g_PciDmaBuffer@NucleusCalls@@SIPAUVector_uint8@@XZ
_?PciDmaPhysicalAddr EQU ?g_PciDmaPhysicalAddr@NucleusCalls@@SIIXZ
_?PciMemRead32 EQU ?g_PciMemRead32@NucleusCalls@@SIIII@Z
_?PciMemWrite32 EQU ?g_PciMemWrite32@NucleusCalls@@SIXIII@Z
_?CycleCounter EQU ?g_Rdtsc@NucleusCalls@@SI_JXZ
_?DebugPrintHex EQU ?g_DebugPrintHex@NucleusCalls@@SIXII@Z
