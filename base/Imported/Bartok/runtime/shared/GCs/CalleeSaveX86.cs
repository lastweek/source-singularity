//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


namespace System.GCs {

    using Microsoft.Bartok.Options;

    using System.Runtime.CompilerServices;

#if SINGULARITY
    using Microsoft.Singularity;
#endif

    [MixinConditional("X86")]
    [MixinConditional("ISA_IX86")]
    [Mixin(typeof(System.GCs.CalleeSaveRegisters))]
    [AccessedByRuntime("referenced from halforgc.asm")]
    internal struct CalleeSaveRegistersX86 /* : CalleeSaveRegisters */
    {

        [MixinOverride]
        internal void DebugTrace() {
            Trace.Log(Trace.Area.Stack,
                      "Registers:  EBX={0:x}, EDI={1:x}, ESI={2:x}, EBP={3:x}",
                      __arglist(this.EBX, this.EDI, this.ESI, this.EBP));
        }

        [MixinOverride]
        internal UIntPtr GetFramePointer()
        {
            return this.EBP;
        }

        [AccessedByRuntime("referenced from halforgc.asm")]
        internal UIntPtr EBX;
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal UIntPtr EDI;
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal UIntPtr ESI;
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal UIntPtr EBP;
    }

    [MixinConditional("X86")]
    [MixinConditional("ISA_IX86")]
    [Mixin(typeof(System.GCs.CalleeSaveLocations))]
    internal unsafe struct CalleeSaveLocationsX86 /* : CalleeSaveLocations */
    {

#if SINGULARITY_KERNEL
#if false
        [MixinOverride]
        internal void SetCalleeSaves(SpillContext *context) {
            EBX.SetCalleeReg(&context->ebx);
            EDI.SetCalleeReg(&context->edi);
            ESI.SetCalleeReg(&context->esi);
            EBP.SetCalleeReg(&context->ebp);
        }
#endif
#endif

        [MixinOverride]
        internal
        void SetCalleeSaves(CalleeSaveRegistersX86 *calleeSaveRegisters)
        {
            EBX.SetCalleeReg(&calleeSaveRegisters->EBX);
            EDI.SetCalleeReg(&calleeSaveRegisters->EDI);
            ESI.SetCalleeReg(&calleeSaveRegisters->ESI);
            EBP.SetCalleeReg(&calleeSaveRegisters->EBP);
        }

        [MixinOverride]
        internal void ClearCalleeSaves() {
            EBX.ClearCalleeReg();
            ESI.ClearCalleeReg();
            EDI.ClearCalleeReg();
            EBP.ClearCalleeReg();
        }

        [MixinOverride]
        internal void ScanLiveRegs(UIntPtr mask,
                                   NonNullReferenceVisitor referenceVisitor)
        {
            EDI.ScanLiveReg((mask >> 2) & 0x3, referenceVisitor);
            ESI.ScanLiveReg((mask >> 4) & 0x3, referenceVisitor);
            EBX.ScanLiveReg((mask >> 0) & 0x3, referenceVisitor);
            EBP.ScanLiveReg((mask >> 6) & 0x3, referenceVisitor);
        }

        [MixinOverride]
        internal void PopFrame(UIntPtr *framePointer,
                               UIntPtr calleeSaveMask,
                               bool framePointerOmitted,
                               bool hasTransitionRecord)
        {
            UIntPtr *calleeSaveStart;
            if (framePointerOmitted) {
                calleeSaveStart = framePointer - 1;
            } else {
                VTable.Assert((calleeSaveMask & 0x10) == 0,
                              "EBP should not be callee saved");
                calleeSaveStart = framePointer;
                EBP.PopFrameReg(ref calleeSaveStart);
            }
            if (hasTransitionRecord) {
                calleeSaveStart -=
                    sizeof(CallStack.TransitionRecord) / sizeof(UIntPtr);
            }
            // Note: the order in which these appear is important!
            if ((calleeSaveMask & 0x1) != 0) {
                EBX.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x8) != 0) {
                EBP.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x4) != 0) {
                ESI.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x2) != 0) {
                EDI.PopFrameReg(ref calleeSaveStart);
            }
        }

        [MixinOverride]
        internal void ClearFrame(UIntPtr calleeSaveMask,
                                 bool framePointerOmitted)
        {
            if (!framePointerOmitted) {
                VTable.Assert((calleeSaveMask & 0x10) == 0,
                              "EBP should not be callee saved");
                EBP.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x1) != 0) {
                EBX.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x8) != 0) {
                EBP.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x4) != 0) {
                ESI.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x2) != 0) {
                EDI.ClearFrameReg();
            }
        }

        [MixinOverride]
        internal UIntPtr GetFramePointer()
        {
            return EBP.value;
        }

        CalleeSaveLocations.RegLocation EBX;
        CalleeSaveLocations.RegLocation EDI;
        CalleeSaveLocations.RegLocation ESI;
        CalleeSaveLocations.RegLocation EBP;

    }

}
