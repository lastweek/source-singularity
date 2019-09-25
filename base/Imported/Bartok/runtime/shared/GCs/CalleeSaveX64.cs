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
    using Microsoft.Singularity.Isal;
#endif


    [MixinConditional("X64")]
    [MixinConditional("ISA_IX64")]
    [Mixin(typeof(System.GCs.CalleeSaveRegisters))]
    [AccessedByRuntime("referenced from halforgc.asm")]
    internal struct CalleeSaveRegistersX64 /* : CalleeSaveRegisters */
    {

        [MixinOverride]
        internal void DebugTrace() {
            Trace.Log(Trace.Area.Stack,
                      "Registers:  EBX={0:x}, EDI={1:x}, ESI={2:x}, EBP={3:x}"+
                      "\nR12={4:x}, R13={5:x}, R14={6:x}, R15={7:x}",
                      __arglist(this.EBX, this.EDI, this.ESI, this.EBP,
                                this.R12, this.R13, this.R14, this.R15));
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
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal UIntPtr R12;
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal UIntPtr R13;
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal UIntPtr R14;
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal UIntPtr R15;
    }

    [MixinConditional("X64")]
    [MixinConditional("ISA_IX64")]
    [Mixin(typeof(System.GCs.CalleeSaveLocations))]
    internal unsafe struct CalleeSaveLocationsX64 /* : CalleeSaveLocations */
    {

#if SINGULARITY_KERNEL
        [MixinOverride]
        internal void SetCalleeSaves(SpillContext *context) {
            EBX.SetCalleeReg(&context->bx);
            EDI.SetCalleeReg(&context->di);
            ESI.SetCalleeReg(&context->si);
            EBP.SetCalleeReg(&context->bp);
            R12.SetCalleeReg(&context->r12);
            R13.SetCalleeReg(&context->r13);
            R14.SetCalleeReg(&context->r14);
            R15.SetCalleeReg(&context->r15);
        }
#endif

        [MixinOverride]
        internal
        void SetCalleeSaves(CalleeSaveRegistersX64 *calleeSaveRegisters)
        {
            EBX.SetCalleeReg(&calleeSaveRegisters->EBX);
            EDI.SetCalleeReg(&calleeSaveRegisters->EDI);
            ESI.SetCalleeReg(&calleeSaveRegisters->ESI);
            EBP.SetCalleeReg(&calleeSaveRegisters->EBP);
            R12.SetCalleeReg(&calleeSaveRegisters->R12);
            R13.SetCalleeReg(&calleeSaveRegisters->R13);
            R14.SetCalleeReg(&calleeSaveRegisters->R14);
            R15.SetCalleeReg(&calleeSaveRegisters->R15);
        }

        [MixinOverride]
        internal void ClearCalleeSaves() {
            EBX.ClearCalleeReg();
            ESI.ClearCalleeReg();
            EDI.ClearCalleeReg();
            EBP.ClearCalleeReg();
            R12.ClearCalleeReg();
            R13.ClearCalleeReg();
            R14.ClearCalleeReg();
            R15.ClearCalleeReg();
        }

        [MixinOverride]
        internal void ScanLiveRegs(UIntPtr mask,
                                   NonNullReferenceVisitor referenceVisitor)
        {
            EDI.ScanLiveReg((mask >> 2) & 0x3, referenceVisitor);
            ESI.ScanLiveReg((mask >> 4) & 0x3, referenceVisitor);
            EBX.ScanLiveReg((mask >> 0) & 0x3, referenceVisitor);
            R12.ScanLiveReg((mask >> 6) & 0x3, referenceVisitor);
            R13.ScanLiveReg((mask >> 8) & 0x3, referenceVisitor);
            R14.ScanLiveReg((mask >> 10) & 0x3, referenceVisitor);
            R15.ScanLiveReg((mask >> 12) & 0x3, referenceVisitor);
            EBP.ScanLiveReg((mask >> 14) & 0x3, referenceVisitor);
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
                VTable.Assert((calleeSaveMask & 0x100) == 0,
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
            if ((calleeSaveMask & 0x80) != 0) {
                EBP.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x4) != 0) {
                ESI.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x2) != 0) {
                EDI.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x8) != 0) {
                R12.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x10) != 0) {
                R13.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x20) != 0) {
                R14.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x40) != 0) {
                R15.PopFrameReg(ref calleeSaveStart);
            }
        }

        [MixinOverride]
        internal void ClearFrame(UIntPtr calleeSaveMask,
                                 bool framePointerOmitted)
        {
            if (!framePointerOmitted) {
                VTable.Assert((calleeSaveMask & 0x100) == 0,
                              "EBP should not be callee saved");
                EBP.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x1) != 0) {
                EBX.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x80) != 0) {
                EBP.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x4) != 0) {
                ESI.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x2) != 0) {
                EDI.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x8) != 0) {
                R12.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x10) != 0) {
                R13.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x20) != 0) {
                R14.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x40) != 0) {
                R15.ClearFrameReg();
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
        CalleeSaveLocations.RegLocation R12;
        CalleeSaveLocations.RegLocation R13;
        CalleeSaveLocations.RegLocation R14;
        CalleeSaveLocations.RegLocation R15;

    }

}
