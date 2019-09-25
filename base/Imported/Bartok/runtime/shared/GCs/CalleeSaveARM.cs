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
    using Microsoft.Singularity.Isal.Arm;
#endif

    [MixinConditional("ARM")]
    [MixinConditional("ISA_ARM")]
    [Mixin(typeof(System.GCs.CalleeSaveRegisters))]
    [AccessedByRuntime("Referenced from halforgc.asm")]
    internal struct CalleeSaveRegistersARM /* : CalleeSaveRegisters */
    {

        [MixinOverride]
        internal void DebugTrace() {
            Trace.Log(Trace.Area.Stack,
                      "Registers: R4={0:x}, R5={0:x}, R6={0:x}, R7={0:x},\n           R8={0:x}, R9={0:x}, R10={0:x}, R11={0:x}",
                      __arglist(this.r4, this.r5, this.r6, this.r7,
                                this.r8, this.r9, this.r10, this.r11));
        }

        [MixinOverride]
        internal UIntPtr GetFramePointer()
        {
            return this.r11;
        }

        [AccessedByRuntime("Referenced from halforgc.asm")]
        internal UIntPtr r4;
        [AccessedByRuntime("Referenced from halforgc.asm")]
        internal UIntPtr r5;
        [AccessedByRuntime("Referenced from halforgc.asm")]
        internal UIntPtr r6;
        [AccessedByRuntime("Referenced from halforgc.asm")]
        internal UIntPtr r7;
        [AccessedByRuntime("Referenced from halforgc.asm")]
        internal UIntPtr r8;
        [AccessedByRuntime("Referenced from halforgc.asm")]
        internal UIntPtr r9;
        [AccessedByRuntime("Referenced from halforgc.asm")]
        internal UIntPtr r10;
        [AccessedByRuntime("Referenced from halforgc.asm")]
        internal UIntPtr r11;

    }

    [MixinConditional("ARM")]
    [MixinConditional("ISA_ARM")]
    [Mixin(typeof(System.GCs.CalleeSaveLocations))]
    internal unsafe struct CalleeSaveLocationsARM /* : CalleeSaveLocations */
    {

#if SINGULARITY_KERNEL
#if false
        [MixinOverride]
        internal void SetCalleeSaves(SpillContext *context) {
            r4.SetCalleeReg(&context->r4);
            r5.SetCalleeReg(&context->r5);
            r6.SetCalleeReg(&context->r6);
            r7.SetCalleeReg(&context->r7);
            r8.SetCalleeReg(&context->r8);
            r9.SetCalleeReg(&context->r9);
            r10.SetCalleeReg(&context->r10);
            r11.SetCalleeReg(&context->r11);
        }
#endif
#endif

        [MixinOverride]
        internal
        void SetCalleeSaves(CalleeSaveRegistersARM *calleeSaveRegisters)
        {
            r4.SetCalleeReg(&calleeSaveRegisters->r4);
            r5.SetCalleeReg(&calleeSaveRegisters->r5);
            r6.SetCalleeReg(&calleeSaveRegisters->r6);
            r7.SetCalleeReg(&calleeSaveRegisters->r7);
            r8.SetCalleeReg(&calleeSaveRegisters->r8);
            r9.SetCalleeReg(&calleeSaveRegisters->r9);
            r10.SetCalleeReg(&calleeSaveRegisters->r10);
            r11.SetCalleeReg(&calleeSaveRegisters->r11);
        }

        [MixinOverride]
        internal void ClearCalleeSaves() {
            r4.ClearCalleeReg();
            r5.ClearCalleeReg();
            r6.ClearCalleeReg();
            r7.ClearCalleeReg();
            r8.ClearCalleeReg();
            r9.ClearCalleeReg();
            r10.ClearCalleeReg();
            r11.ClearCalleeReg();
        }

        [MixinOverride]
        internal void ScanLiveRegs(UIntPtr mask,
                                   NonNullReferenceVisitor referenceVisitor)
        {
            r4.ScanLiveReg((mask >> 0) & 0x3, referenceVisitor);
            r5.ScanLiveReg((mask >> 2) & 0x3, referenceVisitor);
            r6.ScanLiveReg((mask >> 4) & 0x3, referenceVisitor);
            r7.ScanLiveReg((mask >> 6) & 0x3, referenceVisitor);
            r8.ScanLiveReg((mask >> 8) & 0x3, referenceVisitor);
            r9.ScanLiveReg((mask >> 10) & 0x3, referenceVisitor);
            r10.ScanLiveReg((mask >> 12) & 0x3, referenceVisitor);
            r11.ScanLiveReg((mask >> 14) & 0x3, referenceVisitor);
        }

        [MixinOverride]
        internal void PopFrame(UIntPtr *framePointer,
                               UIntPtr calleeSaveMask,
                               bool framePointerOmitted,
                               bool hasTransitionRecord)
        {
            UIntPtr *calleeSaveStart;
            calleeSaveStart = framePointer - 3;  // Step over SP & LR

            if (hasTransitionRecord) {
                calleeSaveStart -=
                    sizeof(CallStack.TransitionRecord) / sizeof(UIntPtr);
            }

            // Note: the order in which these appear is important!
            if (!framePointerOmitted || (calleeSaveMask & 0x80) != 0) {
                r11.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x40) != 0) {
                r10.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x20) != 0) {
                r9.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x10) != 0) {
                r8.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x8) != 0) {
                r7.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x4) != 0) {
                r6.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x2) != 0) {
                r5.PopFrameReg(ref calleeSaveStart);
            }
            if ((calleeSaveMask & 0x1) != 0) {
                r4.PopFrameReg(ref calleeSaveStart);
            }
        }

        [MixinOverride]
        internal void ClearFrame(UIntPtr calleeSaveMask,
                                 bool framePointerOmitted)
        {
            if (!framePointerOmitted) {
                VTable.Assert((calleeSaveMask & 0x100) == 0,
                              "EBP should not be callee saved");
                r11.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x1) != 0) {
                r4.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x2) != 0) {
                r5.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x4) != 0) {
                r6.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x8) != 0) {
                r7.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x10) != 0) {
                r8.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x20) != 0) {
                r9.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x40) != 0) {
                r10.ClearFrameReg();
            }
            if ((calleeSaveMask & 0x80) != 0) {
                r11.ClearFrameReg();
            }
        }

        [MixinOverride]
        internal UIntPtr GetFramePointer()
        {
            return r11.value;
        }

        CalleeSaveLocations.RegLocation r4;
        CalleeSaveLocations.RegLocation r5;
        CalleeSaveLocations.RegLocation r6;
        CalleeSaveLocations.RegLocation r7;
        CalleeSaveLocations.RegLocation r8;
        CalleeSaveLocations.RegLocation r9;
        CalleeSaveLocations.RegLocation r10;
        CalleeSaveLocations.RegLocation r11;

    }

}
