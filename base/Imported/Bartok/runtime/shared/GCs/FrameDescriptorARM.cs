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

    using System.Runtime.InteropServices;
    using Microsoft.Bartok.Runtime;

// ISA_ is the prefix used by Singularity for the system architecture
#if ARM || ISA_ARM
    [StructLayout(LayoutKind.Sequential)]
    internal struct CompressedFrameDescriptor /* : CompressedFrameDescriptorTemplate */
    {
        private UIntPtr mask;

        internal bool IsCompressed()
        {
            return ((this.mask & (UIntPtr) Constants.CompactMask) != 0);
        }

        internal bool IsFramePointerOmitted()
        {
            return ((this.mask & (UIntPtr) Constants.CompactOmitFPMask) != 0);
        }

        internal bool HasTransitionRecord()
        {
            return ((this.mask & (UIntPtr) Constants.CompactTransitionRecordMask) != 0);
        }

        internal uint StackArgSize()
        {
            return ((this.mask >> Constants.CompactArgMaskStart) & Constants.CompactArgMask);
        }

        internal UIntPtr ArgumentMaskNoFP()
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return (this.mask >> 5);
        }

        internal UIntPtr CalleeSaveValueMaskNoFP()
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return ((this.mask >> Constants.CompactCalleeSaveUseStartNoFP) & (UIntPtr) Constants.CompactCalleeSaveUseMaskNoFP);
        }

        internal UIntPtr CalleeSaveMaskNoFP()
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return ((this.mask >> 8) & (UIntPtr) 0xff);
        }

        internal int FrameSizeNoFP()
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return unchecked((int) (this.mask & 0x1f));
        }

        internal int InBetweenSlotsAboveNoFP()
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return Constants.InbetweenSlotsAboveNoFP;
        }

        internal int InBetweenSlotsBelowNoFP()
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return Constants.InbetweenSlotsBelowNoFP;
        }

        internal UIntPtr ArgumentMaskWithFP()
        {
            return (this.mask >> Constants.CompactStackBitMaskStartFP);
        }

        internal UIntPtr CalleeSaveValueMaskWithFP()
        {
            return ((this.mask >> Constants.CompactCalleeSaveUseStartFP) & (UIntPtr) Constants.CompactCalleeSaveUseMaskFP);
        }

        internal UIntPtr CalleeSaveMaskWithFP()
        {
            return ((this.mask >> Constants.CompactCalleeSaveStartFP) & (UIntPtr) Constants.CompactCalleeSaveMaskFP);
        }

        internal int InBetweenSlotsAboveWithFP()
        {
            return Constants.InbetweenSlotsAboveFP;
        }

        internal int InBetweenSlotsBelowWithFP()
        {
            return Constants.InbetweenSlotsBelowFP;
        }

        internal unsafe OverflowFrameDescriptor *OverflowDescriptor()
        {
            return (OverflowFrameDescriptor *) this.mask;
        }

        internal unsafe
        bool IsFramePointerOmitted(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask & (UIntPtr) Constants.FullOmitFPMask) != 0);
        }

        internal unsafe
        bool HasTransitionRecord(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask & (UIntPtr) Constants.FullTransitionRecordMask) != 0);
        }

        internal unsafe
        UIntPtr CalleeSaveValueMaskNoFP(OverflowFrameDescriptor *overflow)
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return this.CalleeSaveValueMaskNoFP();
        }

        internal unsafe
        UIntPtr CalleeSaveMaskNoFP(OverflowFrameDescriptor *overflow)
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return this.CalleeSaveMaskNoFP();
        }

        internal unsafe
        bool HasPinnedPointersNoFP(OverflowFrameDescriptor *overflow)
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return ((overflow->mask & (UIntPtr) 0x1) != 0);
        }

        internal unsafe int FrameSizeNoFP(OverflowFrameDescriptor *overflow)
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return unchecked((int) (overflow->mask >> 4));
        }

        internal unsafe uint EntrySizeNoFP(OverflowFrameDescriptor *overflow)
        {
            // Current bridge doesn't support omitting frame pointer.
            VTable.Assert(false, "Omit FP not supported.");
            return unchecked((uint) ((overflow->mask >> 1) & (UIntPtr) 0x7));
        }

        internal unsafe
        UIntPtr CalleeSaveValueMaskWithFP(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask >> Constants.FullCalleeSaveUseStartFP) & (UIntPtr) Constants.FullCalleeSaveUseMaskFP);
        }

        internal unsafe
        UIntPtr CalleeSaveMaskWithFP(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask >> Constants.FullCalleeSaveStartFP) & (UIntPtr) Constants.FullCalleeSaveMaskFP);
        }

        internal unsafe
        bool HasPinnedPointersWithFP(OverflowFrameDescriptor *overflow)
        {
            return (((overflow->mask >> Constants.FullPinnedPosFP) & (UIntPtr) 0x1) != 0);
        }

        internal unsafe uint EntrySizeWithFP(OverflowFrameDescriptor *overflow)
        {
            return unchecked((uint) ((overflow->mask >> Constants.FullRecordSizePosFP) & (UIntPtr) Constants.FullRecordMask));
        }

        internal static unsafe UIntPtr NextCallSite(bool omitFP, UIntPtr *fp, out UIntPtr *sp)
        {
            if (omitFP) {
                VTable.Assert(false, "ARM doesn't support FPO");
                sp = (UIntPtr*)UIntPtr.Zero;
            } else {
                sp = (UIntPtr*)*(fp - 2);
                return *(fp - 1);
            }
            return UIntPtr.Zero;
        }
    }

    [StructLayout(LayoutKind.Sequential)]
    internal struct OverflowFrameDescriptor {
        internal UIntPtr mask;
        internal int variableData;
    }  
#endif

}
