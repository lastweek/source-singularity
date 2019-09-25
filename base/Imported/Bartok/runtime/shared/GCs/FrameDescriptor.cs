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

    // This is the struct that we should use when traversing the stack.
    // It can be created from the encoded information in the stack
    // descriptor table.
    internal struct FrameDescriptor {

        internal const uint ESCAPE32_TAG = 0x0;
        internal const uint ESCAPE16_TAG = 0x1;
        internal const uint ESCAPE8_TAG  = 0x2;
        internal const uint COMPRESSED_MASK_TAG = 0x3;

        internal bool isFramePointerOmitted;
        internal bool hasTransitionRecord;
        internal bool hasPinnedVariables;
        internal uint argumentCount;
        internal uint argumentTag;
        internal UIntPtr argumentMaskOrTable;
        internal UIntPtr calleeSaveValueMask;
        internal UIntPtr calleeSaveMask;
        internal int frameSize;
        internal int inBetweenSlotsAbove;
        internal int inBetweenSlotsBelow;

        internal unsafe
        FrameDescriptor(CompressedFrameDescriptor smallDescriptor)
        {
            if (smallDescriptor.IsCompressed()) {
                this.argumentCount = smallDescriptor.StackArgSize();
                this.hasPinnedVariables = false;
                this.hasTransitionRecord =
                    smallDescriptor.HasTransitionRecord();
                if (smallDescriptor.IsFramePointerOmitted()) {
                    this.isFramePointerOmitted = true;
                    this.argumentTag = COMPRESSED_MASK_TAG;
                    this.argumentMaskOrTable =
                        smallDescriptor.ArgumentMaskNoFP();
                    this.calleeSaveValueMask =
                        smallDescriptor.CalleeSaveValueMaskNoFP();
                    this.calleeSaveMask = smallDescriptor.CalleeSaveMaskNoFP();
                    this.inBetweenSlotsAbove =
                        smallDescriptor.InBetweenSlotsAboveNoFP();
                    this.inBetweenSlotsBelow =
                        smallDescriptor.InBetweenSlotsBelowNoFP();
                    this.frameSize = smallDescriptor.FrameSizeNoFP();
                } else {
                    this.isFramePointerOmitted = false;
                    this.argumentTag = COMPRESSED_MASK_TAG;
                    this.argumentMaskOrTable =
                        smallDescriptor.ArgumentMaskWithFP();
                    this.calleeSaveValueMask =
                        smallDescriptor.CalleeSaveValueMaskWithFP();
                    this.calleeSaveMask =
                        smallDescriptor.CalleeSaveMaskWithFP();
                    this.inBetweenSlotsAbove =
                        smallDescriptor.InBetweenSlotsAboveWithFP();
                    this.inBetweenSlotsBelow =
                        smallDescriptor.InBetweenSlotsBelowWithFP();
                    this.frameSize = 0;
                }
            } else {
                this.argumentCount = 0;
                OverflowFrameDescriptor *overflow =
                    smallDescriptor.OverflowDescriptor();
                this.hasTransitionRecord =
                    smallDescriptor.HasTransitionRecord(overflow);
                if (smallDescriptor.IsFramePointerOmitted(overflow)) {
                    this.isFramePointerOmitted = true;
                    this.argumentTag =
                        smallDescriptor.EntrySizeNoFP(overflow);
                    this.argumentMaskOrTable = (UIntPtr)
                        (&overflow->variableData);
                    this.calleeSaveMask =
                        smallDescriptor.CalleeSaveMaskNoFP(overflow);
                    this.calleeSaveValueMask =
                        smallDescriptor.CalleeSaveValueMaskNoFP(overflow);
                    this.inBetweenSlotsAbove = 0;
                    this.inBetweenSlotsBelow = 0;
                    this.frameSize =
                        smallDescriptor.FrameSizeNoFP(overflow);
                    this.hasPinnedVariables =
                        smallDescriptor.HasPinnedPointersNoFP(overflow);
                } else {
                    this.isFramePointerOmitted = false;
                    this.argumentTag =
                        smallDescriptor.EntrySizeWithFP(overflow);
                    this.argumentMaskOrTable = (UIntPtr)
                        (&overflow->variableData);
                    this.calleeSaveMask =
                        smallDescriptor.CalleeSaveMaskWithFP(overflow);
                    this.calleeSaveValueMask =
                        smallDescriptor.CalleeSaveValueMaskWithFP(overflow);
                    this.inBetweenSlotsAbove = 0;
                    this.inBetweenSlotsBelow = 0;
                    this.frameSize = 0;
                    this.hasPinnedVariables =
                        smallDescriptor.HasPinnedPointersWithFP(overflow);
                }
            }
        }

    }

    internal struct CompressedFrameDescriptorTemplate {

        internal bool IsCompressed() { return true; }
        internal bool IsFramePointerOmitted() { return true; }
        internal bool HasTransitionRecord() { return true; }
        internal uint StackArgSize() { return 0;}
        internal UIntPtr ArgumentMaskNoFP() { return UIntPtr.Zero;}
        internal UIntPtr CalleeSaveValueMaskNoFP() { return UIntPtr.Zero; }
        internal UIntPtr CalleeSaveMaskNoFP() { return UIntPtr.Zero;}
        internal int FrameSizeNoFP() { return 0; }
        internal int InBetweenSlotsAboveNoFP() { return 0; }
        internal int InBetweenSlotsBelowNoFP() { return 0; }
        internal UIntPtr ArgumentMaskWithFP() { return UIntPtr.Zero; }
        internal UIntPtr CalleeSaveValueMaskWithFP() { return UIntPtr.Zero; }
        internal UIntPtr CalleeSaveMaskWithFP() { return UIntPtr.Zero; }
        internal int InBetweenSlotsAboveWithFP() { return 0; }
        internal int InBetweenSlotsBelowWithFP() { return 0; }
        internal unsafe OverflowFrameDescriptor *OverflowDescriptor() { return null; }
        internal unsafe bool IsFramePointerOmitted(OverflowFrameDescriptor *overflow) { return true; }
        internal unsafe bool HasTransitionRecord(OverflowFrameDescriptor *overflow) { return true; }
        internal unsafe UIntPtr CalleeSaveValueMaskNoFP(OverflowFrameDescriptor *overflow) { return UIntPtr.Zero; }
        internal unsafe UIntPtr CalleeSaveMaskNoFP(OverflowFrameDescriptor *overflow) { return UIntPtr.Zero; }
        internal unsafe bool HasPinnedPointersNoFP(OverflowFrameDescriptor *overflow) { return true; }
        internal unsafe int FrameSizeNoFP(OverflowFrameDescriptor *overflow) { return 0; }
        internal unsafe uint EntrySizeNoFP(OverflowFrameDescriptor *overflow) { return 0; }
        internal unsafe UIntPtr CalleeSaveValueMaskWithFP(OverflowFrameDescriptor *overflow) { return UIntPtr.Zero; }
        internal unsafe UIntPtr CalleeSaveMaskWithFP(OverflowFrameDescriptor *overflow) { return UIntPtr.Zero; }
        internal unsafe bool HasPinnedPointersWithFP(OverflowFrameDescriptor *overflow) { return true; }
        internal unsafe uint EntrySizeWithFP(OverflowFrameDescriptor *overflow) { return 0; }
        internal unsafe void ExpandDescriptor(OverflowFrameDescriptor *overflow, ref FrameDescriptor res) {}
    }
}
