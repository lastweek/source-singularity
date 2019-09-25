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

// ISA_ is the prefix used by Singularity for the system architecture
#if AMD64 || ISA_IX64
    internal struct CompressedFrameDescriptor /* : CompressedFrameDescriptorTemplate */
    {
        private UIntPtr descriptorMask;

        internal bool IsCompressed()
        {
            return ((this.descriptorMask & (UIntPtr) 0x1) != 0);
        }

        internal bool IsFramePointerOmitted()
        {
            return ((this.descriptorMask & (UIntPtr) 0x2) != 0);
        }

        internal bool HasTransitionRecord()
        {
            return ((this.descriptorMask & (UIntPtr) 0x40) != 0);
        }

        internal uint StackArgSize()
        {
            return ((this.descriptorMask >> 2) & 0xf);
        }

        internal UIntPtr ArgumentMaskNoFP()
        {
            return (this.descriptorMask >> 36);
        }

        internal UIntPtr CalleeSaveValueMaskNoFP()
        {
            return ((this.descriptorMask >> 15) & (UIntPtr) 0xffff);
        }

        internal UIntPtr CalleeSaveMaskNoFP()
        {
            return ((this.descriptorMask >> 7) & (UIntPtr) 0xff);
        }

        internal int FrameSizeNoFP()
        {
            return unchecked((int) ((this.descriptorMask >> 31) & 0x1f));
        }

        internal int InBetweenSlotsAboveNoFP()
        {
            return 1;
        }

        internal int InBetweenSlotsBelowNoFP()
        {
            return 0;
        }

        internal UIntPtr ArgumentMaskWithFP()
        {
            return (this.descriptorMask >> 28);
        }

        internal UIntPtr CalleeSaveValueMaskWithFP()
        {
            return ((this.descriptorMask >> 14) & (UIntPtr) 0x3fff);
        }

        internal UIntPtr CalleeSaveMaskWithFP()
        {
            return ((this.descriptorMask >> 7) & (UIntPtr) 0x7f);
        }

        internal int InBetweenSlotsAboveWithFP()
        {
            return 2;
        }

        internal int InBetweenSlotsBelowWithFP()
        {
            return 0;
        }

        internal unsafe OverflowFrameDescriptor *OverflowDescriptor()
        {
            return (OverflowFrameDescriptor *) this.descriptorMask;
        }

        internal unsafe
        bool IsFramePointerOmitted(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask & (UIntPtr) 0x1) != 0);
        }

        internal unsafe
        bool HasTransitionRecord(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask & (UIntPtr) 0x2) != 0);
        }

        internal unsafe
        UIntPtr CalleeSaveValueMaskNoFP(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask >> 10) & (UIntPtr) 0xffff);
        }

        internal unsafe
        UIntPtr CalleeSaveMaskNoFP(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask >> 2) & (UIntPtr) 0xff);
        }

        internal unsafe
        bool HasPinnedPointersNoFP(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask & (UIntPtr) 0x20000000) != 0);
        }

        internal unsafe int FrameSizeNoFP(OverflowFrameDescriptor *overflow)
        {
            return unchecked((int) (overflow->mask >> 38));
        }

        internal unsafe uint EntrySizeNoFP(OverflowFrameDescriptor *overflow)
        {
            return unchecked((uint) ((overflow->mask >> 26) & (UIntPtr) 0x7));
        }

        internal unsafe
        UIntPtr CalleeSaveValueMaskWithFP(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask >> 9) & (UIntPtr) 0x3fff);
        }

        internal unsafe
        UIntPtr CalleeSaveMaskWithFP(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask >> 2) & (UIntPtr) 0x7f);
        }

        internal unsafe
        bool HasPinnedPointersWithFP(OverflowFrameDescriptor *overflow)
        {
            return ((overflow->mask & (UIntPtr) 0x08000000) != 0);
        }

        internal unsafe uint EntrySizeWithFP(OverflowFrameDescriptor *overflow)
        {
            return unchecked((uint) ((overflow->mask >> 23) & (UIntPtr) 0x7));
        }

    }

    [StructLayout(LayoutKind.Sequential)]
    internal struct OverflowFrameDescriptor {
        internal UIntPtr mask;
        internal int variableData;
    }

#endif

}
