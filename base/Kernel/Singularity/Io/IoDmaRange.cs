///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoDmaRange.cs
//

using System;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public sealed class IoDmaRange : IoRange
    {
        private readonly int dma;
        private readonly int size;

#if SINGULARITY_KERNEL
        public IoDmaRange(int channel, int size)
#elif SINGULARITY_PROCESS
        internal IoDmaRange(int channel, int size)
#endif // SINGULARITY_PROCESS
        {
            this.dma = channel;
            this.size = size;
        }

        public IoDma DmaAtOffset(int offset)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (offset + 1 > size) {
                throw new OverflowException("DmaAtOffset out of range.");
            }
#endif
            return new IoDma((byte)(dma + offset));
        }

        public byte Channel {
            get { return (byte)dma; }
        }

        public byte Size {
            get { return (byte)size; }
        }

        public override string ToString()
        {
            return String.Format("DMA:{0:x2}[{1:x}]", dma, size);
        }

#if SINGULARITY_KERNEL
        public override uint RangeBase {
            get { return (uint)dma; }
        }

        public override uint RangeLength {
            get { return (uint)size; }
        }
#endif
    }
}
