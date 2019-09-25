///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoIrqRange.cs
//

using System;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public sealed class IoIrqRange : IoRange
    {
        private readonly byte irq;
        private readonly byte size;

#if SINGULARITY_KERNEL
        public IoIrqRange(byte line, byte size)
#elif SINGULARITY_PROCESS
        public IoIrqRange(byte line, byte size)
#endif // SINGULARITY_PROCESS
        {
            this.irq = line;
            this.size = size;
        }

        public IoIrq IrqAtOffset(byte offset)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (offset + 1 > size) {
                throw new OverflowException("IrqAtOffset out of range.");
            }
#endif
            return new IoIrq((byte)(irq + offset));
        }

        public byte Irq
        {
            get { return irq; }
        }

        public byte Line
        {
            get { return irq; }
        }

        public byte Size
        {
            get { return size; }
        }

        public override string ToString()
        {
            return String.Format("IRQ:{0:x2}[{1:x}]", irq, size);
        }

#if SINGULARITY_KERNEL
        public override uint RangeBase {
            get { return (uint)irq; }
        }

        public override uint RangeLength {
            get { return (uint)size; }
        }
#endif
    }
}
