///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoMemoryRange.cs
//

using System;
using System.Threading;
using Microsoft.Singularity.Memory;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public sealed class IoMemoryRange : IoRange
    {
        private readonly UIntPtr addr; // PHYSICAL address
        private readonly UIntPtr size;
        private readonly bool readable;
        private readonly bool writable;

#if SINGULARITY_KERNEL
        public IoMemoryRange(UIntPtr addr, UIntPtr size, Access access)
#elif SINGULARITY_PROCESS
        internal IoMemoryRange(UIntPtr addr, UIntPtr size, Access access)
#endif // SINGULARITY_PROCESS
        {
            this.addr = addr;
            this.size = size;
            this.readable = (access & Access.Read) != 0;
            this.writable = (access & Access.Write) != 0;
        }

#if SINGULARITY_KERNEL
        public IoMemoryRange(UIntPtr addr, UIntPtr size, bool readable, bool writable)
#elif SINGULARITY_PROCESS
        internal IoMemoryRange(UIntPtr addr, UIntPtr size, bool readable, bool writable)
#endif // SINGULARITY_PROCESS
        {
            this.addr = addr;
            this.size = size;
            this.readable = readable;
            this.writable = writable;
        }

        public IoMemory MemoryAtOffset(uint offset, int bytes, Access access)
        {
            return MemoryAtOffset((UIntPtr)offset, bytes, access);
        }

        public IoMemory MemoryAtOffset(UIntPtr offset, int bytes, Access access)
        {
            return MemoryAtOffset(offset, bytes,
                                  (access & Access.Read) != 0,
                                  (access & Access.Write) != 0);
        }

        public IoMemory MemoryAtOffset(UIntPtr offset, int bytes, bool readable, bool writable)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (bytes < 0 || offset + bytes > size) {
                throw new OverflowException("MemoryAtOffset out of range.");
            }
            if ((readable && !this.readable) || (writable && !this.writable)) {
                throw new OverflowException("MemoryAtOffset invalid access");
            }
#endif
            return IoMemory.MapPhysicalMemory(addr + offset, (uint)bytes,
                                              readable, writable);
        }

        public override string ToString()
        {
            return String.Format("32:{0,8:x8}[{1:x}]{2}{3}", (uint)addr, (uint)size,
                                 readable ? "r" : "", writable ? "w" : "");
        }

#if SINGULARITY_KERNEL
        // The returned address is the PHYSICAL address and is most
        // likely not usable without constructing an IoMemory object.
        public PhysicalAddress PhysicalAddress
        {
            get { return new PhysicalAddress((ulong)addr); }
        }
#endif

        public UIntPtr Length
        {
            get { return size; }
        }

        public bool Readable
        {
            get { return readable; }
        }

        public bool Writable
        {
            get { return writable; }
        }


#if SINGULARITY_KERNEL
        public override uint RangeBase {
            get { return (uint)addr; }
        }

        public override uint RangeLength {
            get { return (uint)size; }
        }
#endif
    }
}
