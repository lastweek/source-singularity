///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoPortRange.cs
//

using System;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public sealed class IoPortRange : IoRange
    {
        private readonly ushort port;
        private readonly ushort size;
        private readonly bool readable;
        private readonly bool writable;

#if SINGULARITY_KERNEL
        public IoPortRange(ushort port, ushort size, Access access)
#elif SINGULARITY_PROCESS
        internal IoPortRange(ushort port, ushort size, Access access)
#endif // SINGULARITY_PROCESS
        {
            this.port = port;
            this.size = size;
            this.readable = (access & Access.Read) != 0;
            this.writable = (access & Access.Write) != 0;
        }

#if SINGULARITY_KERNEL
        public IoPortRange(ushort port, ushort size, bool readable, bool writable)
#elif SINGULARITY_PROCESS
        internal IoPortRange(ushort port, ushort size, bool readable, bool writable)
#endif // SINGULARITY_PROCESS
        {
            this.port = port;
            this.size = size;
            this.readable = readable;
            this.writable = writable;
        }

        public IoPortRange RangeAtOffset(ushort offset, ushort bytes,
                                         bool readable, bool writeable)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (offset + bytes > size) {
                throw new OverflowException("PortAtOffset out of range.");
            }
            if ((readable && !this.readable) || (writable && !this.writable)) {
                throw new OverflowException("PortAtOffset invalid access");
            }
#endif
            return new IoPortRange((ushort)(port + offset), bytes, readable, writable);
        }

        public IoPort PortAtOffset(ushort offset, ushort bytes, Access access)
        {
            return PortAtOffset(offset,
                                bytes,
                                (access & Access.Read) != 0,
                                (access & Access.Write) != 0);
        }

        public IoPort PortAtOffset(ushort offset, ushort bytes, bool readable, bool writable)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (offset + bytes > size) {
                throw new OverflowException("PortAtOffset out of range.");
            }
            if ((readable && !this.readable) || (writable && !this.writable)) {
                throw new OverflowException("PortAtOffset invalid access");
            }
#endif
            return new IoPort((ushort)(port + offset), bytes, readable, writable);
        }

        public ushort Port
        {
            get { return port; }
        }

        public ushort Size
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

        public override string ToString()
        {
            return String.Format("IO:{0,4:x4}[{1:x}]{2}{3}", port, size,
                                 readable ? "r" : "", writable ? "w" : "");
        }

#if SINGULARITY_KERNEL
        public override uint RangeBase {
            get { return (uint)port; }
        }

        public override uint RangeLength {
            get { return (uint)size; }
        }
#endif
    }
}
