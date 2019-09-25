///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoPort.cs
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

#if SINGULARITY_PROCESS
using Microsoft.Singularity.V1.Services;
#endif

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in IoPort.cpp")]
    public sealed class IoPort
    {
        private readonly ushort port;
        private readonly ushort size;
        private readonly bool readable;
        private readonly bool writable;

#if SINGULARITY_KERNEL
        public IoPort(ushort port, ushort size, Access access)
#elif SINGULARITY_PROCESS
        internal IoPort(ushort port, ushort size, Access access)
#endif // SINGULARITY_PROCESS
        {
            this.port = port;
            this.size = size;
            this.readable = (access & Access.Read) != 0;
            this.writable = (access & Access.Write) != 0;
        }

#if SINGULARITY_KERNEL
        public IoPort(ushort port, ushort size, bool readable, bool writable)
#elif SINGULARITY_PROCESS
        internal IoPort(ushort port, ushort size, bool readable, bool writable)
#endif // SINGULARITY_PROCESS
        {
            this.port = port;
            this.size = size;
            this.readable = readable;
            this.writable = writable;
        }

        public ushort Port {
            [NoHeapAllocation]
            get { return port; }
        }

        public ushort Size {
            [NoHeapAllocation]
            get { return size; }
        }

        public bool Readable {
            [NoHeapAllocation]
            get { return readable; }
        }

        public bool Writable {
            [NoHeapAllocation]
            get { return writable; }
        }

        public override string ToString()
        {
            return String.Format("IO:{0,4:x4}[{1}]",
                                 port,
                                 (readable && writable) ? "R/W" :
                                 (readable) ? "R" : "W");
        }

        [Inline]
        public void Write8(byte value)
        {
            Write8(0, value);
        }

        [Inline]
        public void Write16(ushort value)
        {
            Write16(0, value);
        }

        [Inline]
        public void Write16(ushort[] values)
        {
            Write16(0, values);
        }

        [Inline]
        public void Write32(uint value)
        {
            Write32(0, value);
        }

        [Inline]
        public byte Read8()
        {
            return Read8(0);
        }

        [Inline]
        public ushort Read16()
        {
            return Read16(0);
        }

        [Inline]
        public uint Read32()
        {
            return Read32(0);
        }

        ///////////////////////////////////////////////////////////////////////
        //

        [Inline]
        private void CheckRead(uint offset, uint bytes)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            else if (offset + bytes > size) {
                Error.AccessOutOfRange();
            }
#endif // DONT_CHECK_IO_BOUNDS
        }

        [Inline]
        private void CheckWrite(uint offset, uint bytes)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            else if (offset + bytes > size) {
                Error.AccessOutOfRange();
            }
#endif // DONT_CHECK_IO_BOUNDS
        }

        [Inline]
        [NoHeapAllocation]
        private void DebugBreak()
        {
#if SINGULARITY_KERNEL
            DebugStub.Break();
#elif SINGULARITY_PROCESS
            DebugService.Break();
#endif // SINGULARITY_PROCESS
        }

        ///////////////////////////////////////////////////////////////////////
        //

        [Inline]
        public void Write8(uint offset, byte value)
        {
            CheckWrite(offset, 1);
            HalWriteInt8(port + offset, value);
        }

        [Inline]
        public void Write16(uint offset, ushort value)
        {
            CheckWrite(offset, 2);
            HalWriteInt16(port + offset, value);
        }

        [Inline]
        public void Write16(uint offset, ushort[] values)
        {
            CheckWrite(offset, 2);
            for (int i = 0; i < values.Length; i++) {
                HalWriteInt16(port + offset, values[i]);
            }
        }

        [Inline]
        public void Write32(uint offset, uint value)
        {
            CheckWrite(offset, 4);
            HalWriteInt32(port + offset, value);
        }

        [Inline]
        public byte Read8(uint offset)
        {
            CheckRead(offset, 1);
            return HalReadInt8(port + offset);
        }

        [Inline]
        public ushort Read16(uint offset)
        {
            CheckRead(offset, 2);
            return HalReadInt16(port + offset);
        }

        [Inline]
        public uint Read32(uint offset)
        {
            CheckRead(offset, 4);
            return HalReadInt32(port + offset);
        }

        ///////////////////////////////////////////////////////////////////////
        // Export non-exception throwing operations
        //
        // These are intended for use in the kernel on
        // NoHeapAllocation paths.  The caller is expected to
        // check the result and/or know pre-conditions for the
        // I/O operation.

#region NoHeapAllocation Read/Write operations
#if SINGULARITY_KERNEL
        [Inline]
        [NoHeapAllocation]
        private unsafe IoResult CheckReadNoThrow(uint offset, int bytes)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!this.readable) {
                return IoResult.ReadNotSupported;
            }
            if (offset + bytes > this.size) {
                return IoResult.AccessOutOfRange;
            }
#endif // DONT_CHECK_IO_BOUNDS
            return IoResult.Success;
        }

        [Inline]
        [NoHeapAllocation]
        private unsafe IoResult CheckWriteNoThrow(uint offset, int bytes)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!this.writable) {
                return IoResult.WriteNotSupported;
            }
            if (offset + bytes > this.size) {
                return IoResult.AccessOutOfRange;
            }
#endif // DONT_CHECK_IO_BOUNDS
            return IoResult.Success;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Read8NoThrow(uint offset, out byte value)
        {
            IoResult check = CheckReadNoThrow(offset, 1);
            if (IoResult.Success == check) {
                value = HalReadInt8(port + offset);
            }
            else {
                value = 0;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Read16NoThrow(uint offset, out ushort value)
        {
            IoResult check = CheckReadNoThrow(offset, 2);
            if (IoResult.Success == check) {
                value = HalReadInt16(port + offset);
            }
            else {
                value = 0;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Read32NoThrow(uint offset, out uint value)
        {
            IoResult check = CheckReadNoThrow(offset, 4);
            if (IoResult.Success == check) {
                value = HalReadInt32(port + offset);
            }
            else {
                value = 0;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Read8NoThrow(out byte value)
        {
            return Read8NoThrow(0, out value);
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Read16NoThrow(out ushort value)
        {
            return Read16NoThrow(0, out value);
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Read32NoThrow(out uint value)
        {
            return Read32NoThrow(0, out value);
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write8NoThrow(uint offset, byte value)
        {
            IoResult check = CheckWriteNoThrow(offset, 1);
            if (IoResult.Success == check) {
                HalWriteInt8(port + offset, value);
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write16NoThrow(uint offset, ushort value)
        {
            IoResult check = CheckWriteNoThrow(offset, 2);
            if (IoResult.Success == check) {
                HalWriteInt16(port + offset, value);
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write32NoThrow(uint offset, uint value)
        {
            IoResult check = CheckWriteNoThrow(offset, 4);
            if (IoResult.Success == check) {
                HalWriteInt32(port + offset, value);
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Write8NoThrow(byte value)
        {
            return Write8NoThrow(0, value);
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Write16NoThrow(ushort value)
        {
            return Write16NoThrow(0, value);
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Write32NoThrow(uint value)
        {
            return Write32NoThrow(0, value);
        }

#endif // SINGULARITY_KERNEL
#endregion // NoHeapAllocation Read/Write operations

        //////////////////////////////////////////////////////////////////////
        //

        public byte WaitClear8(byte mask)
        {
            CheckRead(0, 1);

            for (int i = 0; i < 100000000; i++) {
                byte value;
                if (((value = HalReadInt8(port)) & mask) == 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalReadInt8(port);
        }

        public ushort WaitClear16(ushort mask)
        {
            CheckRead(0, 2);

            for (int i = 0; i < 100000000; i++) {
                ushort value;
                if (((value = HalReadInt16(port)) & mask) == 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalReadInt16(port);
        }

        public uint WaitClear32(uint mask)
        {
            CheckRead(0, 4);

            for (int i = 0; i < 100000000; i++) {
                uint value;
                if (((value = HalReadInt32(port)) & mask) == 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalReadInt32(port);
        }

        //////////////////////////////////////////////////////////////////////
        //

        public byte WaitSet8(byte mask)
        {
            CheckRead(0, 1);

            for (int i = 0; i < 100000000; i++) {
                byte value;
                if (((value = HalReadInt8(port)) & mask) != 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalReadInt8(port);
        }

        public ushort WaitSet16(ushort mask)
        {
            CheckRead(0, 2);

            for (int i = 0; i < 100000000; i++) {
                ushort value;
                if (((value = HalReadInt16(port)) & mask) != 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalReadInt16(port);
        }

        public uint WaitSet32(uint mask)
        {
            CheckRead(0, 4);

            for (int i = 0; i < 100000000; i++) {
                uint value;
                if (((value = HalReadInt32(port)) & mask) != 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalReadInt32(port);
        }

        [AccessedByRuntime("output to header : defined in IoPort.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(12)]
        [NoHeapAllocation]
        private static extern byte HalReadInt8(uint port);

        [AccessedByRuntime("output to header : defined in IoPort.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(12)]
        [NoHeapAllocation]
        private static extern void HalWriteInt8(uint port, byte value);

        [AccessedByRuntime("output to header : defined in IoPort.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(12)]
        [NoHeapAllocation]
        private static extern ushort HalReadInt16(uint port);

        [AccessedByRuntime("output to header : defined in IoPort.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(12)]
        [NoHeapAllocation]
        private static extern void HalWriteInt16(uint port, ushort value);

        [AccessedByRuntime("output to header : defined in IoPort.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(12)]
        [NoHeapAllocation]
        private static extern uint HalReadInt32(uint port);

        [AccessedByRuntime("output to header : defined in IoPort.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(12)]
        [NoHeapAllocation]
        private static extern void HalWriteInt32(uint port, uint value);

#if DO_UNSAFE_CODE_IN_IO
        [AccessedByRuntime("output to header : defined in IoPort.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [NoHeapAllocation]
        private static extern unsafe void HalReadFifo16(uint port,
                                                        [In] ushort *data,
                                                        uint count);

        [AccessedByRuntime("output to header : defined in IoPort.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [NoHeapAllocation]
        private static extern unsafe void HalWriteFifo16(uint port,
                                                         [In,Out] ushort *data,
                                                         uint Count);
#endif
    }
}
