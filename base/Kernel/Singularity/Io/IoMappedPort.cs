///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoMappedPort.cs
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
    public sealed class IoMappedPort
    {
        private readonly UIntPtr address;
        private readonly uint size;
        private readonly bool readable;
        private readonly bool writable;

#if SINGULARITY_KERNEL
        public IoMappedPort(UIntPtr address, uint size, Access access)
#elif SINGULARITY_PROCESS
        internal IoMappedPort(UIntPtr address, uint size, Access access)
#endif // SINGULARITY_PROCESS
        {
            this.address = address;
            this.size = size;
            this.readable = (access & Access.Read) != 0;
            this.writable = (access & Access.Write) != 0;
        }

#if SINGULARITY_KERNEL
        public IoMappedPort(UIntPtr address, uint size, bool readable, bool writable)
#elif SINGULARITY_PROCESS
        internal IoMappedPort(UIntPtr address, uint size, bool readable, bool writable)
#endif // SINGULARITY_PROCESS
        {
            this.address = address;
            this.size = size;
            this.readable = readable;
            this.writable = writable;
        }

        public UIntPtr Address {
            [NoHeapAllocation]
            get { return address; }
        }

        public uint Length {
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
            return String.Format("IOMapped:{0,8:x8}[{1}]",
                                 address,
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
        public void Write64(ulong value)
        {
            Write64(0, value);
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

        [Inline]
        public ulong Read64()
        {
            return Read64(0);
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

        ///////////////////////////////////////////////////////////////////////
        //

        [Inline]
        public void Write8(uint offset, byte value)
        {
            CheckWrite(offset, 1);
            HalWrite8(offset, value);
        }

        [Inline]
        public void Write16(uint offset, ushort value)
        {
            CheckWrite(offset, 2);
            HalWrite16(offset, value);
        }

        [Inline]
        public void Write16(uint offset, ushort[] values)
        {
            CheckWrite(offset, 2);
            for (int i = 0; i < values.Length; i++) {
                HalWrite16(offset, values[i]);
            }
        }

        [Inline]
        public void Write32(uint offset, uint value)
        {
            CheckWrite(offset, 4);
            HalWrite32(offset, value);
        }

        [Inline]
        public void Write64(uint offset, ulong value)
        {
            CheckWrite(offset, 8);
            HalWrite64(offset, value);
        }

        [Inline]
        public byte Read8(uint offset)
        {
            CheckRead(offset, 1);
            return HalRead8(offset);
        }

        [Inline]
        public ushort Read16(uint offset)
        {
            CheckRead(offset, 2);
            return HalRead16(offset);
        }

        [Inline]
        public uint Read32(uint offset)
        {
            CheckRead(offset, 4);
            return HalRead32(offset);
        }

        [Inline]
        public ulong Read64(uint offset)
        {
            CheckRead(offset, 8);
            return HalRead64(offset);
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
        private IoResult CheckReadNoThrow(uint offset, int bytes)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                return IoResult.ReadNotSupported;
            }
            if (offset + bytes > size) {
                return IoResult.AccessOutOfRange;
            }
#endif // DONT_CHECK_IO_BOUNDS
            return IoResult.Success;
        }

        [Inline]
        [NoHeapAllocation]
        private IoResult CheckWriteNoThrow(uint offset, int bytes)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                return IoResult.WriteNotSupported;
            }
            if (offset + bytes > size) {
                return IoResult.AccessOutOfRange;
            }
#endif // DONT_CHECK_IO_BOUNDS
            return IoResult.Success;
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Read8NoThrow(uint offset, out byte value)
        {
            IoResult check = CheckReadNoThrow(offset, 1);
            if (IoResult.Success == check) {
                value = HalRead8(offset);
            }
            else {
                value = 0;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Read16NoThrow(uint offset, out ushort value)
        {
            IoResult check = CheckReadNoThrow(offset, 2);
            if (IoResult.Success == check) {
                value = HalRead16(offset);
            }
            else {
                value = 0;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Read32NoThrow(uint offset, out uint value)
        {
            IoResult check = CheckReadNoThrow(offset, 4);
            if (IoResult.Success == check) {
                value = HalRead32(offset);
            }
            else {
                value = 0;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Read64NoThrow(uint offset, out ulong value)
        {
            IoResult check = CheckReadNoThrow(offset, 8);
            if (IoResult.Success == check) {
                value = HalRead64(offset);
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
        public IoResult Write8NoThrow(uint offset, byte value)
        {
            IoResult check = CheckWriteNoThrow(offset, 1);
            if (IoResult.Success == check) {
                HalWrite8(offset, value);
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Write16NoThrow(uint offset, ushort value)
        {
            IoResult check = CheckWriteNoThrow(offset, 2);
            if (IoResult.Success == check) {
                HalWrite16(offset, value);
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Write32NoThrow(uint offset, uint value)
        {
            IoResult check = CheckWriteNoThrow(offset, 4);
            if (IoResult.Success == check) {
                HalWrite32(offset, value);
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public IoResult Write64NoThrow(uint offset, ulong value)
        {
            IoResult check = CheckWriteNoThrow(offset, 8);
            if (IoResult.Success == check) {
                HalWrite64(offset, value);
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

        [Inline]
        [NoHeapAllocation]
        public IoResult Write64NoThrow(ulong value)
        {
            return Write64NoThrow(0, value);
        }

        //////////////////////////////////////////////////////////////////////////////

        [Inline]
        [NoHeapAllocation]
        private bool CheckReadNoThrow(uint offset, int bytes, ref IoResult result)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                result = IoResult.ReadNotSupported;
                return false;
            }
            if (offset + bytes > size) {
                result = IoResult.AccessOutOfRange;
                return false;
            }
#endif // DONT_CHECK_IO_BOUNDS
            return true;
        }

        [Inline]
        [NoHeapAllocation]
        private bool CheckWriteNoThrow(uint offset, int bytes, ref IoResult result)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                result = IoResult.WriteNotSupported;
                return false;
            }
            if (offset + bytes > size) {
                result = IoResult.AccessOutOfRange;
                return false;
            }
#endif // DONT_CHECK_IO_BOUNDS
            return true;
        }

        [Inline]
        [NoHeapAllocation]
        public byte Read8NoThrow(uint offset, ref IoResult result)
        {
            if (CheckReadNoThrow(offset, 1, ref result)) {
                return HalRead8(offset);
            }
            else {
                return 0;
            }
        }

        [Inline]
        [NoHeapAllocation]
        public ushort Read16NoThrow(uint offset, ref IoResult result)
        {
            if (CheckReadNoThrow(offset, 2, ref result)) {
                return HalRead16(offset);
            }
            else {
                return 0;
            }
        }

        [Inline]
        [NoHeapAllocation]
        public uint Read32NoThrow(uint offset, ref IoResult result)
        {
            if (CheckReadNoThrow(offset, 4, ref result)) {
                return HalRead32(offset);
            }
            else {
                return 0;
            }
        }

        [Inline]
        [NoHeapAllocation]
        public ulong Read64NoThrow(uint offset, ref IoResult result)
        {
            if (CheckReadNoThrow(offset, 8, ref result)) {
                return HalRead64(offset);
            }
            else {
                return 0;
            }
        }

        [Inline]
        [NoHeapAllocation]
        public byte Read8NoThrow(ref IoResult result)
        {
            return Read8NoThrow(0, ref result);
        }

        [Inline]
        [NoHeapAllocation]
        public ushort Read16NoThrow(ref IoResult result)
        {
            return Read16NoThrow(0, ref result);
        }

        [Inline]
        [NoHeapAllocation]
        public uint Read32NoThrow(ref IoResult result)
        {
            return Read32NoThrow(0, ref result);
        }

        [Inline]
        [NoHeapAllocation]
        public ulong Read64NoThrow(ref IoResult result)
        {
            return Read64NoThrow(0, ref result);
        }

        [Inline]
        [NoHeapAllocation]
        public void Write8NoThrow(uint offset, byte value, ref IoResult result)
        {
            if (CheckWriteNoThrow(offset, 1, ref result)) {
                HalWrite8(offset, value);
            }
        }

        [Inline]
        [NoHeapAllocation]
        public void Write16NoThrow(uint offset, ushort value, ref IoResult result)
        {
            if (CheckWriteNoThrow(offset, 2, ref result)) {
                HalWrite16(offset, value);
            }
        }

        [Inline]
        [NoHeapAllocation]
        public void Write32NoThrow(uint offset, uint value, ref IoResult result)
        {
            if (CheckWriteNoThrow(offset, 4, ref result)) {
                HalWrite32(offset, value);
            }
        }

        [Inline]
        [NoHeapAllocation]
        public void Write64NoThrow(uint offset, ulong value, ref IoResult result)
        {
            if (CheckWriteNoThrow(offset, 8, ref result)) {
                HalWrite64(offset, value);
            }
        }

        [Inline]
        [NoHeapAllocation]
        public void Write8NoThrow(byte value, ref IoResult result)
        {
            Write8NoThrow(0, value, ref result);
        }

        [Inline]
        [NoHeapAllocation]
        public void Write16NoThrow(ushort value, ref IoResult result)
        {
            Write16NoThrow(0, value, ref result);
        }

        [Inline]
        [NoHeapAllocation]
        public void Write32NoThrow(uint value, ref IoResult result)
        {
            Write32NoThrow(0, value, ref result);
        }

        [Inline]
        [NoHeapAllocation]
        public void Write64NoThrow(ulong value, ref IoResult result)
        {
            Write64NoThrow(0, value, ref result);
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
                if (((value = HalRead8(0)) & mask) == 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalRead8(0);
        }

        public ushort WaitClear16(ushort mask)
        {
            CheckRead(0, 2);

            for (int i = 0; i < 100000000; i++) {
                ushort value;
                if (((value = HalRead16(0)) & mask) == 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalRead16(0);
        }

        public uint WaitClear32(uint mask)
        {
            CheckRead(0, 4);

            for (int i = 0; i < 100000000; i++) {
                uint value;
                if (((value = HalRead32(0)) & mask) == 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalRead32(0);
        }

        public ulong WaitClear64(ulong mask)
        {
            CheckRead(0, 8);

            for (int i = 0; i < 100000000; i++) {
                ulong value;
                if (((value = HalRead64(0)) & mask) == 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalRead64(0);
        }

        //////////////////////////////////////////////////////////////////////
        //

        public byte WaitSet8(byte mask)
        {
            CheckRead(0, 1);

            for (int i = 0; i < 100000000; i++) {
                byte value;
                if (((value = HalRead8(0)) & mask) != 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalRead8(0);
        }

        public ushort WaitSet16(ushort mask)
        {
            CheckRead(0, 2);

            for (int i = 0; i < 100000000; i++) {
                ushort value;
                if (((value = HalRead16(0)) & mask) != 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalRead16(0);
        }

        public uint WaitSet32(uint mask)
        {
            CheckRead(0, 4);

            for (int i = 0; i < 100000000; i++) {
                uint value;
                if (((value = HalRead32(0)) & mask) != 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalRead32(0);
        }

        public ulong WaitSet64(ulong mask)
        {
            CheckRead(0, 8);

            for (int i = 0; i < 100000000; i++) {
                ulong value;
                if (((value = HalRead64(0)) & mask) != 0) {
                    return value;
                }
            }

            DebugBreak();

            return HalRead64(0);
        }

        //////////////////////////////////////////////////////////////////////
        //
        [NoHeapAllocation]
        private unsafe byte HalRead8(uint offset)
        {
            return *((/*volatile*/ byte *)(address + offset));
        }

        [NoHeapAllocation]
        private unsafe void HalWrite8(uint offset, byte value)
        {
            *((/*volatile*/ byte *)(address + offset)) = value;
        }

        [NoHeapAllocation]
        private unsafe ushort HalRead16(uint offset)
        {
            return *((/*volatile*/ ushort *)(address + offset));
        }

        [NoHeapAllocation]
        private unsafe void HalWrite16(uint offset, ushort value)
        {
            *((/*volatile*/ ushort *)(address + offset)) = value;
        }

        [NoHeapAllocation]
        private unsafe uint HalRead32(uint offset)
        {
            return *((/*volatile*/ uint *)(address + offset));
        }

        [NoHeapAllocation]
        private unsafe void HalWrite32(uint offset, uint value)
        {
            *((/*volatile*/ uint *)(address + offset)) = value;
        }

        [NoHeapAllocation]
        private unsafe ulong HalRead64(uint offset)
        {
            return *((/*volatile*/ ulong *)(address + offset));
        }

        [NoHeapAllocation]
        private unsafe void HalWrite64(uint offset, ulong value)
        {
            *((/*volatile*/ ulong *)(address + offset)) = value;
        }
    }
}
