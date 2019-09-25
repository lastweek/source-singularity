///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoMemory.cs
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using Microsoft.Singularity.Memory;

#if SINGULARITY_KERNEL
using Microsoft.Singularity.Hal;
#endif

#if SINGULARITY_PROCESS
using Microsoft.Singularity.V1.Services;
using System.Diagnostics;
#endif // SINGULARITY_PROCESS

using PageType = System.GCs.PageType;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public sealed class IoMemory
    {
        private enum MemoryType {
            RegularPages,  // We refer to memory allocated from general-purpose memory
            IOMemory,      // We refer to a block allocated from the IOMemory pool
            VirtWrapper,   // We wrap a range of virtual addresses that we didn't alloc
            PhysMapped,    // We wrap a range of physical addresses that we mapped
            PhysWrapper,   // We wrap a range of physical addresses that we didn't map
        }

        private readonly PhysicalAddress  dataPhys;
        private readonly unsafe byte *    data;
        private readonly int              bytes;
        private readonly MemoryType       type;
        private bool                      readable;
        private bool                      writable;

        //////////////////////////////////////////////////////////////////////////////
        //
#if SINGULARITY_PROCESS
        internal const byte   PageBits = 12;
        internal const uint   PageSize = 1 << PageBits;
        internal const uint   PageMask = PageSize - 1;

        [Inline]
        internal static UIntPtr PagePad(UIntPtr addr) {
            return ((addr + PageMask) & ~PageMask);
        }
#endif

        // Request a mapping to physical memory
        static public IoMemory MapPhysicalMemory(UIntPtr physAddr,
                                                 UIntPtr bytes,
                                                 bool readable,
                                                 bool writable)
        {
            DebugStub.Assert(physAddr != UIntPtr.Zero);

#if SINGULARITY_KERNEL
            UIntPtr virtAddr = MemoryManager.KernelMapPhysicalMemory(
                new PhysicalAddress((ulong)physAddr), bytes);
            DebugStub.Assert(virtAddr != UIntPtr.Zero);
            return new IoMemory(MemoryType.PhysMapped, new PhysicalAddress(physAddr),
                                virtAddr, (int)bytes, readable, writable);
#elif SINGULARITY_PROCESS
            UIntPtr virtAddr = DeviceService.MapPhysicalRange((ulong)physAddr, (uint)bytes,
                                                              readable, writable);
            DebugStub.Assert(virtAddr != UIntPtr.Zero);
            return new IoMemory(MemoryType.PhysMapped, new PhysicalAddress(physAddr),
                                virtAddr, (int)bytes, readable, writable);
#endif
        }

#if SINGULARITY_KERNEL
        // Kernel-only: just wrap a range of memory in an IoMemory for convenience
        //
        static public IoMemory Wrap(UIntPtr virtAddr, UIntPtr bytes,
                                    bool readable, bool writable)
        {
            return new IoMemory(MemoryType.VirtWrapper, virtAddr,
                                (int)bytes, readable, writable);
        }

        //
        // Kernel-only: Allocate fixed memory from the user range
        //
        static internal IoMemory AllocateUserFixed(UIntPtr bytes, Process process,
                                                   PageType type)
        {
            bytes = MemoryManager.PagePad(bytes);
            UIntPtr pages = MemoryManager.PagesFromBytes(bytes);
            UIntPtr addr = MemoryManager.UserAllocate(pages, process, 0, type);

            if (addr == UIntPtr.Zero) {
                return null;
            }

            return new IoMemory(MemoryType.RegularPages, addr, (int)bytes, true, true);
        }
#endif

        //
        // Allocate virtually but not physically contiguous pages. The resulting
        // IoMemory object grants access to a number of bytes rounded up to
        // the nearest page boundary.
        //
        static public IoMemory AllocateFixed(UIntPtr bytes)
        {
#if SINGULARITY_KERNEL
            return AllocateFixed(bytes, Thread.CurrentProcess, PageType.NonGC);
#elif SINGULARITY_PROCESS
            int mybytes = (int)bytes;
            bytes = PagePad(bytes);

            UIntPtr addr = (UIntPtr)PageTableService.Allocate((uint)bytes);

            if (addr == UIntPtr.Zero) {
                return null;
            }

            return new IoMemory(MemoryType.RegularPages, addr, (int)bytes, true, true);
#endif // SINGULARITY_PROCESS
        }

        //
        // Allocate virtually but not physically contiguous pages. The resulting
        // IoMemory object grants access only to the number of bytes requested
        // (possibly leaving inaccessible bytes at the end of the last page)
        //
        static public IoMemory AllocateRealFixed(UIntPtr bytes)
        {
#if SINGULARITY_KERNEL
            return AllocateRealFixed(bytes, Thread.CurrentProcess, PageType.NonGC);
#elif SINGULARITY_PROCESS
            int mybytes = (int)bytes;
            bytes = PagePad(bytes);

            UIntPtr addr = (UIntPtr)PageTableService.Allocate((uint)bytes);

            if (addr == UIntPtr.Zero) {
                return null;
            }

            return new IoMemory(MemoryType.RegularPages, addr, mybytes, true, true);
#endif // SINGULARITY_PROCESS
        }


#if SINGULARITY_KERNEL
        //
        // Kernel-only implementation of AllocateRealFixed
        //
        static internal IoMemory AllocateRealFixed(UIntPtr bytes, Process process,
                                                   PageType type)
        {
            int mybytes = (int)bytes;
            UIntPtr pages = MemoryManager.PagesFromBytes(bytes);
            UIntPtr addr = MemoryManager.KernelAllocate(pages, process, 0, PageType.NonGC);

#if DONT_DUMP
            unchecked {
                Tracing.Log(Tracing.Debug, "AllocateFixed     -> [{0,8:x8}..{1,8:x8}]\n",
                            addr, addr + bytes);
            }
#endif
            if (addr == UIntPtr.Zero) {
                return null;
            }

            return new IoMemory(MemoryType.RegularPages, addr, (int)mybytes, true, true);
        }
#endif // SINGULARITY_KERNEL



#if SINGULARITY_KERNEL
        //
        // Kernel-only implementation of AllocateFixed
        //
        static internal IoMemory AllocateFixed(UIntPtr bytes, Process process,
                                               PageType type)
        {
            bytes = MemoryManager.PagePad(bytes);
            UIntPtr pages = MemoryManager.PagesFromBytes(bytes);
            UIntPtr addr = MemoryManager.KernelAllocate(pages, process, 0, PageType.NonGC);

#if DONT_DUMP
            unchecked {
                Tracing.Log(Tracing.Debug, "AllocateFixed     -> [{0,8:x8}..{1,8:x8}]\n",
                            addr, addr + bytes);
            }
#endif

            if (addr == UIntPtr.Zero) {
                return null;
            }

            return new IoMemory(MemoryType.RegularPages, addr, (int)bytes, true, true);
        }
#endif // SINGULARITY_KERNEL

        //
        // Allocate PHYSICALLY contiguous memory. This allocates IO memory,
        // which is a scarce system resource when paging is enabled.
        //
        static public IoMemory AllocatePhysical(UIntPtr bytes)
        {
            return AllocatePhysical(bytes, 0);
        }

        static public IoMemory AllocatePhysical(UIntPtr bytes,
                                                UIntPtr alignment)
        {
            return AllocatePhysical(0, bytes, alignment);
        }

        static public IoMemory AllocatePhysical(UIntPtr limitAddr,
                                                UIntPtr bytes,
                                                UIntPtr alignment)
        {
#if SINGULARITY_KERNEL
            bytes = MemoryManager.PagePad(bytes);
            UIntPtr addr = MemoryManager.AllocateIOMemory(
                limitAddr, bytes, alignment, Thread.CurrentProcess);

#elif SINGULARITY_PROCESS
            bytes = PagePad(bytes);
            UIntPtr addr = (UIntPtr)PageTableService.AllocateIOMemory(
                (uint)limitAddr, (uint)bytes, (uint)alignment);
#endif // SINGULARITY_PROCESS
#if DONT_DUMP
            unchecked {
                Tracing.Log(Tracing.Debug, "AllocateFixed16MB -> [{0,8:x8}..{1,8:x8}]\n",
                            addr, addr + bytes);
            }
#endif

            if (addr == UIntPtr.Zero) {
                return null;
            }

            // IO memory is identity-mapped
            return new IoMemory(MemoryType.IOMemory, new PhysicalAddress((ulong)addr),
                                addr, (int)bytes, true, true);
        }

        //
        // Allocate PHYSICALLY contiguous memory below the 16MB boundary.
        // This allocates IO memory, which is a scarce system resource when
        // paging is enabled.
        //
        static public IoMemory AllocatePhysBelow16MB(UIntPtr bytes)
        {
            return AllocatePhysBelow16MB(bytes);
        }

        static public IoMemory AllocatePhysBelow16MB(UIntPtr bytes, UIntPtr alignment)
        {
            return AllocatePhysical(0x1000000, bytes, alignment);
        }

        static public void Release(IoMemory range)
        {
            if (range == null || !range.readable) {
                throw new ArgumentNullException("Range is null");
            }

#if SINGULARITY_KERNEL
            Release(Thread.CurrentProcess, range);
#elif SINGULARITY_PROCESS

            switch (range.type) {
                case MemoryType.RegularPages :
                    PageTableService.Free(range.VirtualAddress,
                                          PagePad((UIntPtr)range.bytes));
                    break;

                case MemoryType.IOMemory :
                    PageTableService.FreeIOMemory(range.VirtualAddress,
                                                  PagePad((UIntPtr)range.bytes));
                    break;

                case MemoryType.PhysMapped :
                    DeviceService.UnmapPhysicalRange((uint)range.VirtualAddress,
                                                     (uint)(range.VirtualAddress + range.bytes));
                    break;

                case MemoryType.VirtWrapper :
                case MemoryType.PhysWrapper :
                    // We do not own the memory; don't free it.
                    break;

                default :
                    DebugStub.Assert(false, "Unknown memory type in IoMemory.Release");
                    break;
            }

            range.readable = false;
            range.writable = false;
#endif
        }

#if SINGULARITY_KERNEL
        static internal void Release(Process process, IoMemory range)
        {
            if (range == null || !range.readable) {
                throw new ArgumentNullException("Range is null");
            }

            switch (range.type) {
                case MemoryType.RegularPages :
                    UIntPtr pages = MemoryManager.PagesFromBytes((UIntPtr)range.bytes);

                    //
                    // NOTE: we allocate memory both in the kernel range and
                    // the user range under different scenarios, so distinguish by
                    // pointer value.
                    //
                    if (range.VirtualAddress > Platform.KERNEL_BOUNDARY) {
                        MemoryManager.UserFree(range.VirtualAddress,
                                               pages,
                                               process);
                    }
                    else {
                        MemoryManager.KernelFree(range.VirtualAddress,
                                                 pages,
                                                 process);
                    }
                    break;

                case MemoryType.PhysMapped :
                    MemoryManager.KernelUnmapPhysicalMemory(
                        range.VirtualAddress,
                        range.VirtualAddress + range.bytes);
                    break;

                case MemoryType.IOMemory :
                    MemoryManager.FreeIOMemory(
                        range.VirtualAddress,
                        MemoryManager.PagePad((UIntPtr)range.bytes),
                        process);
                    break;

                case MemoryType.VirtWrapper :
                case MemoryType.PhysWrapper :
                    // We do not own the memory; don't free it.
                    break;

                default :
                    DebugStub.Assert(false, "Unknown memory type in IoMemory.Release");
                    break;
            }



            range.readable = false;
            range.writable = false;
        }
#endif

        // Sets or Gets the element at the given index.
        //
        //| <include path='docs/doc[@for="ArrayList.this"]/*' />
        public unsafe byte this[int index] {
            get {
#if !DONT_CHECK_IO_BOUNDS
                if (index < 0 || index >= bytes) {
                    Error.AccessOutOfRange();
                }
#endif
                return data[index];
            }
            set {
#if !DONT_CHECK_IO_BOUNDS
                if (index < 0 || index >= bytes) {
                    Error.AccessOutOfRange();
                }
#endif
                data[index] = value;
            }
        }

        //////////////////////////////////////////////////////////////////////
        //

        // Constructor for mappings onto physical memory
        private unsafe IoMemory(MemoryType type,
                                PhysicalAddress physicalAddr,
                                UIntPtr virtAddr,
                                int bytes,
                                bool readable,
                                bool writable)
        {
            DebugStub.Assert((type == MemoryType.IOMemory) ||
                             (type == MemoryType.PhysWrapper) ||
                             (type == MemoryType.PhysMapped));

            DebugStub.Assert(physicalAddr.Value != 0);
            DebugStub.Assert(virtAddr != 0);

            this.type = type;
            this.dataPhys = physicalAddr;
            this.data = (byte*)virtAddr;
            this.bytes = (int)bytes;
            this.readable = readable;
            this.writable = writable;
        }

        // Constructor for strictly virtual memory
        private unsafe IoMemory(MemoryType type,
                                UIntPtr virtAddr,
                                int bytes,
                                bool readable,
                                bool writable)
        {
            DebugStub.Assert((type == MemoryType.RegularPages) ||
                             (type == MemoryType.VirtWrapper));

            DebugStub.Assert(virtAddr != 0);

            this.type = type;
            this.dataPhys = PhysicalAddress.Null;
            this.data = (byte*)virtAddr;
            this.bytes = (int)bytes;
            this.readable = readable;
            this.writable = writable;
        }

        // Routines to create create a mapped port within the memory region.
        public IoMappedPort MappedPortAtOffset(uint offset, uint bytes, Access access)
        {
            return MappedPortAtOffset(offset, bytes,
                                      (access & Access.Read) != 0,
                                      (access & Access.Write) != 0);
        }

        public IoMappedPort MappedPortAtOffset(uint offset, uint count, bool read, bool write)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (offset + count > bytes || offset < 0) {
                Error.AccessOutOfRange();
            }
            if (write && !writable) {
                Error.WriteNotSupported();
            }
            if (read && !readable) {
                Error.ReadNotSupported();
            }
#endif
            return new IoMappedPort(VirtualAddress + offset, count, read, write);
        }

        // Routines to create create a sub-region within the memory region.
        public unsafe IoMemory AtOffset(uint byteOffset, int count)
        {
            return AtOffset(byteOffset, count, readable, writable);
        }

        public unsafe IoMemory AtOffset(uint byteOffset, int count,
                                        bool read, bool write)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (byteOffset + count > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif

            if ((type == MemoryType.RegularPages) ||
                (type == MemoryType.VirtWrapper)) {

                // No physical address to worry about
                DebugStub.Assert(dataPhys.Value == 0);

                return new IoMemory(MemoryType.VirtWrapper,
                                    VirtualAddress + byteOffset,
                                    count,
                                    read,
                                    write);
            }
            else {
                DebugStub.Assert(dataPhys.Value != 0);

                // Update our physical address too
                PhysicalAddress newPhys = new PhysicalAddress(PhysicalAddress.Value + byteOffset);

                return new IoMemory(MemoryType.PhysWrapper,
                                    newPhys,
                                    VirtualAddress + byteOffset,
                                    count,
                                    read,
                                    write);
            }
        }

        // This address is likely useless without creating
        // another IoMemory object...
        public unsafe PhysicalAddress PhysicalAddress
        {
            [NoHeapAllocation]
            get {
                return dataPhys;
            }
        }

        public unsafe UIntPtr VirtualAddress
        {
            [NoHeapAllocation]
            get {
                return (UIntPtr)data;
            }
        }

        public int Length
        {
            [NoHeapAllocation]
            get {
                return bytes;
            }
        }

        public override string ToString()
        {
            return String.Format("32:{0,8:x8} -> {1,8:x8}[{2:x}]",
                                 (uint)VirtualAddress, PhysicalAddress.Value,
                                 (uint)bytes);
        }

        public static unsafe void Copy(IoMemory source,
                                       int    byteSource,
                                       IoMemory destination,
                                       int    byteDestination,
                                       int    count)
        {
            byte* srcdataptr = source.data, destdataptr = destination.data;
#if !DONT_CHECK_IO_BOUNDS
            if (byteSource + count > source.bytes           ||
                byteSource < 0                              ||
                byteDestination + count > destination.bytes ||
                byteDestination < 0)
            {
                Error.AccessOutOfRange();
            }
#endif
            Buffer.MoveMemory(&destdataptr[byteDestination],
                              &srcdataptr[byteSource],
                              count * sizeof(byte));
        }

        public unsafe string ReadAsciiZeroString(int byteOffset, int maxSize)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + maxSize > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif

            int len = 0;
            byte *dst = &data[byteOffset];
            for (; len < maxSize && *dst != 0; len++) {
                dst++;
            }

            return String.StringCTOR(data, byteOffset, len);
        }

        public string ReadAsciiZeroString(int byteOffset)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (byteOffset > bytes) {
                Error.AccessOutOfRange();
            }
#endif
            return ReadAsciiZeroString(byteOffset, bytes - byteOffset);
        }

        [Inline]
        public unsafe byte Read8(int byteOffset)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + sizeof(byte) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            return data[byteOffset];
        }

        [Inline]
        public unsafe ushort Read16(int byteOffset)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + sizeof(ushort) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            return *((ushort *)&data[byteOffset]);
        }

        [Inline]
        public unsafe uint Read32(int byteOffset)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + sizeof(uint) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            return *((uint *)&data[byteOffset]);
        }

        [Inline]
        public unsafe ulong Read64(int byteOffset)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + sizeof(ulong) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            return *((ulong *)&data[byteOffset]);
        }

        // --------------------------------------------------------------------
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
        IoResult CheckRead(int byteOffset, int readBytes)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                return IoResult.ReadNotSupported;
            }
            if (byteOffset + readBytes > bytes || byteOffset < 0) {
                return IoResult.AccessOutOfRange;
            }
#endif
            return IoResult.Success;
        }

        [Inline]
        [NoHeapAllocation]
        IoResult CheckWrite(int byteOffset, int writeBytes)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                return IoResult.WriteNotSupported;
            }
            if (byteOffset + writeBytes > bytes || byteOffset < 0) {
                return IoResult.AccessOutOfRange;
            }
#endif
            return IoResult.Success;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Read8NoThrow(int byteOffset, out byte value)
        {
            IoResult check = CheckRead(byteOffset, sizeof(byte));
            if (IoResult.Success == check) {
                value = data[byteOffset];
            }
            else {
                value = 0;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Read16NoThrow(int byteOffset, out ushort value)
        {
            IoResult check = CheckRead(byteOffset, sizeof(ushort));
            if (IoResult.Success == check) {
                value = *((ushort *)&data[byteOffset]);
            }
            else {
                value = 0;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Read32NoThrow(int byteOffset, out uint value)
        {
            IoResult check = CheckRead(byteOffset, sizeof(uint));
            if (IoResult.Success == check) {
                value = *((uint *)&data[byteOffset]);
            }
            else {
                value = 0;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Read64NoThrow(int byteOffset, out ulong value)
        {
            IoResult check = CheckRead(byteOffset, sizeof(ulong));
            if (IoResult.Success == check) {
                value = *((ulong *)&data[byteOffset]);
            }
            else {
                value = 0;
            }
            return check;
        }

        [NoHeapAllocation]
        public unsafe IoResult Read8NoThrow(int                byteOffset,
                                            [In, Out] byte[]   buffer,
                                            int                offset,
                                            int                count)
        {
            IoResult check = CheckRead(byteOffset, sizeof(byte) * count);
            if (IoResult.Success != check) {
                return check;
            }

#if !DONT_CHECK_IO_BOUNDS
            if (buffer == null ||
                offset < 0 ||
                offset + count > buffer.Length) {
                return IoResult.AccessOutOfRange;
            }
#endif

            fixed (byte *dst = &buffer[offset]) {
                Buffer.MoveMemory(dst, &data[byteOffset],
                                  count * sizeof(byte));
            }
            return IoResult.Success;
        }

        [NoHeapAllocation]
        public unsafe IoResult Read16NoThrow(int                byteOffset,
                                             [In, Out] ushort[] buffer,
                                             int                offset,
                                             int                count)
        {
            IoResult check = CheckRead(byteOffset, sizeof(ushort) * count);
            if (IoResult.Success != check) {
                return check;
            }

#if !DONT_CHECK_IO_BOUNDS
            if (buffer == null ||
                offset < 0 ||
                offset + count > buffer.Length) {
                return IoResult.AccessOutOfRange;
            }
#endif
            fixed (ushort *dst = &buffer[offset]) {
                Buffer.MoveMemory((byte *)dst, &data[byteOffset],
                                  count * sizeof(ushort));
            }
            return IoResult.Success;
        }

        [NoHeapAllocation]
        public unsafe IoResult Read32NoThrow(int              byteOffset,
                                             [In, Out] uint[] buffer,
                                             int              offset,
                                             int              count)
        {
            IoResult check = CheckRead(byteOffset, sizeof(uint) * count);
            if (IoResult.Success != check) {
                return check;
            }

#if !DONT_CHECK_IO_BOUNDS
            if (buffer == null ||
                offset < 0 ||
                offset + count > buffer.Length) {
                return IoResult.AccessOutOfRange;
            }
#endif
            fixed (uint *dst = &buffer[offset]) {
                Buffer.MoveMemory((byte *)dst, &data[byteOffset],
                                  count * sizeof(uint));
            }
            return IoResult.Success;
        }

        [NoHeapAllocation]
        public unsafe IoResult Read64NoThrow(int               byteOffset,
                                             [In, Out] ulong[] buffer,
                                             int               offset,
                                             int               count)
        {
            IoResult check = CheckRead(byteOffset, sizeof(ulong) * count);
            if (IoResult.Success != check) {
                return check;
            }

#if !DONT_CHECK_IO_BOUNDS
            if (buffer == null ||
                offset < 0 ||
                offset + count > buffer.Length) {
                return IoResult.AccessOutOfRange;
            }
#endif

            fixed (ulong *dst = &buffer[offset]) {
                Buffer.MoveMemory((byte *)dst, &data[byteOffset],
                                  count * sizeof(ulong));
            }
            return IoResult.Success;
        }

        [NoHeapAllocation]
        public unsafe IoResult Write8NoThrow(int                byteOffset,
                                             [In, Out] byte[]   buffer,
                                             int                offset,
                                             int                count)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(byte) * count);
            if (IoResult.Success != check) {
                return check;
            }

#if !DONT_CHECK_IO_BOUNDS
            if (buffer == null ||
                offset < 0 ||
                offset + count > buffer.Length) {
                return IoResult.AccessOutOfRange;
            }
#endif

            fixed (byte *src = &buffer[offset]) {
                Buffer.MoveMemory(&data[byteOffset], src,
                                  count * sizeof(byte));
            }
            return IoResult.Success;
        }

        [NoHeapAllocation]
        public unsafe IoResult Write16NoThrow(int                byteOffset,
                                              [In, Out] ushort[] buffer,
                                              int                offset,
                                              int                count)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(ushort) * count);
            if (IoResult.Success != check) {
                return check;
            }

#if !DONT_CHECK_IO_BOUNDS
            if (buffer == null ||
                offset < 0 ||
                offset + count > buffer.Length) {
                return IoResult.AccessOutOfRange;
            }
#endif
            fixed (ushort *src = &buffer[offset]) {
                Buffer.MoveMemory(&data[byteOffset], (byte *)src,
                                  count * sizeof(ushort));
            }
            return IoResult.Success;
        }

        [NoHeapAllocation]
        public unsafe IoResult Write32NoThrow(int              byteOffset,
                                              [In, Out] uint[] buffer,
                                              int              offset,
                                              int              count)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(uint) * count);
            if (IoResult.Success != check) {
                return check;
            }

#if !DONT_CHECK_IO_BOUNDS
            if (buffer == null ||
                offset < 0 ||
                offset + count > buffer.Length) {
                return IoResult.AccessOutOfRange;
            }
#endif
            fixed (uint *src = &buffer[offset]) {
                Buffer.MoveMemory(&data[byteOffset], (byte *)src,
                                  count * sizeof(uint));
            }
            return IoResult.Success;
        }

        [NoHeapAllocation]
        public unsafe IoResult Write64NoThrow(int               byteOffset,
                                              [In, Out] ulong[] buffer,
                                              int               offset,
                                              int               count)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(ulong) * count);
            if (IoResult.Success != check) {
                return check;
            }

#if !DONT_CHECK_IO_BOUNDS
            if (buffer == null ||
                offset < 0 ||
                offset + count > buffer.Length) {
                return IoResult.AccessOutOfRange;
            }
#endif

            fixed (ulong *src = &buffer[offset]) {
                Buffer.MoveMemory(&data[byteOffset], (byte *)src,
                                  count * sizeof(ulong));
            }
            return IoResult.Success;
        }

        // --------------------------------------------------------------------

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write8NoThrow(int byteOffset, byte value)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(byte));
            if (IoResult.Success == check) {
                data[byteOffset] = value;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write16NoThrow(int byteOffset, ushort value)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(ushort));
            if (IoResult.Success == check) {
                *((ushort *)&data[byteOffset]) = value;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write32NoThrow(int byteOffset, uint value)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(uint));
            if (IoResult.Success == check) {
                *((uint *)&data[byteOffset]) = value;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write64NoThrow(int byteOffset, ulong value)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(ulong));
            if (IoResult.Success == check) {
                *((ulong *)&data[byteOffset]) = value;
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write8NoThrow(int  byteOffset,
                                             byte value,
                                             int  count)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(byte) * count);
            if (IoResult.Success == check) {
                byte *temp = &data[byteOffset];
                while (count-- > 0) {
                    *temp++ = value;
                }
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write16NoThrow(int    byteOffset,
                                              ushort value,
                                              int    count)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(ushort) * count);
            if (IoResult.Success == check) {
                ushort *temp = (ushort*) &data[byteOffset];
                while (count-- > 0) {
                    *temp++ = value;
                }
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write32NoThrow(int  byteOffset,
                                              uint value,
                                              int  count)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(uint) * count);
            if (IoResult.Success == check) {
                uint *temp = (uint*) &data[byteOffset];
                while (count-- > 0) {
                    *temp++ = value;
                }
            }
            return check;
        }

        [Inline]
        [NoHeapAllocation]
        public unsafe IoResult Write64NoThrow(int   byteOffset,
                                              ulong value,
                                              int   count)
        {
            IoResult check = CheckWrite(byteOffset, sizeof(ulong) * count);
            if (IoResult.Success == check) {
                ulong *temp = (ulong*) &data[byteOffset];
                while (count-- > 0) {
                    *temp++ = value;
                }
            }
            return check;
        }

#endif // SINGULARITY_KERNEL
#endregion // NoHeapAllocation Read/Write operations

        // --------------------------------------------------------------------

        [Inline]
        [NoHeapAllocation]
        internal unsafe byte Read8Unchecked(int byteOffset)
        {
            return data[byteOffset];
        }

        [Inline]
        [NoHeapAllocation]
        internal unsafe ushort Read16Unchecked(int byteOffset)
        {
            return *((ushort *)&data[byteOffset]);
        }

        [Inline]
        [NoHeapAllocation]
        internal unsafe uint Read32Unchecked(int byteOffset)
        {
            return *((uint *)&data[byteOffset]);
        }

        [Inline]
        [NoHeapAllocation]
        internal unsafe ulong Read64Unchecked(int byteOffset)
        {
            return *((ulong *)&data[byteOffset]);
        }

        public unsafe void Read8(int byteOffset, byte *values, int count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + count * sizeof(byte) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            Buffer.MoveMemory(values, &data[byteOffset], count * sizeof(byte));
        }

        public unsafe void Read8(int                byteOffset,
                                 [In, Out] byte[]   buffer,
                                 int                offset,
                                 int                count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + count * sizeof(byte) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
            if (buffer == null || offset < 0 || offset + count > buffer.Length) {
                Error.AccessOutOfRange();
            }
#endif

            fixed (byte *dst = &buffer[offset]) {
                Buffer.MoveMemory(dst, &data[byteOffset], count * sizeof(byte));
            }
        }

        public unsafe void Read16(int                byteOffset,
                                  [In, Out] ushort[] buffer,
                                  int                offset,
                                  int                count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + count * sizeof(ushort) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
            if (buffer == null || offset < 0 || offset + count > buffer.Length) {
                Error.AccessOutOfRange();
            }
#endif

            fixed (ushort *dst = &buffer[offset]) {
                Buffer.MoveMemory((byte *)dst, &data[byteOffset], count * sizeof(ushort));
            }
        }

        public unsafe void Read32(int              byteOffset,
                                  [In, Out] uint[] buffer,
                                  int              offset,
                                  int              count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + count * sizeof(uint) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
            if (buffer == null || offset < 0 || offset + count > buffer.Length) {
                Error.AccessOutOfRange();
            }
#endif

            fixed (uint *dst = &buffer[offset]) {
                Buffer.MoveMemory((byte *)dst, &data[byteOffset], count * sizeof(uint));
            }
        }

        public unsafe void Read64(int               byteOffset,
                                  [In, Out] ulong[] buffer,
                                  int               offset,
                                  int               count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + count * sizeof(ulong) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
            if (buffer == null || offset < 0 || offset + count > buffer.Length) {
                Error.AccessOutOfRange();
            }
#endif
            fixed (ulong *dst = &buffer[offset]) {
                Buffer.MoveMemory((byte *)dst, &data[byteOffset], count * sizeof(ulong));
            }
        }

        public void Read8(int byteOffset, [In,Out] byte[] buffer)
        {
            Read8(byteOffset, buffer, 0, buffer.Length);
        }

        public void Read16(int byteOffset, [In,Out] ushort[] buffer)
        {
            Read16(byteOffset, buffer, 0, buffer.Length);
        }

        public void Read32(int byteOffset, [In,Out] uint[] buffer)
        {
            Read32(byteOffset, buffer, 0, buffer.Length);
        }

        public void Read64(int byteOffset, [In,Out] ulong[] buffer)
        {
            Read64(byteOffset, buffer, 0, buffer.Length);
        }

        public unsafe string ReadString(int byteOffset, int count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteOffset + count * sizeof(byte) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            char[] tempString = new char[count];
            for (int i = 0; i < count; i++) {
                tempString[i] = (char)data[i + byteOffset];
            }
            return new string(tempString);

        }

        public unsafe void WriteString(int byteOffset, string tempString)
        {
            int count = tempString.Length;
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(byte) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            for (int i = 0; i < count; i++) {
                data[i + byteOffset] = (byte)tempString[i];
            }
        }

        [Inline]
        public unsafe void Write8(int byteOffset, byte value)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + sizeof(byte) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            data[byteOffset] = value;
        }

        [Inline]
        public unsafe void Write16(int byteOffset, ushort value)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + sizeof(ushort) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            *((ushort *)&data[byteOffset]) = value;
        }

        [Inline]
        public unsafe void Write32(int byteOffset, uint value)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + sizeof(uint) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            *((uint *)&data[byteOffset]) = value;
        }

        [Inline]
        public unsafe void Write64(int byteOffset, ulong value)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + sizeof(ulong) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            *((ulong *)&data[byteOffset]) = value;
        }

        [Inline]
        [NoHeapAllocation]
        internal unsafe void Write8Unchecked(int byteOffset, byte value)
        {
            data[byteOffset] = value;
        }

        [Inline]
        [NoHeapAllocation]
        internal unsafe void Write16Unchecked(int byteOffset, ushort value)
        {
            *((ushort *)&data[byteOffset]) = value;
        }

        [Inline]
        [NoHeapAllocation]
        internal unsafe void Write32Unchecked(int byteOffset, uint value)
        {
            *((uint *)&data[byteOffset]) = value;
        }

        [Inline]
        [NoHeapAllocation]
        internal unsafe void Write64Unchecked(int byteOffset, ulong value)
        {
            *((ulong *)&data[byteOffset]) = value;
        }

        public unsafe void Write8(int byteOffset, byte value, int count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(byte) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif

            byte *temp = &data[byteOffset];
            while (count-- > 0) {
                *temp++ = value;
            }
        }

        public unsafe void Write16(int byteOffset, ushort value, int count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(ushort) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif

            ushort *temp = (ushort *)&data[byteOffset];
            while (count-- > 0) {
                *temp++ = value;
            }
        }

        public unsafe void Write32(int byteOffset, uint value, int count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(uint) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif

            uint *temp = (uint *)&data[byteOffset];
            while (count-- > 0) {
                *temp++ = value;
            }
        }

        public unsafe void Write64(int byteOffset, ulong value, int count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(ulong) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif

            ulong *temp = (ulong *)&data[byteOffset];
            while (count-- > 0) {
                *temp++ = value;
            }
        }

        public unsafe void Write8(int byteOffset, byte[] values)
        {
            Write8(byteOffset, values, 0, values.Length);
        }

        public unsafe void Write16(int byteOffset, ushort[] values)
        {
            Write16(byteOffset, values, 0, values.Length);
        }

        public unsafe void Write32(int byteOffset, uint[] values)
        {
            Write32(byteOffset, values, 0, values.Length);
        }

        public unsafe void Write64(int byteOffset, ulong[] values)
        {
            Write64(byteOffset, values, 0, values.Length);
        }

        public unsafe void Write8(int byteOffset, byte *values, int count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(byte) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
#endif
            Buffer.MoveMemory(&data[byteOffset], values, count * sizeof(byte));
        }

        public unsafe void Write8(int    byteOffset,
                                  byte[] buffer,
                                  int    offset,
                                  int    count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(byte) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
            if (buffer == null || offset < 0 || offset + count > buffer.Length) {
                Error.AccessOutOfRange();
            }
#endif

            fixed (byte *src = &buffer[offset]) {
                Buffer.MoveMemory(&data[byteOffset], src, count * sizeof(byte));
            }
        }

        public unsafe void Write16(int      byteOffset,
                                   ushort[] buffer,
                                   int      offset,
                                   int      count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(ushort) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
            if (buffer == null || offset < 0 ||
                offset + count > buffer.Length) {
                Error.AccessOutOfRange();
            }
#endif

            fixed (ushort *src = &buffer[offset]) {
                Buffer.MoveMemory(&data[byteOffset], (byte *)src,
                                  count * sizeof(ushort));
            }
        }

        public unsafe void Write32(int    byteOffset,
                                   uint[] buffer,
                                   int    offset,
                                   int    count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(uint) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
            if (buffer == null || offset < 0 || offset + count > buffer.Length) {
                Error.AccessOutOfRange();
            }
#endif

            fixed (uint *src = &buffer[offset]) {
                Buffer.MoveMemory(&data[byteOffset], (byte *)src,
                                  count * sizeof(uint));
            }
        }

        public unsafe void Write64(int     byteOffset,
                                   ulong[] buffer,
                                   int     offset,
                                   int     count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (byteOffset + count * sizeof(ulong) > bytes || byteOffset < 0) {
                Error.AccessOutOfRange();
            }
            if (buffer == null || offset < 0 || offset + count > buffer.Length) {
                Error.AccessOutOfRange();
            }
#endif

            fixed (ulong *src = &buffer[offset]) {
                Buffer.MoveMemory(&data[byteOffset], (byte *)src,
                                  count * sizeof(ulong));
            }
        }

        public unsafe void Copy8(int byteSource,
                                 int byteDestination,
                                 int count)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                Error.WriteNotSupported();
            }
            if (!readable) {
                Error.ReadNotSupported();
            }
            if (byteDestination + count > bytes || byteDestination < 0) {
                Error.AccessOutOfRange();
            }
            if (byteSource + count > bytes || byteSource < 0) {
                Error.AccessOutOfRange();
            }
#endif
            Buffer.MoveMemory(&data[byteDestination], &data[byteSource],
                              count);
        }

        public unsafe void Copy16(int byteSource,
                                  int byteDestination,
                                  int count)
        {
            Copy8(byteSource, byteDestination, count * sizeof(ushort));
        }

        public unsafe void Copy32(int byteSource,
                                  int byteDestination,
                                  int count)
        {
            Copy8(byteSource, byteDestination, count * sizeof(uint));
        }

        public unsafe void Copy64(int byteSource,
                                  int byteDestination,
                                  int count)
        {
            Copy8(byteSource, byteDestination, count * sizeof(ulong));
        }

#if SINGULARITY_KERNEL

        [NoHeapAllocation]
        private IoResult CheckCopy(int byteSource,
                                   int byteDestination,
                                   int byteCount)
        {
#if !DONT_CHECK_IO_BOUNDS
            if (!writable) {
                return IoResult.WriteNotSupported;
            }
            if (!readable) {
                return IoResult.ReadNotSupported;
            }
            if (byteDestination + byteCount > bytes ||
                byteDestination < 0) {
                return IoResult.AccessOutOfRange;
            }
            if ((byteSource + byteCount) > bytes ||
                byteSource < 0 ||
                byteCount < 0) {
                return IoResult.AccessOutOfRange;
            }
#endif // DONT_CHECK_IO_BOUNDS
            return IoResult.Success;
        }

        [NoHeapAllocation]
        public unsafe IoResult Copy8NoThrow(int byteSource,
                                            int byteDestination,
                                            int count)
        {
            int byteCount = count * sizeof(byte);
            IoResult check = CheckCopy(byteSource, byteDestination, byteCount);
            if (IoResult.Success == check) {
                Buffer.MoveMemory(&data[byteDestination], &data[byteSource],
                                  byteCount);
            }
            return check;
        }

        [NoHeapAllocation]
        public unsafe IoResult Copy16NoThrow(int byteSource,
                                             int byteDestination,
                                             int count)
        {
            return Copy8NoThrow(byteSource, byteDestination,
                                count * sizeof(ushort));
        }

        [NoHeapAllocation]
        public unsafe IoResult Copy32NoThrow(int byteSource,
                                             int byteDestination,
                                             int count)
        {
            return Copy8NoThrow(byteSource, byteDestination,
                                count * sizeof(uint));
        }

        [NoHeapAllocation]
        public unsafe IoResult Copy64NoThrow(int byteSource,
                                             int byteDestination,
                                             int count)
        {
            return Copy8NoThrow(byteSource, byteDestination,
                                count * sizeof(ulong));
        }
#endif //SINGULARITY_KERNEL
    }
}
