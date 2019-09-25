//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Notes: The underlying implementation of the ring buffer code.
//  IntelRxRingBuffer or IntelTxRingBuffer should be used for actual
//  implementation of these buffers.
//

using Microsoft.Contracts;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.V1.Services;
using System;

namespace Microsoft.Singularity.Drivers.Network.Intel
{
    internal class IntelRingBuffer
    {
        /// <summary>
        /// Structure used to hold Virtual-To-Physical addresses for
        /// data blocks passed into an NvMacRingBuffer instance.
        /// </summary>
        internal struct MapEntry {
            internal DmaMemory mem;
            internal uint VirtualAddress { get { return mem.PhysicalAddress; } }
            internal uint PhysicalAddress { get { return mem.PhysicalAddress; } }
        }

        private const uint DescriptorBytes = 16;
        private const uint AlignmentBytes  = 64;  // cache line alignment

        private DmaMemory region;
        private MapEntry [] mapEntries;
        uint capacity;
        uint head;
        uint tail;
        uint count;

        internal IntelRingBuffer(uint capacity)
            //requires capacity > 0 && IsPowerOf2(capacity);
        {
            uint length  = capacity * DescriptorBytes;
            DmaMemory region = new DmaMemory((int)length); //TODO: DmaMemory.AllocatePhysical(length, AlignmentBytes);

            // (ARM only, not x86) PlatformService.SetCacheAttributes(region.VirtualAddress,
            //                                   (UIntPtr)region.Length,
            //                                   false,
            //                                   false);

            this.region     = region;
            this.mapEntries = new MapEntry [capacity];
            for (int i = 0; i < capacity; i++) {
                 this.mapEntries[i].mem = new DmaMemory((int)Intel.IEEE8023FrameBytes);
            }
            this.capacity   = capacity;

            this.head       = 0;
            this.tail       = 0;
            this.count      = 0;

            // Clear out ring buffer
            for (int i = 0; i < region.Length; i += 4) {
                region.Write32(i, 0);
            }
        }

        internal void Reset()
            //requires this.Count == 0;
        {
            this.head = 0;
            this.tail = 0;

            for (int i = 0; i < this.region.Length; i += 4) {
                this.region.Write32(i, 0);
            }
        }

        internal void Push(ulong controlBits)
            //requires this.Count < (this.Capacity - 1); // must keep one slot empty to prevent
                                                       // head==tail which would signal an
                                                       // empty buffer.
            //ensures  this.Count == old(this.Count) + 1;
        {
            UIntPtr pa = this.mapEntries[this.head].PhysicalAddress;
            WriteDescriptor(this.head, pa, controlBits);

            this.head = (this.head + 1) & (this.Capacity - 1);
            this.count++;
        }

        internal DmaMemory PeekHead()
        {
            return this.mapEntries[this.head].mem;
        }

        internal void Pop()
            //requires this.Count > 0;
            //ensures  this.Count == old(this.count) - 1;
        {
            this.tail = (this.tail + 1) & (this.Capacity - 1);
            this.count--;
        }

        // Returns true if hardware is done with this descriptor.
        internal bool Peek() {
            if (this.count > 0) {
                uint cb = this.region.Read32((int) (this.tail * DescriptorBytes + 12));
                return (cb & DescriptorStat.DESCRIPTOR_DONE) != 0;
            } else {
                return false;
            }
        }

        // Returns true if hardware is done with this descriptor.
        internal bool Peek(out DmaMemory mem,
                           out ulong controlBits)
        {
            if (this.count > 0) {
                UIntPtr pa;
                ReadDescriptor(this.tail, out pa, out controlBits);
                DebugStub.Assert(pa == this.mapEntries[tail].PhysicalAddress);
                mem = this.mapEntries[tail].mem;
                return ((controlBits & Descriptor.DESCRIPTOR_DONE) != 0);
            } else {
                mem = null;
                controlBits = 0;
                return false;
            }
        }

        private void WriteDescriptor(uint index,
                                     UIntPtr physicalAddr,
                                     ulong controlBits)
            //requires (index >= 0 && index <= this.Capacity);
        {
            ulong addrPtr = physicalAddr.ToUInt64();
            int  descriptorOffset = (int)(index * DescriptorBytes);

            this.region.Write64(descriptorOffset, addrPtr);
            this.region.Write64(descriptorOffset + 8, controlBits);

#if false
            // (ARM only, not x86) PlatformService.CleanAndInvalidateDCache(
            //  ((UIntPtr)this.region.PhysicalAddress.Value) + descriptorOffset,
            //  DescriptorBytes);
#endif // false
        }

        private void ReadDescriptor(uint index,
                                    out UIntPtr physicalAddr,
                                    out ulong controlBits)
        {
            int  descriptorOffset = (int)(index * DescriptorBytes);

#if false
            // (ARM only, not x86) PlatformService.InvalidateDCache(
            //  ((UIntPtr)this.region.PhysicalAddress.Value) + descriptorOffset,
            //  DescriptorBytes);
#endif // false

            ulong addrPtr = this.region.Read64(descriptorOffset);
            controlBits   = this.region.Read64(descriptorOffset + 8);
            physicalAddr = new UIntPtr(addrPtr);
        }

/*
        internal static UIntPtr GetPhysicalAddress(UIntPtr va)
        {
            UIntPtr pa;         // Physical address
            UIntPtr paLeft;     // Bytes remaining on physical page
            if (!DeviceService.GetDmaPhysicalAddress(va, out pa, out paLeft) ||
                pa == UIntPtr.Zero ||
                paLeft < Intel.IEEE8023FrameBytes) {
                throw new ApplicationException("Bad DMA pointer");
            }
            return pa;
        }
*/

        internal void Dump(string preamble, uint count)
        {
            if (count > this.capacity) {
                count = this.capacity;
            }
            Intel.DebugWriteLine("Head {0} Tail {1}\n",
                                 DebugStub.ArgList(this.Head, this.Tail));
            for (uint i = 0; i < count; i++) {
                ulong address = this.region.Read64((int)(i * 16));
                ulong fields  = this.region.Read64((int)(i * 16 + 8));
                Intel.DebugWriteLine("{0}: [{1}] Address {2:x16} Sp={3:x4} Err={4:x1} Sta={5:x2} Checksum {6:x4} Length {7:x4}",
                                     DebugStub.ArgList(preamble, i, address,
                                               (fields >> 48) & 0xffff,
                                               (fields >> 40) & 0xff,
                                               (fields >> 32) & 0xff,
                                               (fields >> 16) & 0xffff,
                                               fields & 0xffff));
            }
        }

        internal uint BaseAddress
        {
            get { return this.region.PhysicalAddress; }
        }

        //[Pure]
        internal uint Capacity { get { return this.capacity; } }

        // Note, saves one descriptor so that ring never gets completely full, which would
        // lead to head == tail, which the hardware takes as meaning the ring is empty.
        //[Pure]
        internal uint Free { get { return (this.capacity - 1) - this.count; } }

        //[Pure]
        internal bool IsFull { get { return (this.Free == 0); } }

        //[Pure]
        internal uint Count { get { return this.count; } }

        //[Pure]
        internal uint Tail { get { return this.tail; } }

        //[Pure]
        internal uint Head { get { return this.head; } }

        //[Pure]
        internal uint DescLength { get { return (this.Capacity * DescriptorBytes); } }

        //[Pure]
        internal static bool IsPowerOf2(uint n)
        {
            return (n > 0) && ((n & (n - 1)) == 0);
        }
    }
}
