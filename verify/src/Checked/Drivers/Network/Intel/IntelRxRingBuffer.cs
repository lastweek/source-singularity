///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Notes: Adaptor class for the Rx ring buffer.
//

using Microsoft.Contracts;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Io.Net;
using Microsoft.Singularity.V1.Services;
using Microsoft.SingSharp;

using System;
using ExRefPacketFifo = Microsoft.Singularity.NetStack2.Channels.Nic.ExRefPacketFifo;
using ByteOrder = Drivers.Net.ByteOrder;

namespace Microsoft.Singularity.Drivers.Network.Intel
{
    internal class IntelRxRingBuffer
    {
        IntelRingBuffer rxRingBuffer;
        ExRefPacketFifo rxPacketsInDevice;
        internal System.Threading.MonitorLock thisLock = new System.Threading.MonitorLock();

        internal IntelRxRingBuffer(uint capacity)
            //requires capacity > 0 && IntelRingBuffer.IsPowerOf2(capacity);
        {
            this.rxRingBuffer = new IntelRingBuffer(capacity);
            this.rxPacketsInDevice = new ExRefPacketFifo(
                new PacketFifo((int) capacity),
                false
                );
        }

        internal void Reset()
        {
            rxRingBuffer.Reset();
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Buffer Operations, should only be called when a lock is held
        // this ring buffer.
        //
        private void LockedPushRecvBuffer(int length)
        {
            // (ARM only, not x86) PlatformService.InvalidateDCache(packetVirtAddr, (UIntPtr)length);

            ulong controlBits = (ulong) ByteOrder.HostToLittleEndian(length);

            rxRingBuffer.Push(controlBits);
        }

        static int pass = 0;

        internal void LockedPushRecvBuffer(Packet packet)
        {
            DebugStub.Assert(packet.FragmentCount == 1);
            DebugStub.Assert(!rxRingBuffer.IsFull);

            int     length = packet.GetFragmentLength(0);

            this.LockedPushRecvBuffer(length);
            PacketFifo liveFifo = this.rxPacketsInDevice.Acquire();
            liveFifo.Push(packet);
            rxPacketsInDevice.Release(liveFifo);
        }

        internal void Dump()
        {
            rxRingBuffer.Dump("rx", 8);
        }

        private FromDeviceFlags GetRecvPktFlags(uint stat_err_flags)
        {
            FromDeviceFlags fromDevFlags = 0;

            if (((RxErrStatFields.CRC_ERROR | RxErrStatFields.SYMBOL_ERROR |
                  RxErrStatFields.SEQUENCE_ERROR | RxErrStatFields.CARRIER_EXT_ERROR |
                  RxErrStatFields.RX_DATA_ERROR) & stat_err_flags) != 0) {
                Intel.DebugPrint("Packet Rsv Error\n");
                fromDevFlags |= FromDeviceFlags.ReceiveError;
            } else {
                fromDevFlags |= FromDeviceFlags.ReceiveSuccess;
            }

            if (((stat_err_flags & RxErrStatFields.IGNORE_CHECKSUM) == 0) &&
                ((stat_err_flags & RxErrStatFields.IP_CHECKSUM_CALC) != 0)) {
                if ((stat_err_flags & RxErrStatFields.IP_CHECKSUM_ERROR) != 0) {
                    Intel.DebugPrint("Bad Ip Checksum\n");
                    fromDevFlags |= FromDeviceFlags.BadIp4Checksum;
                } else {
                    // Good IP checksum flag???
                }
            }

            if (((stat_err_flags & RxErrStatFields.IGNORE_CHECKSUM) == 0) &&
                ((stat_err_flags & RxErrStatFields.TCP_CHECKSUM_CALC)!= 0)) {
                if ((stat_err_flags & RxErrStatFields.TCP_CHECKSUM_ERROR) != 0) {
                    fromDevFlags |= (FromDeviceFlags.BadTcp4Checksum |
                                     FromDeviceFlags.BadUdp4Checksum);
                    // don't know if UDP or TCP
                    Intel.DebugPrint("Bad TCP/UDP Checksum\n");
                } else {
                    fromDevFlags |= (FromDeviceFlags.GoodTcp4Checksum |
                                     FromDeviceFlags.GoodUdp4Checksum);
                }
            }

            //DebugStub.Assert((fromDevFlags == (FromDeviceFlags.ReceiveSuccess)) || (fromDevFlags == (FromDeviceFlags.ReceiveSuccess | FromDeviceFlags.GoodTcp4Checksum | FromDeviceFlags.GoodUdp4Checksum)));

            return fromDevFlags;
        }

        private Packet MakePacketFromDescriptor(DmaMemory mem, ulong controlBits)
        {
            PacketFifo inDevPkts = rxPacketsInDevice.Acquire();
            Packet packet = inDevPkts.Pop();
            int length   = (int) ((controlBits & RxDescriptor.LENGTH_MASK)
                                  >> RxDescriptor.LENGTH_SHIFT);
            uint stat_err = (uint) ((controlBits & RxDescriptor.ERR_STAT_MASK)
                                    >> RxDescriptor.ERR_STAT_SHIFT);

            // can't deal with fragments yet
            if ((stat_err & RxErrStatFields.END_OF_PACKET) == 0) {
                INucleusCalls.DebugPrintHex(40, 0xd0);
                DebugStub.Print("FRAGMENT\n");
                throw new Exception();
            }

            //DebugStub.Assert((stat_err & RxErrStatFields.END_OF_PACKET) != 0);
            //DebugStub.Assert(packet.GetFragmentVirtualAddress(0) == fragmentVirtAddr);
            packet.FromDeviceFlags = GetRecvPktFlags(stat_err);
            packet.SetFragment(0, mem.BytesRef(0, length));
            rxPacketsInDevice.Release(inDevPkts);

            return packet;
        }

        internal void LockedDrainRecvBuffer(PacketFifo toUser)
        {
            DmaMemory mem;
            ulong   controlBits;
            while (rxRingBuffer.Peek(out mem, out controlBits)) {
                Packet packet = MakePacketFromDescriptor(mem, controlBits);
                toUser.Push(packet);
                rxRingBuffer.Pop();
            }
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Ring buffer properties
        //
        internal UIntPtr BaseAddress
        {
            get { return rxRingBuffer.BaseAddress; }
        }

        internal bool NewReceiveEvent() {
            DmaMemory mem;
            ulong   controlBits;

            return rxRingBuffer.Peek(out mem, out controlBits);
//            return rxRingBuffer.Peek();
        }

        //[Pure]
        internal uint Capacity { get { return rxRingBuffer.Capacity; } }

        //[Pure]
        internal uint Free { get { return rxRingBuffer.Free; } }

        //[Pure]
        internal bool IsFull { get { return rxRingBuffer.IsFull; } }

        //[Pure]
        internal uint Count { get { return rxRingBuffer.Count; } }

        //[Pure]
        internal uint Tail { get { return rxRingBuffer.Tail; } }

        //[Pure]
        internal uint Head { get { return rxRingBuffer.Head; } }

        //[Pure]
        internal uint DescLength { get { return rxRingBuffer.DescLength; } }
    }
}
