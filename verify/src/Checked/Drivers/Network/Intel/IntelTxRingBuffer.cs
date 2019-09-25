///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Notes: Adaptor class for the Tx ring buffer.
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
    internal class IntelTxRingBuffer
    {
        IntelRingBuffer txRingBuffer;
        ExRefPacketFifo txPacketsInDevice;
        internal System.Threading.MonitorLock thisLock = new System.Threading.MonitorLock();

        internal IntelTxRingBuffer(uint capacity)
            //requires capacity > 0 && IntelRingBuffer.IsPowerOf2(capacity);
        {
            this.txRingBuffer = new IntelRingBuffer(capacity);
            this.txPacketsInDevice = new ExRefPacketFifo(
                new PacketFifo((int) capacity),
                false
                );
        }

        internal void Reset()
        {
            txRingBuffer.Reset();
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Buffer Operations, should only be called when a lock is held
        // this ring buffer.
        //
        private void _LockedPushTsmtBuffer(Packet packet)
        {
            // (ARM only, not x86) PlatformService.CleanAndInvalidateDCache(packetVirtAddr, (UIntPtr)length);
            int length = packet.GetLength();

            ulong controlBits = (ulong) ByteOrder.HostToLittleEndian(length);

            // set necessary command fields
            controlBits |= (TxCmdFields.END_OF_PACKET | TxCmdFields.INSERT_FCS |
                            TxCmdFields.REPORT_STATUS);

            DmaMemory mem = txRingBuffer.PeekHead();
            packet.CopyToBytes(mem.BytesRef());
            txRingBuffer.Push(controlBits);
        }

        internal void LockedPushTsmtBuffer(Packet packet)
        {
            DebugStub.Assert(packet.FragmentCount == 1);
            DebugStub.Assert(!txRingBuffer.IsFull);

            this._LockedPushTsmtBuffer(packet);

            PacketFifo liveFifo = this.txPacketsInDevice.Acquire();
            liveFifo.Push(packet);
            txPacketsInDevice.Release(liveFifo);
        }

        private Packet MakePacketFromDescriptor(ulong controlBits)
        {
            PacketFifo inDevPkts = txPacketsInDevice.Acquire();
            Packet packet = inDevPkts.Pop();

            // int length   = (int) ((controlBits & TxDescriptor.LENGTH_MASK)
            //                      >> TxDescriptor.LENGTH_SHIFT);
            int stat_err = (int) ((controlBits & TxDescriptor.ERR_STAT_MASK)
                                  >> TxDescriptor.ERR_STAT_SHIFT);


            //DebugStub.Assert(packet.GetFragmentVirtualAddress(0) == fragmentVirtAddr);

            if (((TxStatErrFields.LATE_COLLISION |
                  TxStatErrFields.EXCESS_COLLISIONS |
                  TxStatErrFields.TRANSMIT_UNDERRUN) & stat_err) == 0) {
                packet.FromDeviceFlags = FromDeviceFlags.TransmitSuccess;
            } else {
                packet.FromDeviceFlags = FromDeviceFlags.TransmitError;
            }

            txPacketsInDevice.Release(inDevPkts);

            return packet;
        }

        internal void LockedDrainTsmtBuffer (PacketFifo toUser)
        {
            DmaMemory mem;
            ulong   controlBits;

            while (txRingBuffer.Peek(out mem, out controlBits)) {
                Packet packet = MakePacketFromDescriptor(controlBits);
                toUser.Push(packet);
                txRingBuffer.Pop();
            }
        }


        ///////////////////////////////////////////////////////////////////////
        //
        // Ring buffer properties
        //
        internal UIntPtr BaseAddress
        {
            get { return txRingBuffer.BaseAddress; }
        }

        internal bool NewTransmitEvent() {
            return txRingBuffer.Peek();
        }

        //[Pure]
        internal uint Capacity { get { return txRingBuffer.Capacity; } }

        //[Pure]
        internal uint Free { get { return txRingBuffer.Free; } }

        //[Pure]
        internal bool IsFull { get { return txRingBuffer.IsFull; } }

        //[Pure]
        internal uint Count { get { return txRingBuffer.Count; } }

        //[Pure]
        internal uint Tail { get { return txRingBuffer.Tail; } }

        //[Pure]
        internal uint Head { get { return txRingBuffer.Head; } }

        //[Pure]
        internal uint DescLength { get { return txRingBuffer.DescLength; } }
    }
}
