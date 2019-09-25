///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoDma.cs
//

using System;

namespace Microsoft.Singularity.Io
{
    public class IoDma
    {
        [Flags]
        public enum Settings : byte
        {
            // DMA MODE
            DemandMode          = 0x00,
            SingleMode          = 0x40,
            BlockMode           = 0x80,
            CascadeMode         = 0xC0,

            // ADDRESS INCREMENT DECREMENT
            AddressIncrement    = 0x00,
            AddressDecrement    = 0x20,

            SingleCycle         = 0x00,
            AutoInit            = 0x10,

            // TRANSFER TYPE
            VerifyTransfer      = 0x00,
            WriteTransfer       = 0x04,
            ReadTransfer        = 0x08,
        }

        private byte channel;
        private byte modeByte;
        private byte controlByte;
        private byte controlByteMask;
        private bool eightBit;

        private IoPort addrPort;
        private IoPort countPort;
        private IoPort pagePort;
        private IoPort maskPort;
        private IoPort modePort;
        private IoPort clearPort;

        [CLSCompliant(false)]
        public IoDma(IoDmaRange dmaRange)
            : this((byte)dmaRange.Channel)
        {
        }

        [CLSCompliant(false)]
        internal IoDma(byte ugly)
        {
            channel = (byte)ugly;
            byte addrReg;
            byte countReg;
            byte pageReg;
            byte maskReg;
            byte clearReg;
            byte modeReg;

            eightBit = true;
            controlByte = 0;
            modeByte = 0;
            controlByteMask = 0;

            if (channel < 4) {
                // 8 bit transfer
                addrReg = (byte)(0x00 + (channel * 2));
                countReg = (byte)(0x01 + (channel * 2));
                pageReg = (byte)(0x80 + (new byte[4] { 0x7, 0x3, 0x1, 0x2 })[channel]);
                maskReg = 0x0A;
                clearReg= 0x0C;
                modeReg = 0x0B;
                eightBit = true;
            }
            else if (channel > 4 && channel < 8) {
                channel -= 4;

                //16 bit channel
                addrReg = (byte)(0xC0 + (channel * 4));
                countReg = (byte)(0xC2 + (channel * 4));
                pageReg = (byte)(0x88 + (new byte[4] { 0x7, 0x3, 0x1, 0x2 })[channel]);
                maskReg = 0xD4;
                clearReg = 0xD8;
                modeReg = 0xD6;
                eightBit = false;
            }
            else {
                Tracing.Log(Tracing.Fatal, "Invalid DMA Channel {0}", channel);
                throw new Exception("Invalid DMA Channel");
            }
            // create ports
            addrPort = new IoPort(addrReg, 1, Access.ReadWrite);
            countPort = new IoPort(countReg, 1, Access.ReadWrite);
            pagePort = new IoPort(pageReg, 1, Access.ReadWrite);
            maskPort =  new IoPort(maskReg, 1, Access.ReadWrite);
            clearPort = new IoPort(clearReg, 1, Access.ReadWrite);
            modePort = new IoPort(modeReg, 1, Access.ReadWrite);
        }

        public override string ToString()
        {
            return String.Format("DMA:{0,2:x2} {1}",
                                 channel,
                                 eightBit ? "8-bit" : "16-bit");
        }

        public void SetControlByteMask(Settings mask)
        {
            controlByteMask = (byte)mask;
            controlByteMask |= channel;
        }

        public void SetControlByte()
        {
            controlByte |= controlByteMask;
            modePort.Write8(controlByte);
        }

        public void EnableChannel()
        {
            maskPort.Write8(channel);
        }

        public void DisableChannel()
        {
            maskPort.Write8((byte)(channel | 0x04));
        }

        public void ClearFlipFlop()
        {
            clearPort.Write8(0x00);
        }

        [CLSCompliant(false)]
        public void SetTransferLength(ushort length)
        {
            countPort.Write8((byte)(length & 0xff));//buffersize
            countPort.Write8((byte)(length >> 8));//buffersize
        }

        [CLSCompliant(false)]
        public void SetBuffer(IoMemory buffer)
        {
            uint address = (uint)buffer.PhysicalAddress.Value;
            ushort offs = eightBit
                ? (ushort)((address) & 0xffff)
                : (ushort)((address >> 1) & 0xffff);

            pagePort.Write8((byte)((address >> 16) & 0xff));
            addrPort.Write8((byte)(offs & 0xff));
            addrPort.Write8((byte)(offs >> 8));
        }
    }// end of IoDma class
}
