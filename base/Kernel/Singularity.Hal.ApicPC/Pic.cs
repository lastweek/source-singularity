///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Pic.cs
//
//  Note:
//    http://home.ozonline.com.au/davmac/davpage/PIC.html
//

using Microsoft.Singularity.Io;

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Configuration;

namespace Microsoft.Singularity.Hal
{
    [DriverCategory]
    [Signature("/pnp/PNP0000")]
    public sealed class PicStubResources : DriverCategoryDeclaration
    {
        [IoPortRange(0, Default = 0x0020, Length = 0x02)]
        public IoPortRange port1;

        [IoPortRange(1, Default = 0x00a0, Length = 0x02)]
        public IoPortRange port2;
    }

    [ CLSCompliant(false) ]
    public sealed class PicStub
    {
        public const byte PIC_VECTORS = 16;

        private IoPort pic0CtrlPort;
        private IoPort pic0MaskPort;
        private IoPort pic1CtrlPort;
        private IoPort pic1MaskPort;
        private byte   baseVector;

        // Constants for PIC interrupt vectors.

        internal PicStub(PnpConfig config)
        {
            // /pnp/08/00/01/PNP0000 0003 cfg dis
            // I/O Port inf=01 min=0020 max=0020 aln=01 len=02 0020..0021
            // I/O Port inf=01 min=00a0 max=00a0 aln=01 len=02 00a0..00a1
            // IRQ mask=0004 type=79

            // Range[0]: 0x20; // PIC0
            // Range[1]: 0xA0; // PIC1

            pic0CtrlPort = ((IoPortRange)config.DynamicRanges[0])
                .PortAtOffset(0, 1, Access.ReadWrite);
            pic0MaskPort = ((IoPortRange)config.DynamicRanges[0])
                .PortAtOffset(1, 1, Access.ReadWrite);
            pic1CtrlPort = ((IoPortRange)config.DynamicRanges[1])
                .PortAtOffset(0, 1, Access.ReadWrite);
            pic1MaskPort = ((IoPortRange)config.DynamicRanges[1])
                .PortAtOffset(1, 1, Access.ReadWrite);
        }

        public byte Initialize(byte baseVector)
        {
            this.baseVector = baseVector;

            // Set ICW1 (must be followed by ICW2, ICW3, and ICW4).
            //  00010001b - 8-byte,cascaded,triggered,w/ICW4
            pic1CtrlPort.Write8(0x11);
            pic0CtrlPort.Write8(0x11);

            // ICW2
            pic1MaskPort.Write8((byte)(baseVector + 8));
            pic0MaskPort.Write8(baseVector);

            // ICW3
            pic1MaskPort.Write8(0x02); // Cascaded interrupt number
            pic0MaskPort.Write8(0x04); // Cascaded interrupt bit.

            // ICW4
            pic1MaskPort.Write8(1);
            pic0MaskPort.Write8(1);

            // OCW2 - EOI
            pic1CtrlPort.Write8(0x20);
            pic0CtrlPort.Write8(0x20);

            MaskAll();
            DumpRegisters();

            pic1CtrlPort.Write8(0x20);
            pic0CtrlPort.Write8(0x20);

            MaskAll();
            DumpRegisters();
            MaskAll();

            // OCW2 - EOI
            pic1CtrlPort.Write8(0x20);
            pic0CtrlPort.Write8(0x20);

            return PIC_VECTORS;
        }

        public void Initialize()
        {
            this.Initialize(0x60);
            DumpRegisters();
        }

        [NoHeapAllocation]
        public void AckIrq(byte irq)
        {
            DumpRegisters();

#if DEBUG_INTERRUPTS
            DebugStub.Print("Int{0:x2}  Acked, Mask={1:x8}\n",
                            __arglist(irq + baseVector, irqMask));
#endif

            // Quiet the interrupt controller.
            IoResult result;
            if (irq >= 8) {
                result = pic1CtrlPort.Write8NoThrow(0x20);
                DebugStub.Assert(IoResult.Success == result);
            }
            result = pic0CtrlPort.Write8NoThrow(0x20);
            DebugStub.Assert(IoResult.Success == result);

            DumpRegisters();
        }

        [ Conditional("DEBUG_INTERRUPTS") ]
        [NoHeapAllocation]
        public void DumpRegisters()
        {
            byte irr0, isr0, irr1, isr1;
            IoResult result;

            // OCW3  - read IRR
            result = pic0CtrlPort.Write8NoThrow(0x04 | 0x02);
            DebugStub.Assert(IoResult.Success == result);

            result = pic0CtrlPort.Read8NoThrow(out irr0);
            DebugStub.Assert(IoResult.Success == result);

            // OCW3  - read ISR
            result = pic0CtrlPort.Write8NoThrow(0x04 | 0x03);
            DebugStub.Assert(IoResult.Success == result);

            result = pic0CtrlPort.Read8NoThrow(out isr0);
            DebugStub.Assert(IoResult.Success == result);

            // OCW3  - read IRR
            result = pic1CtrlPort.Write8NoThrow(0x04 | 0x02);
            DebugStub.Assert(IoResult.Success == result);

            result = pic1CtrlPort.Read8NoThrow(out irr1);
            DebugStub.Assert(IoResult.Success == result);

            // OCW3  - read ISR
            result = pic1CtrlPort.Write8NoThrow(0x04 | 0x03);
            DebugStub.Assert(IoResult.Success == result);

            result = pic1CtrlPort.Read8NoThrow(out isr1);
            DebugStub.Assert(IoResult.Success == result);

            // Get mask state
            byte mask0, mask1;
            result = pic0MaskPort.Read8NoThrow(out mask0);
            DebugStub.Assert(IoResult.Success == result);

            result = pic1MaskPort.Read8NoThrow(out mask1);
            DebugStub.Assert(IoResult.Success == result);

            DebugStub.Print("PIC IRR: {0:x2}/{1:x2} ISR: {2:x2}/{3:x2} Mask {4:x2}/{5:x2}\n",
                            __arglist(irr0, irr1, isr0, isr1, mask0, mask1));
        }

        public void ReleaseResources()
        {
        }

        private void MaskAll()
        {
            pic1MaskPort.Write8(0xff);
            pic0MaskPort.Write8(0xff);
        }
    }
}
