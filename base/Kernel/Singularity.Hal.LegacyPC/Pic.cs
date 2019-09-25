////////////////////////////////////////////////////////////////////////////////
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

//#define DEBUG_INTERRUPTS
//#define DEBUG_DISPATCH_IO

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Io;

namespace Microsoft.Singularity.Hal
{
    // declare resources for the kernel manifest
    [DriverCategory]
    [Signature("/pnp/PNP0000")]
    public sealed class PicResources : DriverCategoryDeclaration
    {
        [IoPortRange(0, Default = 0x20, Length = 0x02)]
        public IoPortRange port1;

        [IoPortRange(1, Default = 0xa0, Length = 0x02)]
        public IoPortRange port2;
    }

    [CLSCompliant(false)]
    public sealed class Pic : HalPic
    {
        // Constants for PIC interrupt vectors.
        public const byte   PIC0_BIOS_VECTOR    = 0x08; // IRQ0..IRQ7
        public const byte   PIC1_BIOS_VECTOR    = 0x70; // IRQ8..IRQF

        public const byte   PIC_NS_EOI          = 0x20; // OCW1: End of Interrupt.
        public const ushort PIC_I_PIC1          = 0x04; // IRQ 2 / INT 0x0a 10
        public const byte   PIC_VECTORS         = 16;

        private ushort  irqMask;
        private byte    baseVector;

        private IoPort pic0CtrlPort;
        private IoPort pic0MaskPort;
        private IoPort pic1CtrlPort;
        private IoPort pic1MaskPort;

        internal Pic(PnpConfig config)
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
            DebugStub.Print("Pic.Initializing IRQs at interrupt {0:x2}\n",
                            __arglist(baseVector));

            this.baseVector = baseVector;
            irqMask = unchecked((ushort)~PIC_I_PIC1);

            // Set ICW1 (must be followed by ICW2, ICW3, and ICW4).
            //  00010001b - 8-byte,cascaded,triggered,w/ICW4
            pic1CtrlPort.Write8(0x11);
            pic0CtrlPort.Write8(0x11);

            // Set ICW2..ICW3 (must follow ICW1)
            pic1MaskPort.Write8((byte)(baseVector + 8));
            pic0MaskPort.Write8(baseVector);

            pic1MaskPort.Write8(0x02); // Cascaded interrupt number
            pic0MaskPort.Write8(0x04); // Cascaded interrupt bit.

            pic1MaskPort.Write8(1);    // End of Interrupt
            pic0MaskPort.Write8(1);

            pic1CtrlPort.Write8(0x20);  // EOI
            pic0CtrlPort.Write8(0x20);  // EOI

            MaskAll();

            return PIC_VECTORS;
        }

        public void Initialize()
        {
            this.Initialize(0x70);
        }

        public void ReleaseResources()
        {
            UnmaskAll();
        }

        [NoHeapAllocation]
        public override byte InterruptToIrq(byte interrupt)
        {
            return (byte)(interrupt - baseVector);
        }

        [NoHeapAllocation]
        public override byte IrqToInterrupt(byte irq)
        {
            return (byte)(baseVector + irq);
        }

        public override byte MaximumIrq
        {
            [NoHeapAllocation]
            get { return PIC_VECTORS - 1; }
        }

        [System.Diagnostics.Conditional("PIC_DEBUG")]
        private void DumpRegisters()
        {
            pic0CtrlPort.Write8(0x04 | 0x02); // OCW3  - read IRR
            byte irr0 = pic0CtrlPort.Read8();
            pic0CtrlPort.Write8(0x04 | 0x03); // OCW3  - read ISR
            byte isr0 = pic0CtrlPort.Read8();
            pic1CtrlPort.Write8(0x04 | 0x02); // OCW3  - read IRR
            byte irr1 = pic1CtrlPort.Read8();
            pic1CtrlPort.Write8(0x04 | 0x03); // OCW3  - read ISR
            byte isr1 = pic1CtrlPort.Read8();
            byte mask0 = pic0MaskPort.Read8();
            byte mask1 = pic1MaskPort.Read8();

            DebugStub.Print("PIC IRR: {0:x2}{1:x2} ISR: {2:x2}{3:x2} Mask:{4:x2}{5:x2}\n",
                            __arglist(irr1, irr0, isr1, isr0, mask1, mask0));
        }

        [NoHeapAllocation]
        public override void ClearInterrupt(byte interrupt)
        {
            byte irq = InterruptToIrq(interrupt);

            Mask(irq);
            AckIrq(irq);

#if DEBUG_INTERRUPTS
            DebugStub.Print("pic.ClearInterrupt({0:x2})\n",
                            __arglist(irqMask));
#endif
        }

        [NoHeapAllocation]
        public override void AckIrq(byte irq)
        {
            DebugStub.Assert(Processor.InterruptsDisabled());
#if PIC_DEBUG
            DumpRegisters();
#endif

            // Mark the IRQ as activated and mask it
#if DEBUG_INTERRUPTS
            DebugStub.Print("Int{0:x2}  Acked, Mask={1:x4}\n",
                            __arglist(irq + baseVector, irqMask));
#endif

            // Quite the interrupt controller.
            IoResult result;
            if (irq >= 8) {
                result = pic1CtrlPort.Write8NoThrow(PIC_NS_EOI);
                DebugStub.Assert(IoResult.Success == result);
            }
            result = pic0CtrlPort.Write8NoThrow(PIC_NS_EOI);
            DebugStub.Assert(IoResult.Success == result);

#if PIC_DEBUG
            DumpRegisters();
#endif
        }

        [NoHeapAllocation]
        public ushort Pending()
        {
            byte irr0;
            byte irr1;

            IoResult result = pic0CtrlPort.Write8NoThrow(0x04 | 0x02); // OCW3  - read IRR
            DebugStub.Assert(IoResult.Success == result);

            result = pic0CtrlPort.Read8NoThrow(out irr0);
            DebugStub.Assert(IoResult.Success == result);

            result = pic1CtrlPort.Write8NoThrow(0x04 | 0x02); // OCW3  - read IRR
            DebugStub.Assert(IoResult.Success == result);

            result = pic1CtrlPort.Read8NoThrow(out irr1);
            DebugStub.Assert(IoResult.Success == result);

            return (ushort) (irr0 | (irr1<<8));
        }

        [NoHeapAllocation]
        public override void EnableIrq(byte irq)
        {
            if (irq == 2 || irq >= PIC_VECTORS) {
                DebugStub.Break();
                // throw new OverflowException
                // (String.Format("irq {0} out of range.", irq));
            }

#if DEBUG_INTERRUPTS
            DebugStub.Print("Int{0:x2}  Enable, Mask={1:x4}\n",
                            __arglist(irq + baseVector, irqMask));
#endif

            bool saved = Processor.DisableInterrupts();
            try {
                Unmask(irq);
                DumpRegisters();
            }
            finally {
                Processor.RestoreInterrupts(saved);
            }
        }

        [NoHeapAllocation]
        public override void DisableIrq(byte irq)
        {
            if (irq == 2 || irq >= PIC_VECTORS) {
                DebugStub.Break();
                //                throw new OverflowException
                // (String.Format("irq {0} out of range.", irq));
            }

#if DEBUG_INTERRUPTS
            DebugStub.Print("Int{0:x2} Disable\n",
                            __arglist(irq + baseVector));
#endif
            bool saved = Processor.DisableInterrupts();
            try {
                Mask(irq);
                DumpRegisters();
            }
            finally {
                Processor.RestoreInterrupts(saved);
            }
        }

        //////////////////////////////////////////////////////////////////////
        //
        //
        [NoHeapAllocation]
        private void Mask(byte irq)
        {
            DebugStub.Assert(Processor.InterruptsDisabled());
            ushort newMask = (ushort)(irqMask | (1 << irq));
            if (newMask != irqMask) {
#if DEBUG_DISPATCH_IO
                DebugStub.WriteLine("-- Mask IRQs:   old={0:x4} new={1:x4}",
                                    __arglist(irqMask, newMask));
#endif
                irqMask = newMask;
                IoResult result;
                result = pic1MaskPort.Write8NoThrow((byte)(irqMask >> 8));
                DebugStub.Assert(IoResult.Success == result);
                result = pic0MaskPort.Write8NoThrow((byte)(irqMask & 0xff));
                DebugStub.Assert(IoResult.Success == result);
#if PIC_DEBUG
                byte mask0;
                pic0MaskPort.Read8NoThrow(out mask0);
                byte mask1;
                pic1MaskPort.Read8NoThrow(out mask1);

                DebugStub.Print("PIC Mask: {0:x2}{1:x2}\n",
                                __arglist(mask1, mask0));
#endif
            }
        }

        [NoHeapAllocation]
        private void Unmask(byte irq)
        {
            DebugStub.Assert(Processor.InterruptsDisabled());
            ushort newMask = (ushort)(irqMask & ~(1 << irq));
            if (newMask != irqMask) {
#if DEBUG_DISPATCH_IO
                DebugStub.WriteLine("-- Unmask IRQs: old={0:x4} new={1:x4}",
                                    __arglist(irqMask, newMask));
#endif
                irqMask = newMask;
                IoResult result;

                result = pic1MaskPort.Write8NoThrow((byte)(irqMask >> 8));
                DebugStub.Assert(IoResult.Success == result);

                result = pic0MaskPort.Write8NoThrow((byte)(irqMask & 0xff));
                DebugStub.Assert(IoResult.Success == result);
#if PIC_DEBUG
                byte mask0;
                result = pic0MaskPort.Read8(out mask0);
                DebugStub.Assert(IoResult.Success == result);

                byte mask1;
                result = pic1MaskPort.Read8(out mask1);
                DebugStub.Assert(IoResult.Success == result);

                DebugStub.Print("PIC Mask: {0:x2}{1:x2}\n",
                                __arglist(mask1, mask0));
#endif
            }
        }

        [NoHeapAllocation]
        public bool IrqMasked(byte irq)
        {
            if (irq >= PIC_VECTORS) {
                return false;
            }
            return (irqMask & (1u << irq)) != 0;
        }

        private void MaskAll()
        {
            DebugStub.Assert(Processor.InterruptsDisabled());
            pic1MaskPort.Write8(0xff);
            pic0MaskPort.Write8(0xff);
        }

        private void UnmaskAll()
        {
            DebugStub.Assert(Processor.InterruptsDisabled());
            pic1MaskPort.Write8((byte)(irqMask >> 8));
            pic0MaskPort.Write8((byte)(irqMask & 0xff));
        }
    }
}
