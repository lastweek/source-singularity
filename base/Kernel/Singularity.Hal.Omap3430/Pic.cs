////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Pic.cs
//

#define DEBUG_INTERRUPTS
#define DEBUG_DISPATCH_IO
#define PIC_DEBUG

using Microsoft.Singularity.Io;

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Isal.Arm;

namespace Microsoft.Singularity.Hal
{
    // declare resources for the kernel manifest
    [DriverCategory]
    [Signature("/arm/ti/3430/INTCPS")]
    public sealed class PicResources : DriverCategoryDeclaration
    {
        [IoMemoryRange(0, Default = 0x48200000, Length = 0x1000)]
        internal readonly IoMemoryRange registers;

        // CTR will create the rest of this class:
        public PicResources(IoConfig config)
        {
            // dynamic resources
            registers = (IoMemoryRange)config.DynamicRanges[0];
        }
    }

    [CLSCompliant(false)]
    public sealed class Pic : HalPic
    {
        // size of register block
        const int PicRegisterSize          = 0x00000280; // size of registers in block

        // registers
        const uint INTCPS_REVISION         = 0x00000000; // INTCPS block revision
        const uint INTCPS_SYSCONFIG        = 0x00000010; // configuration
        const uint INTCPS_SYSSTATUS        = 0x00000014; // status
        const uint INTCPS_SIR_IRQ          = 0x00000040; // IRQ source interrupt
        const uint INTCPS_SIR_FIQ          = 0x00000044; // FIQ source interrupt
        const uint INTCPS_CONTROL          = 0x00000048; // control
        const uint INTCPS_PROTECTION       = 0x0000004c; // pic access control
        const uint INTCPS_IDLE             = 0x00000050; // clock idling
        const uint INTCPS_IRQ_PRIORITY     = 0x00000060; // IRQ priority level
        const uint INTCPS_FIQ_PRIORITY     = 0x00000064; // FIQ priority level
        const uint INTCPS_THRESHHOLD       = 0x00000068; // priority threshold control
        const uint INTCPS_ITR              = 0x00000080; // raw interrupt status vector
        const uint INTCPS_MIR              = 0x00000084; // interrupt mask vector
        const uint INTCPS_MIR_CLEAR        = 0x00000088; // clear interrupt mask vector
        const uint INTCPS_MIR_SET          = 0x0000008c; // set interrupt mask vector
        const uint INTCPS_ISR_SET          = 0x00000090; // assert software interrupt vector
        const uint INTCPS_ISR_CLEAR        = 0x00000094; // clear software interrupt vector
        const uint INTCPS_PENDING_IRQ      = 0x00000098; // pending (masked) IRQ interrupt vector
        const uint INTCPS_PENDING_FIQ      = 0x0000009c; // pending (masked) FIQ interrupt vector
        const uint INTCPS_ILR_Base         = 0x00000100; // interrupt priority & fast/slow control
        const uint INTCPS_ILR_Offset       = 0x00000004; // interrupt priority & fast/slow control

        // source interrupt fields
        const uint INTCPS_SIR_IRQ_ACTIVEIRQ_Mask   = 0x0000007f; // active IRQ number
        const uint INTCPS_SIR_FIQ_ACTIVEFIQ_Mask   = 0x0000007f; // active FIQ number

        // interrupt priority fields
        const uint INTCPS_IRQ_PRIORITY_Mask     = 0x0000003f; // current irq priority
        const uint INTCPS_FIQ_PRIORITY_Mask     = 0x0000003f; // current fiq priority

        // interrupt level/routing fields
        const uint INTCPS_ILR_FIQNIRQ           = 0x00000001; // FIQ/IRQ routing
        const uint INTCPS_ILR_PRIORITY_Mask     = 0x0000000d; // interrupt priority
        const int INTCPS_ILR_PRIORITY_Shift     = 0x00000002; // interrupt priority

        // registers
        private IoMappedPort intcps_revision;       // INTCPS block revision
        private IoMappedPort intcps_sysconfig;      // configuration
        private IoMappedPort intcps_sysstatus;      // status
        private IoMappedPort intcps_sir_irq;        // IRQ source interrupt
        private IoMappedPort intcps_sir_fiq;        // FIQ source interrupt
        private IoMappedPort intcps_control;        // control
        private IoMappedPort intcps_protection;     // pic access control
        private IoMappedPort intcps_idle;           // clock idling
        private IoMappedPort intcps_irq_priority;   // IRQ priority level
        private IoMappedPort intcps_fiq_priority;   // FIQ priority level
        private IoMappedPort intcps_threshhold;     // priority threshold control
        private IoMappedPort[] intcps_itr;          // raw interrupt status vector
        private IoMappedPort[] intcps_mir;          // interrupt mask vector
        private IoMappedPort[] intcps_mir_clear;    // clear interrupt mask vector
        private IoMappedPort[] intcps_mir_set;      // set interrupt mask vector
        private IoMappedPort[] intcps_isr_set;      // assert software interrupt vector
        private IoMappedPort[] intcps_isr_clear;    // clear software interrupt vector
        private IoMappedPort[] intcps_pending_irq;  // pending (masked) IRQ interrupt vector
        private IoMappedPort[] intcps_pending_fiq;  // pending (masked) FIQ interrupt vector
        private IoMappedPort intcps_ilr;            // interrupt level/routing

        // constants for PIC interrupt vectors
        const byte INTCPS_Vectors          = 0x60; // count of OMAP3430 interrupt vectors
        const byte INTCPS_Subvector_Size   = 0x20; // size of sub-vectors

        private uint irqMask0; // copy of interrupt mask
        private uint irqMask1; // copy of interrupt mask
        private uint irqMask2; // copy of interrupt mask

        internal Pic(PnpConfig config)
        {
            PicResources pr = new PicResources(config);

            IoMemoryRange range = pr.registers;
            IoMemory regs = range.MemoryAtOffset(0, PicRegisterSize, Access.ReadWrite);

            intcps_revision = regs.MappedPortAtOffset(INTCPS_REVISION, 4, Access.Read);
            intcps_sysconfig = regs.MappedPortAtOffset(INTCPS_SYSCONFIG, 4, Access.ReadWrite);
            intcps_sysstatus = regs.MappedPortAtOffset(INTCPS_SYSSTATUS, 4, Access.Read);
            intcps_sir_irq = regs.MappedPortAtOffset(INTCPS_SIR_IRQ, 4, Access.Read);
            intcps_sir_fiq = regs.MappedPortAtOffset(INTCPS_SIR_FIQ, 4, Access.Read);
            intcps_control = regs.MappedPortAtOffset(INTCPS_CONTROL, 4, Access.ReadWrite);
            intcps_protection = regs.MappedPortAtOffset(INTCPS_PROTECTION, 4, Access.ReadWrite);
            intcps_idle = regs.MappedPortAtOffset(INTCPS_IDLE, 4, Access.ReadWrite);
            intcps_irq_priority = regs.MappedPortAtOffset(INTCPS_IRQ_PRIORITY, 4, Access.ReadWrite);
            intcps_fiq_priority = regs.MappedPortAtOffset(INTCPS_FIQ_PRIORITY, 4, Access.ReadWrite);
            intcps_threshhold = regs.MappedPortAtOffset(INTCPS_THRESHHOLD, 4, Access.ReadWrite);
            intcps_itr = CreatePortVector(regs, INTCPS_ITR, Access.Read);
            intcps_mir = CreatePortVector(regs, INTCPS_MIR, Access.ReadWrite);
            intcps_mir_clear = CreatePortVector(regs, INTCPS_MIR_CLEAR, Access.Write);
            intcps_mir_set = CreatePortVector(regs, INTCPS_MIR_SET, Access.Write);
            intcps_isr_set = CreatePortVector(regs, INTCPS_ISR_SET, Access.ReadWrite);
            intcps_isr_clear = CreatePortVector(regs, INTCPS_ISR_CLEAR, Access.Write);
            intcps_pending_irq = CreatePortVector(regs, INTCPS_PENDING_IRQ, Access.Read);
            intcps_pending_fiq = CreatePortVector(regs, INTCPS_PENDING_FIQ, Access.Read);
            intcps_ilr = regs.MappedPortAtOffset(
                INTCPS_ILR_Base,
                INTCPS_ILR_Offset * INTCPS_Vectors,
                Access.ReadWrite
                );
        }

        private static IoMappedPort[] CreatePortVector(IoMemory regs, uint offset, Access access)
        {
            return new IoMappedPort[3] {
                regs.MappedPortAtOffset(offset + 0x00, 4, access),
                regs.MappedPortAtOffset(offset + 0x20, 4, access),
                regs.MappedPortAtOffset(offset + 0x40, 4, access)
            };
        }

        public void Initialize()
        {
            DebugStub.WriteLine("Pic.Initializing IRQs");

            // mask all interrupts
            MaskAll();

            // clear all pending interrupts
            intcps_isr_clear[0].Write32(0xffffffff);
            intcps_isr_clear[1].Write32(0xffffffff);
            intcps_isr_clear[2].Write32(0xffffffff);
        }

        public void Finalize()
        {
            UnmaskAll();
        }

        [NoHeapAllocation]
        public override byte InterruptToIrq(byte interrupt)
        {
            DebugStub.WriteLine("Pic.InterruptToIrq({0})", __arglist(interrupt));
            // hack - all h/w interrupts on ARM are routed through a common vector
            DebugStub.Assert((interrupt == ExceptionVector.Fiq) ||
                             (interrupt == ExceptionVector.Irq));

            IoResult result = IoResult.Success;

            if (interrupt == ExceptionVector.Fiq) {

                // read currently active FIQ
                ushort sir = intcps_sir_fiq.Read16NoThrow(ref result);
                return (byte)(sir & INTCPS_SIR_FIQ_ACTIVEFIQ_Mask);

            }
            else { // if (interrupt == ExceptionVector.Irq)

                // read currently active IRQ
                ushort sir = intcps_sir_irq.Read16NoThrow(ref result);
                return (byte)(sir & INTCPS_SIR_IRQ_ACTIVEIRQ_Mask);
            }
        }

        [NoHeapAllocation]
        public override byte IrqToInterrupt(byte irq)
        {
            DebugStub.WriteLine("Pic.IrqToInterrupt({0})", __arglist(irq));
            // range check
            DebugStub.Assert(irq < INTCPS_Vectors);

            // check where the interrupt is routed: IRQ or FIQ
            IoResult result = IoResult.Success;
            uint ilr = intcps_ilr.Read32NoThrow(irq * INTCPS_ILR_Offset, ref result);

            if ((ilr & INTCPS_ILR_FIQNIRQ) != 0) {
                return (byte)ExceptionVector.Fiq;
            }
            else {
                return (byte)ExceptionVector.Irq;
            }
        }

        public override byte MaximumIrq
        {
            [NoHeapAllocation]
            get { return INTCPS_Vectors - 1; }
        }

        [System.Diagnostics.Conditional("PIC_DEBUG")]
        [NoHeapAllocation]
        private void DumpBits(String label, IoMappedPort[] regs)
        {
            IoResult result = IoResult.Success;
            uint v0 = regs[0].Read32NoThrow(ref result);
            uint v1 = regs[1].Read32NoThrow(ref result);
            uint v2 = regs[2].Read32NoThrow(ref result);

            DebugStub.WriteLine(label, __arglist(v0, v1, v2));
        }

        [System.Diagnostics.Conditional("PIC_DEBUG")]
        [NoHeapAllocation]
        private void DumpRegisters()
        {
            IoResult result = IoResult.Success;

            ushort currentIrqNumber = (ushort)(intcps_sir_irq.Read16NoThrow(ref result)
                                               & INTCPS_SIR_IRQ_ACTIVEIRQ_Mask);
            ushort currentIrqPriority = (ushort)(intcps_irq_priority.Read16NoThrow(ref result)
                                                 & (ushort)INTCPS_IRQ_PRIORITY_Mask);
            DebugStub.WriteLine("PIC Current IRQ: {0:x4} Priority: {0:x4}",
                                __arglist(currentIrqNumber, currentIrqPriority));

            ushort currentFiqNumber = (ushort)(intcps_sir_fiq.Read16NoThrow(ref result)
                                               & INTCPS_SIR_FIQ_ACTIVEFIQ_Mask);
            ushort currentFiqPriority = (ushort)(intcps_fiq_priority.Read16NoThrow(ref result)
                                                 & INTCPS_FIQ_PRIORITY_Mask);
            DebugStub.WriteLine("PIC Current FIQ: {0:x4} Priority: {0:x4}",
                                __arglist(currentFiqNumber, currentFiqPriority));

            DumpBits("PIC raw interrupt status: {2:x8}{1:x8}{0:x8}", intcps_itr);
            DumpBits("PIC interrupt mask:       {2:x8}{1:x8}{0:x8}", intcps_mir);
            DumpBits("PIC software interrupts:  {2:x8}{1:x8}{0:x8}", intcps_isr_set);
            DumpBits("PIC pending IRQs:         {2:x8}{1:x8}{0:x8}", intcps_pending_irq);
            DumpBits("PIC pending FIQs:         {2:x8}{1:x8}{0:x8}", intcps_pending_fiq);

            for (uint i = 0; i < INTCPS_Vectors; ++i) {

                uint ilr = intcps_ilr.Read32NoThrow(i * INTCPS_ILR_Offset, ref result);

                string interruptType = ((ilr & INTCPS_ILR_FIQNIRQ) != 0) ? "fiq" : "irq";
                byte priority = (byte)((ilr & INTCPS_ILR_PRIORITY_Mask)
                                       >> INTCPS_ILR_PRIORITY_Shift);

                DebugStub.WriteLine("PIC ILR[{0}]: {1} Priority: {2:x2}",
                                    __arglist(i, interruptType, priority));
            }

            DebugStub.Assert(IoResult.Success == result);
        }

        [NoHeapAllocation]
        public override void ClearInterrupt(byte interrupt)
        {
            byte irq = InterruptToIrq(interrupt);

            Mask(irq);
            AckIrq(irq);
            Unmask(irq);

#if DEBUG_INTERRUPTS
            DebugStub.WriteLine("pic.ClearInterrupt({2:x8}{1:x8}{0:x8})",
                                __arglist(irqMask0, irqMask1, irqMask2));
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
            DebugStub.WriteLine("Int{0:x2}  Acked, Mask={3:x8}{2:x8}{1:x8}",
                                __arglist(irq, irqMask0, irqMask1, irqMask2));
#endif

            // Quiet the interrupt controller.
            IoResult result = IoResult.Success;
            uint n = irq / 32u;
            uint bit = 1u << (irq % 32);
            if (n < intcps_isr_clear.Length) {
                intcps_isr_clear[n].Write32NoThrow(bit, ref result);
            }
            DebugStub.Assert(IoResult.Success == result);

#if PIC_DEBUG
            DumpRegisters();
#endif
        }

        [NoHeapAllocation]
        public override void EnableIrq(byte irq)
        {
            if (irq >= INTCPS_Vectors) {
                DebugStub.Break();
                // throw new OverflowException
                // (String.Format("irq {0} out of range.", irq));
            }

#if DEBUG_INTERRUPTS
            DebugStub.WriteLine("Int{0:x2}  Enable, Mask={3:x8}{2:x8}{1:x8}",
                                __arglist(irq, irqMask0, irqMask1, irqMask2));
#endif

            bool saved = Processor.DisableInterrupts();
            try {
                Unmask(irq);
#if PIC_DEBUG
                DumpRegisters();
#endif
            }
            finally {
                Processor.RestoreInterrupts(saved);
            }
        }

        [NoHeapAllocation]
        public override void DisableIrq(byte irq)
        {
            if (irq >= INTCPS_Vectors) {
                DebugStub.Break();
                //                throw new OverflowException
                // (String.Format("irq {0} out of range.", irq));
            }

#if DEBUG_INTERRUPTS
            DebugStub.WriteLine("Int{0:x2} Disable", __arglist(irq));
#endif
            bool saved = Processor.DisableInterrupts();
            try {
                Mask(irq);
#if PIC_DEBUG
                DumpRegisters();
#endif
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
            uint n = irq / 32u;
            uint bit = 1u << (irq % 32);
#if DEBUG_DISPATCH_IO
            DebugStub.WriteLine("PIC.Mask({0}) => {1:x8}", __arglist(irq, bit));
#endif

            uint mask = GetMaskWord(n);
            if ((mask & bit) == 0) {

#if DEBUG_DISPATCH_IO
                DebugStub.WriteLine("-- Mask IRQs [{0}: old={1:x8} new={2:x8}",
                                    __arglist(n, mask, mask | bit));
#endif
                IoResult result = IoResult.Success;
                intcps_mir_set[n].Write32NoThrow(bit, ref result);
                DebugStub.Assert(IoResult.Success == result);

                SetMaskWord(n, mask | bit);
#if PIC_DEBUG
                DumpBits("-- PIC interrupt mask:    {2:x8}{1:x8}{0:x8}", intcps_mir);
#endif
            }
        }

        [NoHeapAllocation]
        private void Unmask(byte irq)
        {
            DebugStub.Assert(Processor.InterruptsDisabled());
            uint n = irq / 32u;
            uint bit = 1u << (irq % 32);
#if DEBUG_DISPATCH_IO
            DebugStub.WriteLine("PIC.Unmask({0}) => {1:x8}", __arglist(irq, bit));
#endif

            uint mask = GetMaskWord(n);
            if ((mask & bit) != 0) {

#if DEBUG_DISPATCH_IO
                DebugStub.WriteLine("-- Unmask IRQs [{0}: old={1:x8} new={2:x8}",
                                    __arglist(n, mask, mask & ~bit));
#endif
#if false // Enable this to set interrupt without hardware.
                IoResult result = IoResult.Success;
                intcps_mir_clear[n].Write32NoThrow(bit, ref result);
                intcps_isr_set[n].Write32NoThrow(bit, ref result);
                DebugStub.Assert(IoResult.Success == result);
#endif

                SetMaskWord(n, mask & ~bit);
#if PIC_DEBUG
                DumpBits("-- PIC interrupt mask:    {2:x8}{1:x8}{0:x8}", intcps_mir);
#endif
            }
        }

        [NoHeapAllocation]
        public bool IrqMasked(byte irq)
        {
            uint n = irq / 32u;
            uint bit = 1u << (irq % 32);

            if (irq >= INTCPS_Vectors) {
                return true;
            }
            return ((GetMaskWord(n) & bit) != 0);
        }

        [NoHeapAllocation]
        private uint GetMaskWord(uint n)
        {
            switch (n) {
                case 0: return irqMask0;
                case 1: return irqMask1;
                case 2: return irqMask2;
            }
            return 0;
        }

        [NoHeapAllocation]
        private void SetMaskWord(uint n, uint value)
        {
            switch (n) {
                case 0: irqMask0 = value; break;
                case 1: irqMask1 = value; break;
                case 2: irqMask2 = value; break;
            }
        }

        private void MaskAll()
        {
            DebugStub.Assert(Processor.InterruptsDisabled());

            for (int i = 0; i < intcps_mir_set.Length; i++) {
                intcps_mir_set[i].Write32(0xffffffff);
            }
            irqMask0 = irqMask1 = irqMask2 = 0xffffffff;
        }

        private void UnmaskAll()
        {
            DebugStub.Assert(Processor.InterruptsDisabled());

            for (int i = 0; i < intcps_mir_clear.Length; i++) {
                intcps_mir_clear[i].Write32(0xffffffff);
            }
            irqMask0 = irqMask1 = irqMask2 = 0x0;
        }
    }
}

