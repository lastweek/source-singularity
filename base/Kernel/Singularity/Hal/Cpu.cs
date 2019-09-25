// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity.Isal;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;

#if ISA_IX
using Microsoft.Singularity.Isal.IX;
#endif

namespace Microsoft.Singularity.Hal
{
    //
    // Cpu contains per-CPU data structures that HAL sets up.
    //

    [AccessedByRuntime("referenced in c++")]
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential, Pack=4)]
    public class Cpu
    {
        /////////////////////////////////////////////////////////////////////////////////////
        // Boot configuration information: this is all filled out by the loader or another CPU
        //////////////////////////////////////////////////////////////////////////////////

        public Cpu()
        {
        }

        protected Cpu(int id, UIntPtr stackLimit, UIntPtr stackBegin)
        {
            Size = 0;
            Id = id;
            KernelStackLimit = stackLimit;
            KernelStackBegin = stackBegin;
        }

        // Size of instance; this is a versioning/consistency check
        [AccessedByRuntime("referenced in c++")]
        public readonly int        Size;

        // Cpu index
        [AccessedByRuntime("referenced in c++")]
        public readonly int        Id;

        // The HAL is responsible for allocating a page for processor-specific
        // data structures.  This is the address of that page. (Note it must be paragraph aligned.)
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     CpuRecordPage;

        // The HAL is responsible for allocating the kernel stack.  The boundaries
        // are reported here.
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     KernelStackLimit; // lower bounds of stack
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     KernelStackBegin; // upper bounds of stack

        //Is 0 or 1...
        [AccessedByRuntime("referenced in c++")]
        public readonly int         DomainBsp;

        ///// NaticeCpu
#if ISA_IX
        // This is our segment table.
        [AccessedByRuntime("referenced in c++")]
        DescriptorTable                     segments;
#endif

        internal bool halted;

        ///////////////////////////////////////////////////////////////////////
        // Kernel information: initialized by kernel during early boot
        ///////////////////////////////////////////////////////////////////////

        // Low level initialization (no allocation allowed)
        [NoHeapAllocation]
        [AccessedByRuntime("referenced in c++")]
        public unsafe void Initialize()
        {
            if (DomainBsp == 0) {
                Platform.ThePlatform.RegisterCpu(this);
            }

            halted = false;
        }

        // High level intialization (requires object allocation)
        public void InitializeServices()
        {
        }

        // Called from the ISA Target upon interrupt dispatch.
        [NoHeapAllocation]
        public unsafe void DispatchInterrupt(InterruptContext *context)
        {
            Processor p = Processor.CurrentProcessor;
            int interrupt = context->ExceptionId;

            // Indicate that we are in an interrupt context.
            Thread target = null;
            Thread current = Processor.GetCurrentThread();

            Kernel.Waypoint(801);

            // Don't generate loads of output for debugger-related interrupts
#if DEBUG_INTERRUPTS
            DebugStub.WriteLine("Int{0:x2}", __arglist(interrupt));
            context->Display();
#endif

            if (Processor.IsSamplingEnabled) {
                if (p.nextSampleIdle == false) {
                    p.Profiler.LogStackTrace(context->InstructionPointer,
                                             context->StackPointer);
                }
                p.nextSampleIdle = false;
            }

            if (halted) {
                p.clock.CpuResumeFromHaltEvent();
                halted = false;
            }

            unchecked {
                if (interrupt != p.clockInterrupt &&
                    interrupt != p.timerInterrupt) {
                    // We don't log the clockInterrupt because of all the spew.
                    Tracing.Log(Tracing.Debug, "Interrupt 0x{0:x}, count={1:x}, eip={2:x} [CC={3:x8}]",
                                (UIntPtr)(uint)interrupt,
                                (UIntPtr)p.interruptCounts[interrupt],
                                (UIntPtr)context->InstructionPointer,
                                (UIntPtr)(uint)Processor.CycleCount);
                }
            }

            Monitoring.Log(Monitoring.Provider.Processor,
                           (ushort)ProcessorEvent.Interrupt, 0,
                           (uint)interrupt, 0, 0, 0, 0);

            if (interrupt == Kernel.HalIpiInterrupt) {
#if DEBUG_IPI
                DebugStub.WriteLine("IPI received 0x{0:x2} on processor {1}",
                                    __arglist(interrupt, p.Id));
#endif // DEBUG_DISPATCH_TIMER
                Platform.ClearFixedIPI(interrupt);
                //p.dispatcher.HandlePreemptionReschedule();

            }
            else if (interrupt == p.timerInterrupt) {
                // Polling on every timer interrupt is EXCEEDINGLY costly
                p.timer.ClearInterrupt();
                p.dispatcher.HandlePreemptionReschedule(p.timer);
            }
            else if (interrupt == p.clockInterrupt) {

                p.clock.ClearInterrupt();
#if DEBUG
                // Check for a debug break.
                if (DebugStub.PollForBreak()) {
                    DebugStub.WriteLine("Debugger ctrl-break after interrupt 0x{0:x2}",
                                        __arglist(interrupt));
                    DebugStub.Break();
                }
#endif // DEBUG
            }
#if ISA_IX
            else if (interrupt == EVectors.GCSynchronization) {

                Platform.ClearFixedIPI(interrupt);

                MpExecution.GCSynchronizationInterrupt();
            }
            else if (interrupt == EVectors.SpuriousInterrupt) {

                // FIXME: identify the source of these isolated interrupts after the
                // warmboot. Ignore them for now.
                DebugStub.WriteLine("Spurious interrupt");
            }
#endif // ISA_IX
            else {
                if (!Platform.InternalInterrupt((byte)interrupt)) {
                    HalPic pic = p.GetPic();

                    DebugStub.Assert(pic != null);

                    pic.ClearInterrupt((byte)interrupt);
                    IoIrq.SignalInterrupt(pic.InterruptToIrq((byte)interrupt));

#if DEBUG_DISPATCH_IO
                    DebugStub.WriteLine("++DispatchInterruptEvent Irq={0:x2}, Thread={1:x8}",
                                        __arglist(pic.InterruptToIrq((byte)interrupt),
                                                  Kernel.AddressOf(target)));
#endif // DEBUG_DISPATCH_IO

                    p.dispatcher.HandleIOReschedule();
                }
                else {
                    // Potentially missed interrupt
                    DebugStub.Break();
                }
            }

#if DEBUG_INTERRUPTS
            DebugStub.WriteLine("(2nd)Int{0:x2}", __arglist(interrupt));
            context->Display();
            if (!Processor.InterruptsDisabled()) {
                DebugStub.WriteLine("        interrupts enabled!!!!!!!");
                DebugStub.Break();
            }
#if DEBUG_DEEPER
            DebugStub.WriteLine("Int{0:x2}", __arglist(interrupt));
            Thread.DisplayAbbrev(ref context, " int end");
#endif
#endif

            // Now swap in the resulting current thread. (Note that this call will not return.)
            Isa.GetCurrentThread()->spill.Resume();
        }
    }
}

