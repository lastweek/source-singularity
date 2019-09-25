///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: HalDevices.cs
//
//  Note:
//

// #define DEBUG_PCI_INTERRUPT_TRANSLATION

using System;
using System.Collections;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Hal.Acpi;
using Microsoft.Singularity.Io;

namespace Microsoft.Singularity.Hal
{
    // Lockstep states for MP initialization.  The bootstrap
    // processor (BSP) sets states beginning Bsp and the
    // upcoming Application Processor (AP) sets states beginning
    // with Ap.
    internal enum MpSyncState : int
    {
        BspWaitingForAp             = 0,
        ApOnline                    = 1,
        BspWaitingForApCalibration  = 2,
        ApCalibrationDone           = 3,
        BspWaitingApRunning         = 6,
        ApRunning                   = 7
    }

    [CLSCompliant(false)]
    public sealed class HalDevicesApic : HalDevices
    {
        private const byte PicBaseVector  = 0x60;
        private const byte ApicBaseVector = 0x70;

        private static IoApic [] ioApics;

        private static HalDevicesApic devices;
        private static HalClockApic   halClock;
        private static ApicTimer      halTimer;
        private static Apic           halPic;

        private static PicStub   pic;       // for squelching pic interrupts

        private static PMTimer   pmTimer;
        private static Timer8254Apic stallTimer;

        private static RTClockApic   rtClock;

        private static HalMemory halMemory;

        private static int processorCount;

        private static volatile MpSyncState mpSyncState;

        private static HalScreenDirect halScreen;

        public static HalDevices Create()
        {
            devices = new HalDevicesApic();

            return devices;
        }

        private void InitializeBsp(Processor rootProcessor)
        {
            DebugStub.Print("HalDevicesApic.Initialize()\n");

            pmTimer = AcpiTables.GetPMTimer();

            // Get PIC resources.  Pic is masked by default.
            PnpConfig picConfig
                = (PnpConfig)IoSystem.YieldResources("/pnp/PNP0000", typeof(PicStub));
            pic = new PicStub(picConfig);
            pic.Initialize(PicBaseVector);

            // Parse MP Table and create IO apics
            MpResources.ParseMpTables();
            ioApics = IoApic.CreateIOApics();

            halPic = new Apic(ioApics);
            halPic.Initialize(ApicBaseVector);

            // Apic timer is used to provide one-shot timer interrupts.
            halTimer = new ApicTimer(halPic);
            halTimer.Initialize();

            // Calibrate timers
            Calibrate.CpuCycleCounter(pmTimer);
            Calibrate.ApicTimer(pmTimer, halTimer);

            // Legacy timer is used to time stalls when starting CPUs.
            PnpConfig i8254Config
                = (PnpConfig)IoSystem.YieldResources("/pnp/PNP0100", typeof(Timer8254Apic));
            stallTimer = new Timer8254Apic(i8254Config);

            // Real-time clock
            PnpConfig rtClockConfig
                = (PnpConfig)IoSystem.YieldResources("/pnp/PNP0B00", typeof(RTClockApic));
            rtClock = new RTClockApic(rtClockConfig, halPic);

            // Compose our HalClock from the component clocks we have available
            halClock = new HalClockApic(halPic, rtClock, new PMClock(pmTimer));

            SystemClock.Initialize(halClock, TimeSpan.FromHours(8).Ticks);

            rootProcessor.AddPic(halPic);

            rootProcessor.AddTimer(halTimer.Interrupt, halTimer);
            rootProcessor.AddClock(halClock.Interrupt, halClock);

            InitializeProcessorCount();
            DebugReportProcessors();

            halTimer.Start();

            // Get the screen resources.  Since we have metadata above to
            // declare all fixed resources used by the screen,
            // YieldResources("") will keep the resource tracking correct:

            halScreen = new HalScreenDirect(IoSystem.YieldResources("", typeof(HalScreen)));
            Console.Screen = (HalScreen)halScreen;

            halPic.DumpState();
            foreach (IoApic ioApic in ioApics) {
                ioApic.DumpRedirectionEntries();
            }
            pic.DumpRegisters();
        }

        private void InitializeAp(Processor processor)
        {
//            Thread.BindKernelThread(nextKernelThread,
//                                    nextKernelStackBegin,
//                                    nextKernelStackLimit);

            // Fleeting check that allocator works.
            Object o = new Object();
            if (o == null)
                DebugStub.Break();

            halPic.Initialize();
            halTimer.Initialize();
            processor.AddPic(halPic);
            processor.AddTimer(halTimer.Interrupt, halTimer);
            processor.AddClock(halClock.Interrupt, halClock);

            SetMpSyncState(MpSyncState.ApOnline);
            WaitForMpSyncState(MpSyncState.BspWaitingForApCalibration);

            // Calibrate timers
            ulong t1 = Processor.CycleCount;
            Calibrate.CpuCycleCounter(pmTimer);
            Calibrate.ApicTimer(pmTimer, halTimer);
            ulong t2 = Processor.CycleCount;
            Tracing.Log(Tracing.Audit, "Calibration time {0}",
                        new UIntPtr((uint)(t2 - t1)));

            SetMpSyncState(MpSyncState.ApCalibrationDone);

            bool success = false;
            WaitForMpSyncState(MpSyncState.BspWaitingApRunning, 100000,
                               ref success);

            SetMpSyncState(MpSyncState.ApRunning);

            halTimer.Start();
        }

        public override void Initialize(Processor processor)
        {
            Cpu thisCpu = (Cpu) Platform.CurrentCpu;
            if (processor.Id == 0) {
                InitializeBsp(processor);

                IoSystem.RegisterKernelDriver(
                    typeof(HpetResources),
                    new IoDeviceCreate(Hpet.CreateDevice)
                    );
            }
            else {
                InitializeAp(processor);
            }
        }

        public override void ReleaseResources()
        {
            rtClock.ReleaseResources();
            rtClock = null;

            halTimer.ReleaseResources();
            halTimer = null;

            halPic.ReleaseResources();
            halPic = null;

            pic.ReleaseResources();
            pic = null;
        }

        [NoHeapAllocation]
        public override bool InternalInterrupt(byte interrupt)
        {
            if (interrupt >= PicBaseVector && interrupt < ApicBaseVector) {
                // Spurious PIC interrupt.
                // Appears to happen once on test boards even though PIC
                // is masked out and no interrupt was raised before masking.
                pic.DumpRegisters();
                pic.AckIrq((byte) (interrupt - PicBaseVector));
                return true;
            }
            return false;
        }

        [NoHeapAllocation]
        internal static void StallProcessor(uint microseconds)
        {
            ulong todo = microseconds *
                (Processor.CyclesPerSecond / 1000000);
            ulong last = Processor.CycleCount;
            ulong elapsed = 0;

            while (elapsed < todo) {
                // Keep track of how much time has elapsed.
                ulong now  = Processor.CycleCount;
                elapsed   += (now - last);
                last       = now;
            }
        }

        internal static void SwitchToHpetClock(Hpet hpet)
        {
            DebugStub.WriteLine("Switching to HPET clock");
            halClock.SwitchToHpetClock(
                new HpetClock(hpet, (ulong)halClock.GetKernelTicks() + 1000u)
                );
        }

        [Conditional("SINGULARITY_MP")]
        [NoHeapAllocation]
        private static void SetMpSyncState(MpSyncState newState)
        {
            Tracing.Log(Tracing.Debug, "Changing MP sync state {0} -> {1}",
                        (uint)mpSyncState, (uint)newState);
            mpSyncState = newState;
        }

        [Conditional("SINGULARITY_MP")]
        [NoHeapAllocation]
        private static void WaitForMpSyncState(MpSyncState newState,
                                               uint microseconds,
                                               ref bool success)
        {
            Tracing.Log(
                Tracing.Debug,
                "Waiting for MP sync state {0} -> {1} ({2} microseconds)",
                (uint)mpSyncState, (uint)newState, microseconds
                );

            ulong todo = microseconds * (Processor.CyclesPerSecond / 1000000);
            ulong last = Processor.CycleCount;
            ulong elapsed = 0;

            success = false;

            while (elapsed < todo) {
                ulong now  = Processor.CycleCount;
                elapsed   += (now - last);
                last       = now;
                if (HalDevicesApic.mpSyncState == newState) {
                    success = true;
                    return;
                }
            }
            Tracing.Log(Tracing.Debug, "Mp sync state timed out");
        }

        [Conditional("SINGULARITY_MP")]
        [NoHeapAllocation]
        private static void WaitForMpSyncState(MpSyncState newState)
        {
            Tracing.Log(
                Tracing.Debug,
                "Waiting for MP sync state {0} -> {1} (indefinite)",
                (uint)mpSyncState, (uint)newState
                );
            while (HalDevicesApic.mpSyncState != newState)
                ;
        }

        [NoHeapAllocation]
        public override byte GetMaximumIrq()
        {
            return halPic.MaximumIrq;
        }

        //
        // Adding and removing interrupts from the Pic.
        //
        [NoHeapAllocation]
        public override void EnableIoInterrupt(byte irq)
        {
            halPic.EnableIrq(irq);
        }

        [NoHeapAllocation]
        public override void DisableIoInterrupt(byte irq)
        {
            halPic.DisableIrq(irq);
        }

        private void InitializeProcessorCount()
        {
            Madt madt = AcpiTables.GetMadt();
            if (madt != null) {
                processorCount = madt.GetLocalApics().Count;
            }
            else if (MpResources.ProcessorEntries != null) {
                processorCount = MpResources.ProcessorEntries.Count;
            }
            else {
                processorCount = 1;
            }

            //
            // Platform.ThePlatform.CpuRealCount was setup by
            // the boot loader and should be the same that we read here.
            //
            DebugStub.Assert(Platform.ThePlatform.CpuRealCount == processorCount);
        }

        //
        // This returns the available physical processors, which may be more
        // than the actual processors started.
        //
        [NoHeapAllocation]
        public override int GetProcessorCount()
        {
            return processorCount;
        }

        private static void DebugReportProcessors()
        {
#if SINGULARITY_MP
            string kernelType = "Multi";
#else
            string kernelType = "Uni";
#endif
            DebugStub.Print("{0}processor kernel on {1} processor system.\n",
                            __arglist(kernelType, devices.GetProcessorCount()));
        }

        [Conditional("SINGULARITY_MP")]
        [NoHeapAllocation]
        private static void AnnounceApFail(int nextCpu)
        {
            MpSyncState localMpState = mpSyncState;
            DebugStub.Print("MpState {0}", __arglist(localMpState));
            DebugStub.Break();
            Platform bi = Platform.ThePlatform;
            DebugStub.Print("Cpu {0} failed. ",
                            __arglist(nextCpu));
            DebugStub.Print("GotBack-> Status {0} Count {1:x8}\n",
                            __arglist(bi.MpStatus32, bi.MpCpuCount));
        }

        //
        // CPU's specifies the limit of the number of processors we will
        // start since they may have been limited from the command line.
        //
        [Conditional("SINGULARITY_MP")]
        //        [NoHeapAllocation]
        private static void StartApProcessorsInternal(int cpus)
        {
            // Kernel thread stack variables
            Thread  nextKernelThread;
            UIntPtr nextKernelStackBegin;
            UIntPtr nextKernelStackLimit;

            //
            // We fire up all processors unless limited by the
            // cpus argument. They are started sequentially and
            // serialize on a spin lock in low memory.
            //
            int expectedCpus = devices.GetProcessorCount();

            DebugStub.Assert(cpus <= expectedCpus);

            //
            // cpus may be less than the real expected CPU's due to
            // the command line argument passed to Main()
            //
            if (cpus < expectedCpus) {
                expectedCpus = cpus;
            }

            // If only 1 cpu, we are done
            if (cpus == 1) {
                return;
            }

            int nextCpu      = 1;

            int nextCpuRealId;
            Platform p = Platform.ThePlatform;
            nextCpuRealId = p.ApicId;
            nextCpuRealId++;

            bool en = Processor.DisableInterrupts();
            try {
                do {
                    DebugStub.Print("Starting CPU {0} / {1}\n",
                                    __arglist(nextCpu + 1,
                                              expectedCpus));
                    SetMpSyncState(MpSyncState.BspWaitingForAp);
                    Tracing.Log(Tracing.Audit,
                                "Initializing cpu {0}", (uint)nextCpu);

                    nextKernelThread = Thread.PrepareKernelThread(Processor.processorTable[nextCpu]);

                    Platform.ThePlatform.MpBootInfo.PrepareForCpuStart(nextCpu);

                    nextKernelStackBegin = Platform.ThePlatform.MpBootInfo.KernelStackBegin;
                    nextKernelStackLimit = Platform.ThePlatform.MpBootInfo.KernelStackLimit;

                    //
                    // Set it on the processor object so it may be set when the starting
                    // processor initializes
                    //
                    Processor.processorTable[nextCpu].InitializeKernelThreadState(
                         nextKernelThread, nextKernelStackBegin, nextKernelStackLimit);

                    Tracing.Log(Tracing.Audit,
                                "Starting cpu {0}. Stack start {1:x8} limit {3:x8})\n",
                                new UIntPtr(nextCpu),
                                nextKernelStackBegin,
                                nextKernelStackLimit);

                    DebugStub.WriteLine("Attempting to start cpu real id {0}\n", __arglist(nextCpuRealId));
                    Platform bi = Platform.ThePlatform;
                    halPic.SendSingleStartupIPI((uint)nextCpuRealId, (byte) (bi.MpEnter32 >> 12));
                    nextCpuRealId++;

                    WaitForMpSyncState(MpSyncState.ApOnline);

                    SetMpSyncState(MpSyncState.BspWaitingForApCalibration);

                    WaitForMpSyncState(MpSyncState.ApCalibrationDone);

                    SetMpSyncState(MpSyncState.BspWaitingApRunning);
                    WaitForMpSyncState(MpSyncState.ApRunning);
                    Processor.RestoreInterrupts(en);
                    en = false;

                    DebugStub.Print("Cpu {0} running ({1} remaining).\n",
                                    __arglist(nextCpu,
                                              expectedCpus - nextCpu - 1));
                } while (++nextCpu < expectedCpus);

                DebugStub.Print("Done.");

                Platform np = Platform.ThePlatform;
            }
            finally {
                DebugStub.Print("Reached finally block in StartApProcessorsInternal()");
                Processor.RestoreInterrupts(en);
            }
        }

        //        [NoHeapAllocation]
        public override void StartApProcessors(int cpus)
        {
            if (GetProcessorCount() > 1) {
                StartApProcessorsInternal(cpus);
            }
        }

        //
        // Reset the Ap processors so there is no way they will be woken
        // up by a debug NMI while in the processor of shutdown/warmboot.
        //
        [NoHeapAllocation]
        public override void ResetApProcessors()
        {
            //
            // Send SIPI to reset them back to real mode with everything
            // flushed and spinning in the BIOS and not OS or OS boot loader
            // code.
            //
            halPic.BroadcastResetIPI();
        }

        //
        // This is a NMI freeze for the debugger
        //
        [NoHeapAllocation]
        public override void FreezeProcessors()
        {
            halPic.BroadcastFreezeIPI();
        }

        [NoHeapAllocation]
        public override void SendFixedIPI(byte vector, int from, int to)
        {
            halPic.SendFixedIPI(vector, from, to);
        }

        [NoHeapAllocation]
        public override void BroadcastFixedIPI(byte vector, bool includeSelf)
        {
            halPic.BroadcastFixedIPI(vector, includeSelf);
        }

        [NoHeapAllocation]
        public override void ClearFixedIPI(int interrupt)
        {
            // Native does not need the interrupt parameter
            halPic.ClearFixedIPI(interrupt);
        }

        public override byte TranslatePciInterrupt(byte currentInterruptLine,
                                                   byte pciInterruptPin,
                                                   PciPort pciPort)
        {
            //
            // The pin number in the tables is zero based, while the pin number
            // from the PCI config space is 1-based.  So convert to the table space.
            //
            pciInterruptPin -= 1;

#if DEBUG_PCI_INTERRUPT_TRANSLATION
            DebugStub.Print("HalApic: Translating interrupt for PCI device 0x{0:x} pin {1} on Bus 0x{2:x}\n",
                __arglist(pciPort.Device, pciInterruptPin, pciPort.Bus));
#endif

            //
            // By default, if we can't find the device, we'll return the current
            // interrupt line.
            //
            byte resultLine = currentInterruptLine;

            foreach (MpInterruptEntry interruptEntry in MpResources.IoInterruptEntries)
            {
#if DEBUG_PCI_INTERRUPT_TRANSLATION
                DebugStub.Print("Found interrupt entry bus 0x{0:x} busIrq 0x{1:x} => ApicId 0x{2:x} ApicLine 0x{3:x}\n",
                    __arglist(interruptEntry.BusId,
                              interruptEntry.BusIrq,
                              interruptEntry.ApicId,
                              interruptEntry.ApicLine));
#endif

                //
                // According to the MPS spec: for PCI buses, the bus IRQ in the table entry
                // contains the pin in the low two bits, and the device number in the next
                // five bits (and the rest are reserved).
                //
                if ((interruptEntry.BusId == pciPort.Bus) &&
                    ((interruptEntry.BusIrq & 3) == pciInterruptPin) &&
                    (((interruptEntry.BusIrq >> 2) & ((1 << 5) - 1)) == pciPort.Device))
                {
#if DEBUG_PCI_INTERRUPT_TRANSLATION
                    DebugStub.Print("Found device 0x{0:x} connected to IoApic Id 0x{1:x}, line 0x{2:x}\n",
                        __arglist(pciPort.Device, interruptEntry.ApicId, interruptEntry.ApicLine));
#endif

                    //
                    // And then we need to translate it into a global interrupt number.
                    //

                    foreach (Acpi.IoApic ioApic in AcpiTables.GetMadt().GetIoApics())
                    {
#if DEBUG_PCI_INTERRUPT_TRANSLATION
                        DebugStub.Print("Found IoApic 0x{0:x}, interrupt base 0x{1:x}\n",
                            __arglist(ioApic.Id, ioApic.InterruptBase));
#endif

                        if (ioApic.Id == interruptEntry.ApicId)
                        {
                            resultLine = (byte)(ioApic.InterruptBase + interruptEntry.ApicLine);
#if DEBUG_PCI_INTERRUPT_TRANSLATION
                            DebugStub.Print("Using global interrupt line 0x{0:x}\n",
                                __arglist(resultLine));
#endif

                            return resultLine;
                        }
                    }

                    break;
                }
            }

#if DEBUG_PCI_INTERRUPT_TRANSLATION
            DebugStub.Print("HalApic: Translated PCI device 0x{0:x} pin {1} on bus 0x{2:x} to global interrupt 0x{3:x}\n",
                __arglist(pciPort.Device, pciInterruptPin, pciPort.Bus, resultLine));
#endif
            return resultLine;
        }
    }
}
