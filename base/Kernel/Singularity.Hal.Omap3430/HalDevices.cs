///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: HalDevices.cs
//
//  Note: This file implements the contract specified in HalDevices.csi which are
//        static methods calling the proper platform specific class at runtime.
//
//        Many of these methods may be called from C++ or ASM code (PIC functions)
//        so they need to be static.
//

using System;
using System.Collections;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;

namespace Microsoft.Singularity.Hal
{
    // Factory class
    [CLSCompliant(false)]
    public sealed class HalDevicesFactory
    {
        public static object Initialize(Processor processor)
        {
            HalDevicesOmap3430 devices = new HalDevicesOmap3430();
            devices.Initialize(processor);
            return devices;
        }
    }

    [CLSCompliant(false)]
    public sealed class HalDevicesOmap3430 : HalDevices
    {
        private static Pic pic;
        private static TimerOmap3430 timer;
        private static HalClockNull clock;
        private static HalScreenNull halScreen;
        private static HalMemoryNull halMemory;

        [CLSCompliant(false)]
        public override void Initialize(Processor rootProcessor)
        {
            DebugStub.Print("HalDevices.Initialize() - ARM\n");

            // PIC
            PnpConfig picConfig
                = (PnpConfig)IoSystem.YieldResources("/arm/ti/3430/INTCPS",
                                                     typeof(Pic));
            pic = new Pic(picConfig);
            pic.Initialize();

            // Timer
            PnpConfig timerConfig
                = (PnpConfig)IoSystem.YieldResources("/arm/ti/3430/GPTIMER1",
                                                     typeof(TimerOmap3430));
            timer = new TimerOmap3430(timerConfig, pic);
            byte timerInterrupt = timer.Initialize();

            // Real-time clock
            clock = new HalClockNull();
            byte clockInterrupt = clock.Initialize();
            bool noisyTimer = false;

            CalibrateTimers.Run(clock, timer);

            SystemClock.Initialize(clock, TimeSpan.FromHours(8).Ticks);

            rootProcessor.AddPic(pic);

            rootProcessor.AddTimer(timerInterrupt, timer);
            rootProcessor.AddClock(clockInterrupt, clock);

            // ----------------------------------------------------------
            // Add Srat tables to the Processor
            halMemory = new HalMemoryNull();
            ProcessorNode.AddMemory(halMemory);

            timer.Start();

            halScreen = new HalScreenNull();
            Console.Screen = (HalScreen)halScreen;
        }

        public override void ReleaseResources()
        {
            clock.ReleaseResources();
            clock = null;

            timer.ReleaseResources();
            timer = null;

            pic.ReleaseResources();
            pic = null;
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override byte GetMaximumIrq()
        {
            return pic.MaximumIrq;
        }

        //
        // Adding and removing interrupts from the Pic.
        //
        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override void EnableIoInterrupt(byte irq)
        {
            pic.EnableIrq(irq);
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override void DisableIoInterrupt(byte irq)
        {
            pic.DisableIrq(irq);
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override bool InternalInterrupt(byte interrupt)
        {
            // Strictly there are no interrupts internal to
            // this Hal instance.  In practice, some hardware seems
            // intent on firing an interrupt even if it is masked.
            //
            // Return true if interrupt appears to be valid but
            // is masked, false otherwise.
            byte irq = pic.InterruptToIrq(interrupt);

#if DEBUG_SPURIOUS
            DebugStub.Break();
#endif

            if (pic.IrqMasked(irq) == true) {
                DebugStub.WriteLine("--- Acked spurious Irq={0:x2}", __arglist(irq));
                pic.AckIrq(irq);
                return true;
            }
            return false;
        }

        [NoHeapAllocation]
        public override int GetProcessorCount()
        {
            return 1;
        }

        public override void StartApProcessors(int cpus)
        {
        }

        [NoHeapAllocation]
        public override void ResetApProcessors()
        {
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override void FreezeProcessors()
        {
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override void SendFixedIPI(byte vector, int from, int to)
        {
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override void BroadcastFixedIPI(byte vector, bool includeSelf)
        {
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override void ClearFixedIPI(int interrupt)
        {
        }

        public override byte TranslatePciInterrupt(byte currentInterruptLine,
                                                   byte pciInterruptPin,
                                                   PciPort pciPort)
        {
            //
            // On a non-ACPI PC, there's nothing to translate;
            // just return the current interrupt line.
            //
            return currentInterruptLine;
        }
    }
}

