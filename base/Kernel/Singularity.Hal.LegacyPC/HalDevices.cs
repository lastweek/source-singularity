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

using System;
using System.Collections;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.Singularity.Hal.Acpi;
using Microsoft.Singularity.Io;

namespace Microsoft.Singularity.Hal
{
    public class HalDevicesLegacyPC : HalDevices
    {
        private static HalDevicesLegacyPC devices;
        private static Pic pic;
        private static Timer8254LegacyPC timer;
        private static PMTimer pmTimer;
        private static RTClockLegacyPC clock;
        private static HalScreenDirect halScreen;

        private static HalMemory halMemory;

        public static HalDevices Create()
        {
            devices = new HalDevicesLegacyPC();

            return devices;
        }

        [CLSCompliant(false)]
        public override void Initialize(Processor rootProcessor)
        {
            DebugStub.Print("HalDevices.Initialize() - Legacy\n");

            pmTimer = AcpiTables.GetPMTimer();

            // PIC
            PnpConfig picConfig
                = (PnpConfig)IoSystem.YieldResources("/pnp/PNP0000", typeof(Pic));
            pic = new Pic(picConfig);
            pic.Initialize();

            // Timer
            PnpConfig timerConfig
                = (PnpConfig)IoSystem.YieldResources("/pnp/PNP0100", typeof(Timer8254LegacyPC));
            timer = new Timer8254LegacyPC(timerConfig, pic);
            byte timerInterrupt = timer.Initialize();

            // Real-time clock
            PnpConfig clockConfig
                = (PnpConfig)IoSystem.YieldResources("/pnp/PNP0B00", typeof(RTClockLegacyPC));
            clock = new RTClockLegacyPC(clockConfig, pic, timer);
            byte clockInterrupt = clock.Initialize();

            bool noisyTimer = false;
            if (pmTimer != null) {
                noisyTimer = CalibrateTimers.Run(pmTimer, timer);
            }
            else {
                CalibrateTimers.Run(clock, timer);
            }

            clock.SetNoisyTimer(noisyTimer);
            clock.Start();

            SystemClock.Initialize(clock, TimeSpan.FromHours(8).Ticks);

            rootProcessor.AddPic(pic);
            rootProcessor.AddTimer(timerInterrupt, timer);
            rootProcessor.AddClock(clockInterrupt, clock);

            // ----------------------------------------------------------
            // Add Srat tables to the Processor
            halMemory = new HalMemorySrat(AcpiTables.GetSrat());
            Processor.AddMemory(halMemory);

            timer.Start();

            // Get the screen resources.  Since we have metadata above to
            // declare all fixed resources used by the screen,
            // YieldResources("") will keep the resource tracking correct:

            halScreen = new HalScreenDirect(IoSystem.YieldResources("", typeof(HalScreen)));
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

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public override void ClearFixedIPI(int interrupt)
        {
        }
    }
}
