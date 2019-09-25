///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: HalDevicesFactory.cs
//
//  Constructs the correct HAL implementation based on system configuation.
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
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity.Hal
{
    [CLSCompliant(false)]
    public sealed class HalDevicesFactory
    {
        public static HalDevices devices = null;

        public static bool apic = false; // True if APIC is present

        public static object Initialize(Processor processor)
        {
            if (processor.Id == 0) {

                 // We have hardware PICS, determine which kind
                 //
                 // Detect if an APIC is present on the CPU
                 //
                 // From 8.4.2 Presence of the Local APIC on page 337 of the
                 // Intel 64 and IA-32 Architectures Software Developers Manual
                 //
                 // function (1) -> eax
                 // cpuid
                 // eax -> p0
                 // ebx -> p1
                 // ecx -> p2
                 // edx -> p3 Bit 9 set if APIC present
                 //
                 //
                 // Note: It has been noted that some older motherboards
                 //       may have an APIC capable processor, but a chipset
                 //       that does not properly support the APIC interrupt
                 //       protocol. These motherboards will remove the APIC
                 //       hardware tables from the ACPI tables as an indication
                 //       that the APIC present on the processor should not
                 //       be used. Of course these are uni-processor only
                 //       motherboards without hyperthreading or multiple-cores.
                 //
                 uint p0, p1, p2, p3;
                 Isa.ReadCpuid((uint)1, out p0, out p1, out p2, out p3);

                 if (((p3 >> 9) & 0x1) != 0) {
                     apic = true;
                     DebugStub.Print("HalDevices: CPUID says APIC present\n");
                 }
                 else {
                     apic = false;
                     DebugStub.Print("HalDevices: CPUID says APIC NOT present\n");
                 }

                 // Dynamically select the proper hardware support drivers
                 if (apic) {
                     devices = HalDevicesApic.Create();
                 }
                 else {
                     devices = HalDevicesLegacyPC.Create();
                 }
            }

            // This happens for all processors
            devices.Initialize(processor);

            return devices;
        }
    }
}

