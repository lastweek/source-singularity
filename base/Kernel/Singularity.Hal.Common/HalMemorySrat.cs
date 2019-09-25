///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//
//
//  Caution:
//

using Microsoft.Singularity.Hal.Acpi;

namespace Microsoft.Singularity.Hal
{
    using System;
    using System.Diagnostics;
    using Microsoft.Singularity.Io;

    [CLSCompliant(false)]
    internal class HalMemorySrat : HalMemory
    {
        // See ProcessorAffinity and MemoryAffinity in the HalMemory.cs

        private static ProcessorAffinity[] processors;
        private static MemoryAffinity[] memories;
        private static bool disabled;

        private Srat srat;

        internal HalMemorySrat(Srat srat)
        {
            this.srat = srat;
            if (srat == null) {
                processors = null;
                memories = null;
                disabled = true;
            }
            else {
                processors = new
                    ProcessorAffinity[srat.GetNumberOfProcessors()];
                memories = new
                    MemoryAffinity [srat.GetNumberOfMemories()];

                for (int i = 0; i < processors.Length; i++) {
                    processors[i].domain = srat.GetProcessorDomain(i);
                    processors[i].apicId = srat.GetProcessorApicId(i);
                    processors[i].flagIgnore = srat.GetProcessorFlagIgnore(i);
                }

                // Some memory addresses may be outside what is addressable by a UIntPtr
                // (e.g. an IX with 32-bit addressing on a machine with more than 4 GB
                // of real memory).  If this happens, disable the feature.
                //
                // TODO: Someone needs to extend this feature to cover that case.
                for (int i = 0; i < memories.Length; i++) {
                    ulong endAddr = srat.GetMemoryEndAddress(i);
                    if (endAddr > (ulong) UIntPtr.MaxValue) {
                        DebugStub.WriteLine("Disabling per-processor memory affinity");
                        memories = null;
                        processors = null;
                        disabled = true;
                        return;
                    }
                    memories[i].domain = srat.GetMemoryDomain(i);
                    memories[i].baseAddress = srat.GetMemoryBaseAddress(i);
                    memories[i].endAddress = endAddr;
                    memories[i].memorySize = srat.GetMemorySize(i);
                    memories[i].flagIgnore = srat.GetMemoryFlagIgnore(i);
                    memories[i].flagHotPluggable =
                        srat.GetMemoryFlagHotPluggable(i);
                    memories[i].flagNonVolatile =
                        srat.GetMemoryFlagNonVolatile(i);
                }
            }
        }

        public override ProcessorAffinity[] GetProcessorAffinity()
        {
            return processors;
        }

        public override MemoryAffinity[] GetMemoryAffinity()
        {
            return memories;
        }

        public override bool PerProcessorAddressSpaceDisabled()
        {
            return disabled;
        }
    }
}
