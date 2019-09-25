////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Hal.Acpi;

using System;
using System.Collections;
using System.Diagnostics;
using System.Text;

namespace Microsoft.Singularity.Drivers
{
    [CLSCompliant(false)]
    public class AcpiBus : IBusDevice
    {
        [DriverCategory]
        [Signature("/root/acpi0")]
        [EnumeratesDevice("/acpi/...")]
        class MyConfig : DriverCategoryDeclaration
        {
        }

        private AcpiDevice[]! deviceInfoEntries;
        delegate IoRange IoRangeTransformer(IoRange);

        public AcpiBus(AcpiDevice[]! deviceInfoEntries)
        {
            this.deviceInfoEntries = deviceInfoEntries;
        }

        private static IoRange ProcessExceptions(string deviceId, IoRange resource) {
            // Some Dells like the Dell Precision 490 make the HPET range
            // read-only - but it needs to be read-write.
            if (deviceId == "/pnp/PNP0103" && resource is IoMemoryRange &&
                !((IoMemoryRange)resource).Writable) {
                IoMemoryRange resourceMemoryRange = (IoMemoryRange)resource;
                return new IoMemoryRange(resourceMemoryRange.RangeBase, resourceMemoryRange.RangeLength,
                                         true/*readable*/, true/*writable*/);
            }
            else {
                return resource;
            }
        }

        public void Initialize()
        {
        }

        public void Finalize()
        {
        }

        public PnpConfig! ReportConfig()
        {
            // TODO: What resources does the root ACPI "bus" have? Any?
            return new PnpConfig(new string[] { "" }, new ArrayList());
        }

        private IoConfig! ResourceDescriptorsToIoConfig(string deviceId, ResourceDescriptor[] resourceDescriptors)
        {
            ArrayList resourceList = new ArrayList();
            string[]! ids = new string[1];
            ids[0] = deviceId;

            foreach (ResourceDescriptor resourceDescriptor in resourceDescriptors) {
                if (resourceDescriptor is MemoryRangeDescriptor) {
                    MemoryRangeDescriptor descriptor = (MemoryRangeDescriptor)resourceDescriptor;
                    if (descriptor.ConsumerProducer == ConsumerProducer.Consumes) {
                        // The resource can take on any base address in the range descriptor.Minimum -
                        // descriptor.Maximum. Just use the minimum for now.
                        resourceList.Add(new IoMemoryRange(descriptor.Minimum, descriptor.Length,
                                                           true/*readable*/, descriptor.Writable));
                    }
                }
                else if (resourceDescriptor is IoRangeDescriptor) {
                    IoRangeDescriptor descriptor = (IoRangeDescriptor)resourceDescriptor;
                    if (descriptor.ConsumerProducer == ConsumerProducer.Consumes) {
                        // The resource can take on any base address in the range descriptor.Minimum -
                        // descriptor.Maximum. Just use the minimum for now. We use Access.ReadWrite
                        // since ACPI supplies no information about whether it's writable.
                        resourceList.Add(new IoPortRange((ushort)descriptor.Minimum, (ushort)descriptor.Length,
                                                         Access.ReadWrite));
                    }
                }
                else if (resourceDescriptor is IrqDescriptor) {
                    IrqDescriptor descriptor = (IrqDescriptor)resourceDescriptor;
                    foreach (int interruptNumber in descriptor.InterruptNumbers) {
                        resourceList.Add(new IoIrqRange((byte)interruptNumber, 1));
                    }
                }
                else if (resourceDescriptor is DmaDescriptor) {
                    DmaDescriptor descriptor = (DmaDescriptor)resourceDescriptor;
                    foreach (int dmaChannelNumber in descriptor.DmaChannelNumbers) {
                        resourceList.Add(new IoDmaRange((byte)dmaChannelNumber, 1));
                    }
                }
            }

            ArrayList processedResourceList = new ArrayList();
            foreach (object obj in resourceList) {
                IoRange newResource = (IoRange)ProcessExceptions(deviceId, (IoRange)obj);
                if (newResource != null) {
                    processedResourceList.Add(newResource);
                }
            }

            return new PnpConfig(ids, processedResourceList);
        }

        public SortedList Enumerate()
        {
            SortedList found = new SortedList();

            int node = 0x100;

            foreach (AcpiDevice! deviceInfo in deviceInfoEntries) {
                IoConfig! ioConfig = ResourceDescriptorsToIoConfig(deviceInfo.DeviceId,
                                         (!)deviceInfo.ResourceDescriptors);

                DebugStub.Write("Detected ACPI device ");
                DebugStub.WriteLine(ioConfig.Id);
                System.Text.StringBuilder descriptionBuilder = new System.Text.StringBuilder();
                ioConfig.DumpRanges(descriptionBuilder);
                DebugStub.WriteLine(descriptionBuilder.ToString());

                found.Add(String.Format("/{0,3:x3}", node++), ioConfig);
            }

            return found;
        }
    }
}
