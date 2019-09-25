///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

// Because ARM compiles out ACPI support, we need to stub out the mandatory
// classes declared in the HAL interface here.

namespace Microsoft.Singularity.Hal.Acpi
{
    public class AcpiTables
    {
        public static void Parse() {
        }

        public static AcpiDevice[] LoadDevices() {
            return new AcpiDevice[0];
        }
    }

    public class AcpiDevice
    {
        public string DeviceId {
            get {
                return "";
            }
        }

        public ResourceDescriptor[] ResourceDescriptors {
            get {
                return new ResourceDescriptor[0];
            }
        }
    }

    public enum ConsumerProducer
    {
        ProducesAndConsumes = 0,
        Consumes = 1
    }

    public abstract class ResourceDescriptor
    {
    }

    public class AddressSpaceDescriptor : ResourceDescriptor
    {
        public ulong Minimum {
            get {
                return 0;
            }
        }

        public ulong Maximum {
            get {
                return 0;
            }
        }

        public ulong Length {
            get {
                return 0;
            }
        }

        public ConsumerProducer ConsumerProducer {
            get {
                return ConsumerProducer.Consumes;
            }
        }
    }

    public class MemoryRangeDescriptor : AddressSpaceDescriptor
    {
        public bool Writable {
            get {
                return true;
            }
        }
    }

    public class IoRangeDescriptor : AddressSpaceDescriptor
    {
    }

    public class IrqDescriptor : ResourceDescriptor
    {
        public int[] InterruptNumbers {
            get {
                return new int[0];
            }
        }
    }

    public class DmaDescriptor : ResourceDescriptor
    {
        public int[] DmaChannelNumbers {
            get {
                return new int[0];
            }
        }
    }

    public class GenericRegisterDescriptor : ResourceDescriptor
    {
    }

    public class VendorDefinedDescriptor : ResourceDescriptor
    {
    }
}
