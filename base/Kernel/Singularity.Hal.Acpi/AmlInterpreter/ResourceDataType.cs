///////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

using System;
using System.Collections;
using System.Diagnostics;
using System.Text;

namespace Microsoft.Singularity.Hal.Acpi
{
    //
    // Based on section 6.4 of ACPI Specification 3.0b, Resource Data Types for ACPI,
    // this class hierarchy describes and parses resource descriptors that can be encoded
    // inside buffers returned by the _CRS, _PRS, and _SRS methods of ACPI objects.
    //

    public enum ConsumerProducer
    {
        ProducesAndConsumes = 0,
        Consumes = 1
    }

    /// <summary>
    /// Small item name tag bits as described in table 6-21 of section
    /// 6.4.2 of the ACPI specification 3.0b.
    /// </summary>
    public enum SmallResourceItemName
    {
        IrqFormatDescriptor = 0x04,
        DmaFormatDescriptor = 0x05,
        StartDependentFunctionsDescriptor = 0x06,
        EndDependentFunctionsDescriptor = 0x07,
        IoPortDescriptor = 0x08,
        FixedLocationIoPortDescriptor = 0x09,
        VendorDefinedDescriptor = 0x0E,
        EndTagDescriptor = 0x0F
    }

    /// <summary>
    /// Large item name tag bits as described in table 6-33 of section
    /// 6.4.2 of the ACPI specification 3.0b.
    /// </summary>
    public enum LargeResourceItemName
    {
        MemoryRangeDescriptor24Bit = 0x01,
        GenericRegisterDescriptor = 0x02,
        VendorDefinedDescriptor = 0x04,
        MemoryRangeDescriptor32Bit = 0x05,
        FixedLocationMemoryRangeDescriptor32Bit = 0x06,
        DwordAddressSpaceDescriptor = 0x07,
        WordAddressSpaceDescriptor = 0x08,
        ExtendedIrqDescriptor = 0x09,
        QwordAddressSpaceDescriptor = 0x0A,
        ExtendedAddressSpaceDescriptor = 0x0B
    }

    public abstract class ResourceDescriptor
    {
        public abstract void Accept(ResourceDescriptorVisitor v);
    }

    public class AddressSpaceDescriptor : ResourceDescriptor
    {
        public enum ResourceType : byte
        {
            MemoryRange = 0,
            IoRange = 1,
            BusNumberRange = 2
        }

        public enum DecodeType
        {
            BridgePositivelyDecodes = 0,
            BridgeSubtractivelyDecodes = 1
        }

        ResourceType resourceType;
        ulong minimum; // _MIN
        ulong maximum; // _MAX
        ulong length; // _LEN
        ulong alignment; // _GRA, _ALN

        bool minimumAddressIsFixed;
        bool maximumAddressIsFixed;
        ulong addressTranslationOffset; // _TRA
        DecodeType decodeType;
        ConsumerProducer consumerProducer;

        public ulong Minimum
        {
            get
            {
                return minimum;
            }
        }

        public ulong Maximum
        {
            get
            {
                return maximum;
            }
        }

        public ulong Length
        {
            get
            {
                return length;
            }
        }

        public ConsumerProducer ConsumerProducer
        {
            get
            {
                return consumerProducer;
            }
        }

        public AddressSpaceDescriptor(ResourceType resourceType, ulong minimum, ulong maximum, ulong length, ulong alignment)
        {
            this.resourceType = resourceType;
            this.minimum = minimum;
            this.maximum = maximum;
            this.length = length;
            this.alignment = alignment;

            this.minimumAddressIsFixed = false;
            this.maximumAddressIsFixed = false;
            this.addressTranslationOffset = 0;
            this.decodeType = DecodeType.BridgePositivelyDecodes;
            this.consumerProducer = ConsumerProducer.Consumes;
        }

        public AddressSpaceDescriptor(ResourceType resourceType, ulong minimum, ulong maximum,
                                      ulong length, ulong alignment, ulong addressTranslationOffset,
                                      bool minimumAddressIsFixed, bool maximumAddressIsFixed,
                                      DecodeType decodeType, ConsumerProducer consumerProducer)
        {
            this.resourceType = resourceType;
            this.minimum = minimum;
            this.maximum = maximum;
            this.length = length;
            this.alignment = alignment;

            this.minimumAddressIsFixed = minimumAddressIsFixed;
            this.maximumAddressIsFixed = maximumAddressIsFixed;
            this.addressTranslationOffset = addressTranslationOffset;
            this.decodeType = decodeType;
            this.consumerProducer = consumerProducer;
        }

        public override void Accept(ResourceDescriptorVisitor v)
        {
            v.Visit(this);
        }
    }

    public class MemoryRangeDescriptor : AddressSpaceDescriptor
    {
        [Flags]
        public enum AcpiMemoryFlags
        {
            None = 0,
            ACPI_MEMORY_UC = 0x0000000000000001,
            ACPI_MEMORY_WC = 0x0000000000000002,
            ACPI_MEMORY_WT = 0x0000000000000004,
            ACPI_MEMORY_WB = 0x0000000000000008,
            ACPI_MEMORY_UCE = 0x0000000000000010,
            ACPI_MEMORY_NV = 0x0000000000008000
        }

        public enum MemoryToIoTranslation
        {
            TypeStatic = 0,
            TypeTranslation = 1
        }

        public enum AddressRangeAttribute
        {
            Memory = 0,
            Reserved = 1,
            Acpi = 2,
            Nvs = 3
        }

        public enum CacheableAttribute
        {
            NonCacheable = 0,
            Cacheable = 1,
            CacheableWithWriteCombining = 2,
            CacheableAndPrefetchable = 3
        }

        public enum WriteStatus
        {
            ReadOnly = 0,
            ReadWrite = 1
        }

        AcpiMemoryFlags acpiMemoryFlags; // _ATT
        MemoryToIoTranslation memoryToIoTranslation; // _TTP
        AddressRangeAttribute addressRangeAttribute; // _MTP
        CacheableAttribute cacheableAttribute; // _MEM
        WriteStatus writeStatus; // _RW

        public bool Writable
        {
            get
            {
                return writeStatus == WriteStatus.ReadWrite;
            }
        }

        public MemoryRangeDescriptor(ulong minimum, ulong maximum, ulong length, ulong alignment, WriteStatus writeStatus)
            : base(AddressSpaceDescriptor.ResourceType.MemoryRange, minimum, maximum, length, alignment)
        {
            this.acpiMemoryFlags = AcpiMemoryFlags.None;
            this.memoryToIoTranslation = MemoryToIoTranslation.TypeStatic;
            this.addressRangeAttribute = AddressRangeAttribute.Memory;
            this.cacheableAttribute = CacheableAttribute.NonCacheable;
            this.writeStatus = writeStatus;
        }

        public MemoryRangeDescriptor(ResourceType resourceType, ulong minimum, ulong maximum,
                                     ulong length, ulong alignment, ulong addressTranslationOffset,
                                     bool minimumAddressIsFixed, bool maximumAddressIsFixed,
                                     DecodeType decodeType, ConsumerProducer consumerProducer,
                                     AcpiMemoryFlags acpiMemoryFlags, MemoryToIoTranslation memoryToIoTranslation,
                                     AddressRangeAttribute addressRangeAttribute,
                                     CacheableAttribute cacheableAttribute, WriteStatus writeStatus)
            : base(resourceType, minimum, maximum, length, alignment, addressTranslationOffset,
                   minimumAddressIsFixed, maximumAddressIsFixed, decodeType, consumerProducer)
        {
            this.acpiMemoryFlags = acpiMemoryFlags;
            this.memoryToIoTranslation = memoryToIoTranslation;
            this.addressRangeAttribute = addressRangeAttribute;
            this.cacheableAttribute = cacheableAttribute;
            this.writeStatus = writeStatus;
        }

        public override void Accept(ResourceDescriptorVisitor v)
        {
            v.Visit(this);
        }
    }

    public class IoRangeDescriptor : AddressSpaceDescriptor
    {
        public enum IoToMemoryTranslation
        {
            TypeStatic,
            TypeTranslationDense,
            TypeTranslationSparse
        }

        IoToMemoryTranslation ioToMemoryTranslation; // _TTP, _TRS combined

        public IoRangeDescriptor(ulong minimum, ulong maximum, ulong length, ulong alignment)
            : base(AddressSpaceDescriptor.ResourceType.IoRange, minimum, maximum, length, alignment)
        {
            this.ioToMemoryTranslation = IoToMemoryTranslation.TypeStatic;
        }

        public IoRangeDescriptor(ResourceType resourceType, ulong minimum, ulong maximum,
                                 ulong length, ulong alignment, ulong addressTranslationOffset,
                                 bool minimumAddressIsFixed, bool maximumAddressIsFixed,
                                 DecodeType decodeType, ConsumerProducer consumerProducer,
                                 IoToMemoryTranslation ioToMemoryTranslation)
            : base(resourceType, minimum, maximum, length, alignment, addressTranslationOffset,
                   minimumAddressIsFixed, maximumAddressIsFixed, decodeType, consumerProducer)
        {
            this.ioToMemoryTranslation = ioToMemoryTranslation;
        }

        public override void Accept(ResourceDescriptorVisitor v)
        {
            v.Visit(this);
        }
    }

    public class IrqDescriptor : ResourceDescriptor
    {
        public enum Polarity
        {
            ActiveHigh = 0,
            ActiveLow = 1
        }
        public enum Mode
        {
            LevelTriggered = 0,
            EdgeTriggered = 1
        }

        int[] interruptNumbers;
        bool sharable; // _SHR
        Polarity polarity; // _LL
        Mode mode; // _HE

        // Extended Interrupt Descriptor-only attributes
        ConsumerProducer consumerProducer;
        string resourceSource;
        byte resourceSourceIndex;

        public IrqDescriptor(int[] interruptNumbers, bool sharable, Polarity polarity, Mode mode)
        {
            this.interruptNumbers = interruptNumbers;
            this.sharable = sharable;
            this.polarity = polarity;
            this.mode = mode;
        }

        public override void Accept(ResourceDescriptorVisitor v)
        {
            v.Visit(this);
        }

        // Make this an ICollection<int> when generics come around
        int[] InterruptNumbers
        {
            get
            {
                return interruptNumbers;
            }
        }
    }

    public class DmaDescriptor : ResourceDescriptor
    {
        public enum ChannelSpeed
        {
            CompatibilityMode = 0,
            TypeA = 1,
            TypeB = 2,
            TypeF = 3
        }

        public enum LogicalDeviceBusMasterStatus
        {
            IsNotBusMaster = 0,
            IsBusMaster = 1
        }

        public enum TransferTypePreference
        {
            Type8BitOnly = 0,
            TypeBoth = 1,
            Type16BitOnly = 2
        }

        int[] dmaChannelNumbers; // _DMA
        ChannelSpeed channelSpeed; // _TYP
        LogicalDeviceBusMasterStatus logicalDeviceBusMasterStatus; // _BM
        TransferTypePreference transferTypePreference; // _SIZ

        public DmaDescriptor(int[] dmaChannelNumbers,
                             ChannelSpeed channelSpeed,
                             LogicalDeviceBusMasterStatus logicalDeviceBusMasterStatus,
                             TransferTypePreference transferTypePreference)
        {
            this.dmaChannelNumbers = dmaChannelNumbers;
            this.channelSpeed = channelSpeed;
            this.logicalDeviceBusMasterStatus = logicalDeviceBusMasterStatus;
            this.transferTypePreference = transferTypePreference;
        }

        public override void Accept(ResourceDescriptorVisitor v)
        {
            v.Visit(this);
        }

        public int[] DmaChannelNumbers
        {
            get
            {
                return dmaChannelNumbers;
            }
        }
    }

    public class GenericRegisterDescriptor : ResourceDescriptor
    {
        public enum AddressSpace
        {
            SystemMemory = 0x00,
            SystemIo = 0x01,
            PciConfigurationSpace = 0x02,
            EmbeddedController = 0x03,
            SmBus = 0x04,
            FunctionalFixedHardware = 0x7F
        }

        public enum AddressSize
        {
            ByteAccess = 1,
            WordAccess = 2,
            DwordAccess = 3,
            QwordAccess = 4
        }

        AddressSpace addressSpace; // _ASI
        byte registerBitWidth; // _RBW
        byte registerBitOffset; // _RBO
        AddressSize addressSize; // _ASZ
        ulong registerAddress; // _ADR

        public GenericRegisterDescriptor(AddressSpace addressSpace, byte registerBitWidth, byte registerBitOffset,
                                         AddressSize addressSize, ulong registerAddress)
        {
            this.addressSpace = addressSpace;
            this.registerBitWidth = registerBitWidth;
            this.registerBitOffset = registerBitOffset;
            this.addressSize = addressSize;
            this.registerAddress = registerAddress;
        }

        public override void Accept(ResourceDescriptorVisitor v)
        {
            v.Visit(this);
        }
    }

    public class VendorDefinedDescriptor : ResourceDescriptor
    {
        Guid uuid;
        byte subtype;
        byte[] data;

        public VendorDefinedDescriptor(byte[] data)
            : this(new Guid(), 0, data) { }

        public VendorDefinedDescriptor(Guid uuid, byte subtype, byte[] data)
        {
            this.uuid = uuid;
            this.subtype = subtype;
            this.data = data;
        }

        public override void Accept(ResourceDescriptorVisitor v)
        {
            v.Visit(this);
        }
    }

    public abstract class ResourceDescriptorVisitor
    {
        public abstract void Visit(AddressSpaceDescriptor descriptor);
        public abstract void Visit(MemoryRangeDescriptor descriptor);
        public abstract void Visit(IoRangeDescriptor descriptor);
        public abstract void Visit(IrqDescriptor descriptor);
        public abstract void Visit(DmaDescriptor descriptor);
        public abstract void Visit(GenericRegisterDescriptor descriptor);
        public abstract void Visit(VendorDefinedDescriptor descriptor);
    }

    public class ResourceDescriptionParseException : Exception
    {
        public ResourceDescriptionParseException()
            : base("Failure parsing ACPI resource description") { }

        public ResourceDescriptionParseException(string str)
            : base("Failure parsing ACPI resource description: " + str) { }
    }

    public class ResourceDescriptorParser
    {
        private class IntList
        {
            ArrayList list = new ArrayList();

            public void Add(int i) {
                list.Add(i);
            }

            public int[] ToArray() {
                return (int[])list.ToArray(typeof(int));
            }
        }

        private class ResourceDescriptorList
        {
            ArrayList list = new ArrayList();

            public void Add(ResourceDescriptor rd) {
                list.Add(rd);
            }

            public ResourceDescriptor[] ToArray() {
                return (ResourceDescriptor[])list.ToArray(typeof(ResourceDescriptor));
            }
        }

        // Expects bytes in little-endian order
        private static UInt16 BuildUInt16(byte[] b, int offset)
        {
            return (ushort)((((ulong)b[offset + 1]) << 8) |
                            (((ulong)b[offset + 0]) << 0));
        }

        // Expects bytes in little-endian order
        private static UInt32 BuildUInt32(byte[] b, int offset)
        {
            return (uint)((((ulong)b[offset + 3]) << 24) |
                          (((ulong)b[offset + 2]) << 16) |
                          (((ulong)b[offset + 1]) << 8) |
                          (((ulong)b[offset + 0]) << 0));
        }

        // Expects bytes in little-endian order
        private static UInt64 BuildUInt64(byte[] b, int offset)
        {
            return (ulong)((((ulong)b[offset + 7]) << 56) |
                           (((ulong)b[offset + 6]) << 48) |
                           (((ulong)b[offset + 5]) << 40) |
                           (((ulong)b[offset + 4]) << 32) |
                           (((ulong)b[offset + 3]) << 24) |
                           (((ulong)b[offset + 2]) << 16) |
                           (((ulong)b[offset + 1]) << 8) |
                           (((ulong)b[offset + 0]) << 0));
        }

        public static ResourceDescriptor[] Parse(byte[] resourceBuffer)
        {
            ResourceDescriptorList result = new ResourceDescriptorList();

            for (int start = 0; start < resourceBuffer.Length; ) {
                if (resourceBuffer.Length < 1) {
                    throw new ArgumentException("resourceBuffer must have length at least 1");
                }
                if ((resourceBuffer[start] & 0x80) == 0) {
                    // Small item
                    int lengthBytes = resourceBuffer[start] & 0x7;

                    switch ((SmallResourceItemName)((resourceBuffer[start] >> 3) & 0x0F)) {
                        case SmallResourceItemName.IrqFormatDescriptor: {
                            Debug.Assert(lengthBytes == 2 || lengthBytes == 3);
                            IntList interruptNumbers = new IntList();
                            for (int i = 0; i < 8; i++) {
                                if ((resourceBuffer[start + 1] & (1 << i)) != 0) {
                                    interruptNumbers.Add(i);
                                }
                                if ((resourceBuffer[start + 2] & (1 << i)) != 0) {
                                    interruptNumbers.Add(i + 8);
                                }
                            }

                            // From spec: "If byte 3 is not included, High true,
                            // edge sensitive, non-shareable is assumed."
                            bool sharable = false;
                            IrqDescriptor.Polarity polarity = IrqDescriptor.Polarity.ActiveHigh;
                            IrqDescriptor.Mode mode = IrqDescriptor.Mode.EdgeTriggered;

                            if (lengthBytes == 3) {
                                byte flags = resourceBuffer[start + 3];
                                sharable = (flags & (1 << 4)) != 0;
                                polarity = (IrqDescriptor.Polarity)((flags >> 3) & 1);
                                mode = (IrqDescriptor.Mode)(flags & 1);
                            }

                            result.Add(new IrqDescriptor(interruptNumbers.ToArray(),
                                                         sharable, polarity, mode));
                            break;
                        }

                        case SmallResourceItemName.DmaFormatDescriptor: {
                            Debug.Assert(lengthBytes == 2);
                            IntList dmaChannelNumbers = new IntList();
                            for (int i = 0; i < 8; i++) {
                                if ((resourceBuffer[start + 1] & (1 << i)) != 0) {
                                    dmaChannelNumbers.Add(i);
                                }
                            }

                            byte flags = resourceBuffer[start + 2];
                            DmaDescriptor.ChannelSpeed channelSpeed =
                                (DmaDescriptor.ChannelSpeed)((flags >> 5) & 0x3);
                            DmaDescriptor.LogicalDeviceBusMasterStatus logicalDeviceBusMasterStatus =
                                (DmaDescriptor.LogicalDeviceBusMasterStatus)((flags >> 2) & 0x1);
                            DmaDescriptor.TransferTypePreference transferTypePreference =
                                (DmaDescriptor.TransferTypePreference)(flags & 0x3);

                            result.Add(new DmaDescriptor(dmaChannelNumbers.ToArray(),
                                                         channelSpeed, logicalDeviceBusMasterStatus, transferTypePreference));
                            break;
                        }

                        case SmallResourceItemName.StartDependentFunctionsDescriptor:
                            throw new ResourceDescriptionParseException("Unimplemented ACPI resource descriptor");

                        case SmallResourceItemName.EndDependentFunctionsDescriptor:
                            throw new ResourceDescriptionParseException("Unimplemented ACPI resource descriptor");

                        case SmallResourceItemName.IoPortDescriptor: {
                            UInt16 minimum = BuildUInt16(resourceBuffer, start + 2);
                            UInt16 maximum = BuildUInt16(resourceBuffer, start + 4);
                            byte alignment = resourceBuffer[start + 6];
                            byte length = resourceBuffer[start + 7];
                            result.Add(new IoRangeDescriptor(minimum, maximum, length, alignment));
                            break;
                        }

                        case SmallResourceItemName.FixedLocationIoPortDescriptor: {
                            UInt16 baseAddress = BuildUInt16(resourceBuffer, start + 1);
                            baseAddress &= 0x3FF;
                            byte length = resourceBuffer[start + 3];
                            result.Add(new IoRangeDescriptor(baseAddress, baseAddress, length, /*alignment*/1));
                            break;
                        }

                        case SmallResourceItemName.VendorDefinedDescriptor: {
                            byte[] data = new byte[7];
                            Array.Copy(resourceBuffer, start + 1, data, 0, 7);
                            result.Add(new VendorDefinedDescriptor(data));
                            break;
                        }

                        case SmallResourceItemName.EndTagDescriptor:
                            // Used to check it was at the end here, but apparently it can occur elsewhere
                            break;

                        default:
                            // Just ignore it and skip over it
                            break;
                    }

                    start += 1 + lengthBytes; // 1 for the tag byte 0
                }
                else {
                    // Large item
                    UInt16 lengthBytes = BuildUInt16(resourceBuffer, start + 1);
                    LargeResourceItemName itemName = (LargeResourceItemName)(resourceBuffer[start] & 0x7F);

                    switch (itemName) {
                        case LargeResourceItemName.MemoryRangeDescriptor24Bit: {
                            MemoryRangeDescriptor.WriteStatus writeStatus =
                                (MemoryRangeDescriptor.WriteStatus)(resourceBuffer[start + 3] & 1);
                            UInt16 minimum   = BuildUInt16(resourceBuffer, start + 3);
                            minimum *= 256;
                            UInt16 maximum   = BuildUInt16(resourceBuffer, start + 6);
                            maximum *= 256;
                            UInt16 alignment = BuildUInt16(resourceBuffer, start + 8);
                            UInt16 length    = BuildUInt16(resourceBuffer, start + 10);
                            length *= 256;
                            result.Add(new MemoryRangeDescriptor(minimum, maximum, length, alignment, writeStatus));
                            break;
                        }

                        case LargeResourceItemName.GenericRegisterDescriptor: {
                            GenericRegisterDescriptor.AddressSpace addressSpace =
                                (GenericRegisterDescriptor.AddressSpace)resourceBuffer[3];
                            byte registerBitWidth = resourceBuffer[start + 4];
                            byte registerBitOffset = resourceBuffer[start + 5];
                            GenericRegisterDescriptor.AddressSize addressSize =
                                (GenericRegisterDescriptor.AddressSize)resourceBuffer[6];
                            ulong registerAddress = BuildUInt64(resourceBuffer, start + 7);

                            result.Add(new GenericRegisterDescriptor(
                                addressSpace, registerBitWidth, registerBitOffset, addressSize, registerAddress));
                            break;
                        }

                        case LargeResourceItemName.VendorDefinedDescriptor: {
                            byte[] guidBytes = new byte[16];
                            Array.Copy(resourceBuffer, start + 4, guidBytes, 0, 16);
                            byte[] data = new byte[lengthBytes - 16 - 1];
                            Array.Copy(resourceBuffer, start + 20, data, 0, data.Length);
                            result.Add(new VendorDefinedDescriptor(new Guid(guidBytes), resourceBuffer[start + 3], data));
                            break;
                        }

                        case LargeResourceItemName.MemoryRangeDescriptor32Bit: {
                            MemoryRangeDescriptor.WriteStatus writeStatus =
                                (MemoryRangeDescriptor.WriteStatus)(resourceBuffer[start + 3] & 1);
                            UInt32 minimum   = BuildUInt32(resourceBuffer, start + 6);
                            UInt32 maximum   = BuildUInt32(resourceBuffer, start + 10);
                            UInt32 alignment = BuildUInt32(resourceBuffer, start + 14);
                            UInt32 length    = BuildUInt32(resourceBuffer, start + 18);
                            result.Add(new MemoryRangeDescriptor(minimum, maximum, length, alignment, writeStatus));
                            break;
                        }

                        case LargeResourceItemName.FixedLocationMemoryRangeDescriptor32Bit: {
                            MemoryRangeDescriptor.WriteStatus writeStatus =
                                (MemoryRangeDescriptor.WriteStatus)(resourceBuffer[start + 3] & 1);
                            UInt32 baseAddress = BuildUInt32(resourceBuffer, start + 4);
                            UInt32 length      = BuildUInt32(resourceBuffer, start + 8);
                            result.Add(new MemoryRangeDescriptor(baseAddress, baseAddress, length, 1, writeStatus));
                            break;
                        }

                        case LargeResourceItemName.WordAddressSpaceDescriptor:
                        case LargeResourceItemName.DwordAddressSpaceDescriptor:
                        case LargeResourceItemName.QwordAddressSpaceDescriptor:
                        case LargeResourceItemName.ExtendedAddressSpaceDescriptor: {
                            AddressSpaceDescriptor.ResourceType resourceType =
                                (AddressSpaceDescriptor.ResourceType)resourceBuffer[start + 3];

                            byte flags = resourceBuffer[start + 4];
                            bool maximumAddressIsFixed = (flags & (1 << 3)) != 0;
                            bool minimumAddressIsFixed = (flags & (1 << 2)) != 0;
                            AddressSpaceDescriptor.DecodeType decodeType =
                                (AddressSpaceDescriptor.DecodeType)((flags >> 1) & 1);
                            ConsumerProducer consumerProducer =
                                (ConsumerProducer)(flags & 1);
                            
                            // alignment same thing as granularity in spec
                            ulong minimum, maximum, length, alignment, addressTranslationOffset; 
                            if (itemName == LargeResourceItemName.WordAddressSpaceDescriptor) {
                                minimum   = BuildUInt16(resourceBuffer, start +  8);
                                maximum   = BuildUInt16(resourceBuffer, start + 10);
                                alignment = BuildUInt16(resourceBuffer, start +  6);
                                length    = BuildUInt16(resourceBuffer, start + 14);
                                addressTranslationOffset = BuildUInt16(resourceBuffer, start + 12);
                            }
                            else if (itemName == LargeResourceItemName.DwordAddressSpaceDescriptor) {
                                minimum   = BuildUInt32(resourceBuffer, start + 10);
                                maximum   = BuildUInt32(resourceBuffer, start + 14);
                                alignment = BuildUInt32(resourceBuffer, start +  6);
                                length    = BuildUInt32(resourceBuffer, start + 22);
                                addressTranslationOffset = BuildUInt32(resourceBuffer, start + 18);
                            }
                            else if (itemName == LargeResourceItemName.QwordAddressSpaceDescriptor) {
                                minimum   = BuildUInt64(resourceBuffer, start + 14);
                                maximum   = BuildUInt64(resourceBuffer, start + 22);
                                alignment = BuildUInt64(resourceBuffer, start + 6);
                                length    = BuildUInt64(resourceBuffer, start + 38);
                                addressTranslationOffset = BuildUInt64(resourceBuffer, start + 30);
                            }
                            else /* if (itemName == LargeResourceItemName.ExtendedAddressSpaceDescriptor) */ {
                                minimum   = BuildUInt64(resourceBuffer, start + 16);
                                maximum   = BuildUInt64(resourceBuffer, start + 24);
                                alignment = BuildUInt64(resourceBuffer, start + 8);
                                length    = BuildUInt64(resourceBuffer, start + 40);
                                addressTranslationOffset = BuildUInt64(resourceBuffer, start + 32);
                            }

                            byte typeSpecificFlags = resourceBuffer[start + 4];
                            if (resourceType == AddressSpaceDescriptor.ResourceType.MemoryRange) {
                                MemoryRangeDescriptor.AcpiMemoryFlags acpiMemoryFlags =
                                    (itemName == LargeResourceItemName.ExtendedAddressSpaceDescriptor) ?
                                    (MemoryRangeDescriptor.AcpiMemoryFlags)BuildUInt16(resourceBuffer, start + 48) :
                                    MemoryRangeDescriptor.AcpiMemoryFlags.None;
                                MemoryRangeDescriptor.MemoryToIoTranslation memoryToIoTranslation = 
                                    (MemoryRangeDescriptor.MemoryToIoTranslation)((typeSpecificFlags >> 5) & 1);
                                MemoryRangeDescriptor.AddressRangeAttribute addressRangeAttribute = 
                                    (MemoryRangeDescriptor.AddressRangeAttribute)((typeSpecificFlags >> 3) & 3);
                                MemoryRangeDescriptor.CacheableAttribute cacheableAttribute = 
                                    (MemoryRangeDescriptor.CacheableAttribute)((typeSpecificFlags >> 1) & 3);
                                MemoryRangeDescriptor.WriteStatus writeStatus = 
                                    (MemoryRangeDescriptor.WriteStatus)(typeSpecificFlags & 1);

                                result.Add(new MemoryRangeDescriptor(resourceType, minimum, maximum, length,
                                                                     alignment, addressTranslationOffset,
                                                                     minimumAddressIsFixed, maximumAddressIsFixed,
                                                                     decodeType, consumerProducer,
                                                                     acpiMemoryFlags, memoryToIoTranslation,
                                                                     addressRangeAttribute, cacheableAttribute,
                                                                     writeStatus));
                            }
                            else if (resourceType == AddressSpaceDescriptor.ResourceType.IoRange) {
                                bool translation = ((typeSpecificFlags >> 4) & 1) != 0;
                                bool sparse      = ((typeSpecificFlags >> 5) & 1) != 0;

                                IoRangeDescriptor.IoToMemoryTranslation ioToMemoryTranslation;
                                if (!translation) {
                                    ioToMemoryTranslation = IoRangeDescriptor.IoToMemoryTranslation.TypeStatic;
                                }
                                else if (sparse) {
                                    ioToMemoryTranslation = IoRangeDescriptor.IoToMemoryTranslation.TypeTranslationSparse;
                                }
                                else {
                                    ioToMemoryTranslation = IoRangeDescriptor.IoToMemoryTranslation.TypeTranslationDense;
                                }

                                result.Add(new IoRangeDescriptor(resourceType, minimum, maximum, length,
                                                                 alignment, addressTranslationOffset,
                                                                 minimumAddressIsFixed, maximumAddressIsFixed,
                                                                 decodeType, consumerProducer,
                                                                 ioToMemoryTranslation));
                            }
                            else {
                                result.Add(new AddressSpaceDescriptor(resourceType, minimum, maximum, length,
                                                                      alignment, addressTranslationOffset,
                                                                      minimumAddressIsFixed, maximumAddressIsFixed,
                                                                      decodeType, consumerProducer));
                            }
                            break;
                        }

                        case LargeResourceItemName.ExtendedIrqDescriptor: {
                            byte flags = resourceBuffer[start + 3];
                            bool sharable = (flags & (1 << 4)) != 0;
                            IrqDescriptor.Polarity polarity = (IrqDescriptor.Polarity)((flags >> 3) & 1);
                            IrqDescriptor.Mode mode = (IrqDescriptor.Mode)(flags & 1);

                            int[] interruptTable = new int[resourceBuffer[start + 4]];
                            for (int i = 0; i < interruptTable.Length; i++) {
                                interruptTable[i] = resourceBuffer[start + 5 + i];
                            }

                            // TODO: Currently we don't extract the Resource Source, if present

                            result.Add(new IrqDescriptor(interruptTable, sharable, polarity, mode));
                            break;
                        }

                        default:
                            // Just ignore it and skip over it
                            break;
                    }

                    start += 1 + 2 + lengthBytes; // 1 for the tag byte, 2 for length bytes
                }
            }

            return result.ToArray();
        }
    }
}
