///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   AcpiTables.cs
//
//  Note:
//    Based on ACPI 3.0 Spec.

// Define to dump all ACPI tables in uuencoded binary form to the debugger
// at boot time.
//#define DUMP_ACPI_TABLES_UUENCODED

// Define to dump a trace of all raw read/writes performed by the ACPI
// interpreter to the debugger. This can be processed by a tool
// %SINGULARITY_ROOT%\Windows\ACPI\TestFiles\parse_read_write_trace.pl
// to produce a read/write trace for use by the test harness.
//#define DUMP_RAW_READ_WRITES

// Define to dump all names in the initial ACPI namespace tree.
//#define DUMP_ACPI_NAMESPACE

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using System.Collections;
    using System.Text;

    using Microsoft.Singularity.Io;
    using Microsoft.Singularity.Hal;

    internal sealed class VerboseOut
    {
        [System.Diagnostics.Conditional("VERBOSE")]
        internal static void WriteLine(string format, __arglist)
        {
            DebugStub.WriteLine(format, new ArgIterator(__arglist));
        }

        [System.Diagnostics.Conditional("VERBOSE")]
        internal static void WriteLine(string message)
        {
            DebugStub.WriteLine(message);
        }

        [System.Diagnostics.Conditional("VERBOSE")]
        internal static void WriteLine()
        {
            DebugStub.WriteLine();
        }

        [System.Diagnostics.Conditional("VERBOSE")]
        internal static void Write(string format, __arglist)
        {
            DebugStub.Write(format, new ArgIterator(__arglist));
        }

        [System.Diagnostics.Conditional("VERBOSE")]
        internal static void Write(string message)
        {
            DebugStub.Write(message);
        }

        [System.Diagnostics.Conditional("VERBOSE")]
        internal static void Print(string format, __arglist)
        {
            DebugStub.Print(format, new ArgIterator(__arglist));
        }

        [System.Diagnostics.Conditional("VERBOSE")]
        internal static void Print(string message)
        {
            DebugStub.Print(message);
        }
    }

    [ CLSCompliant(false) ]
    public class AcpiTables
    {
        private static Fadt fadt;
        private static Madt madt;

        private static Dsdt dsdt;
        private static Ssdt ssdt;

        private static Srat srat;

        private static SystemTableHeader rsdtHeader;
        private static Rsdt rsdt;

        private static PMTimer pmTimer;

        private static AcpiNamespace acpiNamespace;
        private static ReservedObjects reservedObjects;

        private static UIntPtr GetRsdpBase()
        {
            unsafe
            {
                return Platform.ThePlatform.AcpiRoot32;
            }
        }

        public static Fadt GetFadt()
        {
            return fadt;
        }

        public static Madt GetMadt()
        {
            return madt;
        }

        public static Srat GetSrat()
        {
            return srat;
        }

        public static PMTimer GetPMTimer()
        {
            return pmTimer;
        }

        public static AcpiNamespace AcpiNamespace
        {
            get
            {
                return acpiNamespace;
            }
        }

        private class StringSet
        {
            private SortedList map = new SortedList();

            public void Add(string s)
            {
                map.Add(s, null);
            }

            public bool Contains(string s)
            {
                return map.ContainsKey(s);
            }
        }

        public static void Parse()
        {
            UIntPtr rsdpBase = GetRsdpBase();

            if (rsdpBase == UIntPtr.Zero) {
                VerboseOut.Print("ACPI RSDP not found\n");
            }

#if DUMP_ACPI_TABLES_UUENCODED
            UuencodeDumpRegion("RSDP.dmp",
                IoMemory.MapPhysicalMemory(
                    rsdpBase, 36u,
                    true, false));
#endif
            Rsdp rsdp = Rsdp.Parse(rsdpBase, 36u);

            VerboseOut.Print("ACPI RSDP OemId is {0:x8}\n",
                            __arglist(rsdp.OemId));
            VerboseOut.Print("ACPI RSDP revision is {0:x8}\n",
                            __arglist(rsdp.Revision));

            if (rsdp.Revision == 2) {
                rsdtHeader = SystemTableHeader.Create(rsdp.XsdtAddress);
#if DUMP_ACPI_TABLES_UUENCODED
                UuencodeDumpRegion("XSDT.dmp",
                    IoMemory.MapPhysicalMemory(
                        rsdtHeader.Address, rsdtHeader.FullTableLength,
                        true, false));
#endif
                rsdt = Xsdt.Create(rsdtHeader);
            }
            else {
                rsdtHeader = SystemTableHeader.Create(rsdp.RsdtAddress);
#if DUMP_ACPI_TABLES_UUENCODED
                UuencodeDumpRegion("RSDT.dmp",
                    IoMemory.MapPhysicalMemory(
                        rsdtHeader.Address, rsdtHeader.FullTableLength,
                        true, false));
#endif
                rsdt = Rsdt.Create(rsdtHeader);
            }

            VerboseOut.Print("ACPI RSDT/XSDT OemTableId is {0}\n",
                            __arglist(rsdtHeader.OemTableId));
            VerboseOut.Print("ACPI RSDT/XSDT Revision is {0:x8}\n",
                            __arglist(rsdtHeader.Revision));
            VerboseOut.Print("ACPI RSDT/XSDT CreatorId is {0:x8}\n",
                            __arglist(rsdtHeader.CreatorId));
            VerboseOut.Print("ACPI RSDT/XSDT CreatorRevision is {0:x8}\n",
                            __arglist(rsdtHeader.CreatorRevision));

            VerboseOut.Print("RSDT contains:\n");
            for (int i = 0; i < rsdt.EntryCount; i++) {
                SystemTableHeader header = rsdt.GetTableHeader(i);
                VerboseOut.Print("    {0:x8}\n", __arglist(header.Signature));
                if (header.Signature == Fadt.Signature) {
                    fadt = Fadt.Create(header);
                }
                else if (header.Signature == Madt.Signature) {
                    madt = Madt.Create(header);
                }
                else if (header.Signature == Ssdt.Signature) {
                    ssdt = Ssdt.Create(header);
                }
                // Srat, Slit
                else if (header.Signature == Srat.Signature) {
                    srat = Srat.Create(header);
                    srat.ParseSratStructure();

                    // srat.DumpSratOffsets();
                    // srat.DumpSratImportantFields();
                    // srat.DumpSratStructure();

                }
            }

            SystemTableHeader dsdtHeader = null;

            if (fadt != null) {
                pmTimer = PMTimer.Create(fadt);
                VerboseOut.Print("PMTimer Value={0} Width={1}\n",
                                __arglist(pmTimer.Value, pmTimer.Width));
                uint t0 = pmTimer.Value;
                uint t1 = pmTimer.Value;
                uint t2 = pmTimer.Value;
                uint delta = (t2 >= t1) ? t2 - t1 : ((t1 | 0xff000000) - t2);
                VerboseOut.Print("Read cost {0} ticks\n", __arglist(delta));

                if (fadt.DSDT != 0) {
                    dsdtHeader = SystemTableHeader.Create(fadt.DSDT);
                    dsdt = Dsdt.Create(dsdtHeader);
                }
            }

            VerboseOut.Print("Parsing and loading AML\n");

#if DUMP_ACPI_TABLES_UUENCODED
            if (dsdtHeader != null) {
                UuencodeDumpRegion("ACPI.DSDT.dmp",
                    IoMemory.MapPhysicalMemory(
                                dsdtHeader.Address, dsdtHeader.FullTableLength,
                                true, false));
            }

            for (int i = 0; i < rsdt.EntryCount; i++) {
                SystemTableHeader header = rsdt.GetTableHeader(i);
                UuencodeDumpRegion("ACPI." + header.Signature + "." + header.OemTableId + ".dmp",
                    IoMemory.MapPhysicalMemory(
                        header.Address, header.FullTableLength,
                        true, false));
            }
#endif // DUMP_ACPI_TABLES_UUENCODED
        }

        public static AcpiDevice[] LoadDevices()
        {
            OperationRegionAccessor operationRegionAccessor = new OperationRegionAccessor();
            acpiNamespace = new AcpiNamespace();
            reservedObjects = new ReservedObjects(acpiNamespace);
            reservedObjects.CreateReservedObjects();

            if (dsdt != null) {
                if (ParseAndLoadRegion(dsdt.Region, operationRegionAccessor) == AmlParser.ParseSuccess.Failure) {
                    throw new Exception("AML parser failure while parsing DSDT");
                }
            }

            // From the spec: "SSDTs are a continuation of the DSDT. Multiple SSDTs
            // can be used as part of a platform description. After the DSDT is loaded
            // into the ACPI Namespace, each secondary description table listed in the
            // RSDT/XSDT with a unique OEM Table ID is loaded." - section 2.1, General
            // ACPI Terminology
            StringSet visitedOemTableIds = new StringSet();
            for (int i = 0; i < rsdt.EntryCount; i++) {
                SystemTableHeader header = rsdt.GetTableHeader(i);
                VerboseOut.Print("    {0:x8}\n", __arglist(header.Signature));

                string oemTableId = header.OemTableId;
                if (!visitedOemTableIds.Contains(oemTableId) && header.Signature == Ssdt.Signature) {
                    visitedOemTableIds.Add(oemTableId);
                    ssdt = Ssdt.Create(header);
                    if (ParseAndLoadRegion(ssdt.Region, operationRegionAccessor) == AmlParser.ParseSuccess.Failure) {
                        throw new Exception("AML parser failure while parsing SSDT " + oemTableId);
                    }
                }
            }

#if DUMP_ACPI_NAMESPACE
            DebugStub.WriteLine("Dumping ACPI namespace tree...");
            acpiNamespace.DumpTree();
#endif

            return GetDeviceInfo(operationRegionAccessor);
        }

#if DUMP_ACPI_TABLES_UUENCODED
        private static void UuencodeDumpRegion(string filename, IoMemory region)
        {
            DebugStub.Print("\nbegin 777 {0}\n", __arglist(filename));

            StringBuilder line = new StringBuilder();
            int inputBytesOnLine = 0;
            for (int i = 0; i < region.Length; i += 3) {
                byte b1 = (byte)0, b2 = (byte)0, b3 = (byte)0;

                b1 = region.Read8(i);
                inputBytesOnLine++;

                if (i + 1 < region.Length) {
                    b2 = region.Read8(i + 1);
                    inputBytesOnLine++;
                }

                if (i + 2 < region.Length) {
                    b3 = region.Read8(i + 2);
                    inputBytesOnLine++;
                }

                line.Append((char)(32 + (b1 >> 2)));
                line.Append((char)(32 + (((b1 << 4) | (b2 >> 4)) & 0x3F)));
                line.Append((char)(32 + (((b2 << 2) | (b3 >> 6)) & 0x3F)));
                line.Append((char)(32 + (b3 & 0x3F)));

                if (line.Length >= 60 || i + 3 >= region.Length) {
                    DebugStub.Print("{0}{1}\n", __arglist((char)(inputBytesOnLine + 32), line.ToString()));
                    line.Remove(0, line.Length);
                    inputBytesOnLine = 0;
                }
            }

            DebugStub.Print("end\n\n");
        }
#endif // #if DUMP_ACPI_TABLES_UUENCODED

        private static AmlParser.ParseSuccess ParseAndLoadRegion(IoMemory region, AcpiObject.IOperationRegionAccessor operationRegionAccessor)
        {
            AmlParser.AMLCode result;
            int offset = 0;
            AmlParser parser = new AmlParser(new IoMemoryAmlStreamAdapter(region), null, null);
            AmlParser.ParseSuccess parseSuccess =
                parser.ParseAMLCode(out result, ref offset, region.Length);

            if (parseSuccess == AmlParser.ParseSuccess.Success) {
                AmlLoader loader = new AmlLoader(acpiNamespace, operationRegionAccessor);
                loader.Load(result);
            }
            return parseSuccess;
        }

        private static AcpiDevice[] GetDeviceInfo(AcpiObject.IOperationRegionAccessor operationRegionAccessor)
        {
            ArrayList deviceInfo = new ArrayList();

            AmlInterpreter interpreter = new AmlInterpreter(acpiNamespace, operationRegionAccessor);

            foreach (AcpiNamespace.Node crsNode in acpiNamespace.GetAllNodes()) {
                if (crsNode.Name != "_CRS") {
                    continue;
                }

                VerboseOut.Write("Loading resource descriptors for ACPI device ");
                foreach (string segment in crsNode.Path.RemoveSegment().NameSegments) {
                    VerboseOut.Write(segment + "\\");
                }
                VerboseOut.WriteLine();

                AcpiNamespace.Node hidNode =
                    acpiNamespace.LookupNode(crsNode.Path.RemoveSegmentAbsolute().AddSegmentAbsolute("_HID"));
                if (hidNode == null) {
                    throw new Exception("Found device with _CRS property but no matching _HID property");
                }

                AcpiObject.AcpiObject hidObject = hidNode.Value;
                if (hidObject is AcpiObject.BytecodeMethod) {
                    AmlInterpreterThread thread =
                        interpreter.InvokeMethodOnNewThread(null, hidNode.Path, new AcpiObject.AcpiObject[] { });
                    interpreter.Run();
                    hidObject = thread.ExitValue;
                }
                string deviceId = HidObjectToDeviceId(hidObject);

                AcpiObject.AcpiObject crsObject = crsNode.Value;
                if (crsObject is AcpiObject.BytecodeMethod) {
                    AmlInterpreterThread thread =
                        interpreter.InvokeMethodOnNewThread(null, crsNode.Path, new AcpiObject.AcpiObject[] { });
                    interpreter.Run();
                    crsObject = thread.ExitValue;
                }

                if (crsObject is AcpiObject.Buffer) {
                    byte[] crsBuffer = crsObject.GetAsBuffer().Contents;
                    ResourceDescriptor[] resourceDescriptors = ResourceDescriptorParser.Parse(crsBuffer);

                    VerboseOut.WriteLine("Loaded resource descriptor for device " + deviceId);

                    deviceInfo.Add(new AcpiDevice(deviceId, resourceDescriptors));
                }
                else {
                    VerboseOut.WriteLine("No resource descriptor for device " + deviceId);
                }
            }

            return (AcpiDevice[])deviceInfo.ToArray(typeof(AcpiDevice));
        }

        private static string HidObjectToDeviceId(AcpiObject.AcpiObject obj)
        {
            AcpiObject.AcpiObjectType type =
                (AcpiObject.AcpiObjectType)((AcpiObject.Integer)(obj.ObjectType())).Value;
            string hid;

            if (type == AcpiObject.AcpiObjectType.Integer)
            {
                // Swap byte order so that all fields are contiguous
                ulong eisaId = ByteOrder.Swap((uint)(((AcpiObject.Integer)obj).Value));
                hid = String.Format("{0}{1}{2}{3:X}{4:X}{5:X}{6:X}",
                                    (char)(((eisaId >> 26) & 0x1F) + '@'),
                                    (char)(((eisaId >> 21) & 0x1F) + '@'),
                                    (char)(((eisaId >> 16) & 0x1F) + '@'),
                                    (eisaId >> 12) & 0xF,
                                    (eisaId >> 8) & 0xF,
                                    (eisaId >> 4) & 0xF,
                                    (eisaId >> 0) & 0xF);
            }
            else if (type == AcpiObject.AcpiObjectType.String) {
                hid = ((AcpiObject.String)obj).Value;
            }
            else {
                throw new ArgumentException("_HID object was not an integer or string as expected");
            }

            if (hid.StartsWith("PNP")) {
                return "/pnp/" + hid;
            }
            else {
                return "/acpi/" + hid;
            }
        }

        public class IoMemoryAmlStreamAdapter : IAmlStream
        {
            private IoMemory region;

            public IoMemoryAmlStreamAdapter(IoMemory region)
            {
                this.region = region;
            }

            public byte ReadByteData(ref int offset)
            {
                if (offset + 1 > region.Length) {
                    throw new EndOfAmlStreamException();
                }
                byte result = region.Read8(offset);
                offset++;
                return result;
            }

            public bool TryReadByteData(ref int offset, out byte result)
            {
                if (offset + 1 > region.Length) {
                    result = 0;
                    return false;
                }
                result = region.Read8(offset);
                offset++;
                return true;
            }

            public char ReadChar(ref int offset)
            {
                if (offset + 1 > region.Length) {
                    throw new EndOfAmlStreamException();
                }
                char result = (char)region.Read8(offset);
                offset++;
                return result;
            }

            public byte[] ReadByteDataArray(ref int offset, int length)
            {
                if (offset + length > region.Length) {
                    throw new EndOfAmlStreamException();
                }
                byte[] result = new byte[length];
                if (length != 0) {
                    region.Read8(offset, result, 0, length);
                }
                offset += length;
                return result;
            }

            public bool TryReadByteDataArray(ref int offset, int length, out byte[] result)
            {
                if (offset + length > region.Length) {
                    result = null;
                    return false;
                }
                result = new byte[length];
                if (length != 0) {
                    region.Read8(offset, result, 0, length);
                }
                offset += length;
                return true;
            }

            public ushort ReadWordData(ref int offset)
            {
                if (offset + 2 > region.Length) {
                    throw new EndOfAmlStreamException();
                }
                ushort result = ByteOrder.LittleEndianToHost(region.Read16(offset));
                offset += 2;
                return result;
            }

            public uint ReadDWordData(ref int offset)
            {
                if (offset + 4 > region.Length) {
                    throw new EndOfAmlStreamException();
                }
                uint result = ByteOrder.LittleEndianToHost(region.Read32(offset));
                offset += 4;
                return result;
            }

            public ulong ReadQWordData(ref int offset)
            {
                if (offset + 8 > region.Length) {
                    throw new EndOfAmlStreamException();
                }
                ulong result = ByteOrder.LittleEndianToHost(region.Read64(offset));
                offset += 8;
                return result;
            }
        }

        public class OperationRegionAccessor : AcpiObject.IOperationRegionAccessor
        {
            private const ushort PciAddressPort = 0xcf8;
            private const uint PciConfigEnableMask = 1u << 31;
            private IoPort pciConfigAddressPort;
            private IoPort pciConfigDataPort;

            public OperationRegionAccessor()
            {
                IoPortRange pciConfigPorts = new IoPortRange(PciAddressPort, 8, Access.ReadWrite);
                pciConfigAddressPort = pciConfigPorts.PortAtOffset(0, 4, Access.Write);
                pciConfigDataPort = pciConfigPorts.PortAtOffset(4, 4, Access.ReadWrite);
            }

            public byte Read8(AcpiObject.RegionSpace regionSpace, ulong offset)
            {
                byte result;
                switch (regionSpace) {
                    case AcpiObject.RegionSpace.SystemMemory:
                        // TODO: This is a first stab - ideally the AcpiObject.OperationRegion
                        // ought to be holding onto an IoMemoryRange and passing it in repeatedly.
                        IoMemory region = IoMemory.MapPhysicalMemory(offset, 1, true/*readable*/, false/*writable*/);
                        result = region.Read8(0);
                        break;

                    case AcpiObject.RegionSpace.SystemIO:
                        IoPort port = new IoPort((ushort)offset, 1, Access.Read);
                        result = port.Read8();
                        break;

                    case AcpiObject.RegionSpace.PCI_Config:
                        pciConfigAddressPort.Write32(PciConfigEnableMask | (uint)offset);
                        result = pciConfigDataPort.Read8();
                        break;

                    default:
                        throw new Exception("Unimplemented operation region type" + regionSpace);
                }
#if DUMP_RAW_READ_WRITES
                DebugStub.WriteLine("ACPI read: space: " + regionSpace + ", offset: " + offset + ", bytes: " + 1 + ", result: " + result.ToString("X"));
#endif
                return result;
            }

            public void Write8(AcpiObject.RegionSpace regionSpace, ulong offset, byte value)
            {
#if DUMP_RAW_READ_WRITES
                DebugStub.WriteLine("ACPI write: space: " + regionSpace + ", offset: " + offset + ", bytes: " + 1 + ", value: " + value.ToString("X"));
#endif
                switch (regionSpace) {
                    case AcpiObject.RegionSpace.SystemMemory:
                        IoMemory region = IoMemory.MapPhysicalMemory(offset, 1, true/*readable*/, true/*writable*/);
                        region.Write8(0, value);
                        break;

                    case AcpiObject.RegionSpace.SystemIO:
                        IoPort port = new IoPort((ushort)offset, 1, Access.ReadWrite);
                        port.Write8(value);
                        break;

                    case AcpiObject.RegionSpace.PCI_Config:
                        pciConfigAddressPort.Write32(PciConfigEnableMask | (uint)offset);
                        pciConfigDataPort.Write8(value);
                        break;

                    default:
                        throw new Exception("Unimplemented operation region type" + regionSpace);
                }
            }

            public ushort Read16(AcpiObject.RegionSpace regionSpace, ulong offset)
            {
                ushort result;
                switch (regionSpace) {
                    case AcpiObject.RegionSpace.SystemMemory:
                        // TODO: This is a first stab - ideally the AcpiObject.OperationRegion
                        // ought to be holding onto an IoMemoryRange and passing it in.
                        IoMemory region = IoMemory.MapPhysicalMemory(offset, 2, true/*readable*/, false/*writable*/);
                        result = region.Read16(0);
                        break;

                    case AcpiObject.RegionSpace.SystemIO:
                        IoPort port = new IoPort((ushort)offset, 2, Access.Read);
                        result = port.Read16();
                        break;

                    case AcpiObject.RegionSpace.PCI_Config:
                        pciConfigAddressPort.Write32(PciConfigEnableMask | (uint)offset);
                        result = pciConfigDataPort.Read16();
                        break;

                    default:
                        throw new Exception("Unimplemented operation region type" + regionSpace);
                }

#if DUMP_RAW_READ_WRITES
                DebugStub.WriteLine("ACPI read: space: " + regionSpace + ", offset: " + offset + ", bytes: " + 2 + ", result: " + result.ToString("X"));
#endif
                return result;
            }

            public void Write16(AcpiObject.RegionSpace regionSpace, ulong offset, ushort value)
            {
#if DUMP_RAW_READ_WRITES
                DebugStub.WriteLine("ACPI write: space: " + regionSpace + ", offset: " + offset + ", bytes: " + 2 + ", value: " + value.ToString("X"));
#endif
                switch (regionSpace) {
                    case AcpiObject.RegionSpace.SystemMemory:
                        IoMemory region = IoMemory.MapPhysicalMemory(offset, 2, true/*readable*/, true/*writable*/);
                        region.Write16(0, value);
                        break;

                    case AcpiObject.RegionSpace.SystemIO:
                        IoPort port = new IoPort((ushort)offset, 2, Access.ReadWrite);
                        port.Write16(value);
                        break;

                    case AcpiObject.RegionSpace.PCI_Config:
                        pciConfigAddressPort.Write32(PciConfigEnableMask | (uint)offset);
                        pciConfigDataPort.Write16(value);
                        break;

                    default:
                        throw new Exception("Unimplemented operation region type" + regionSpace);
                }
            }

            public uint Read32(AcpiObject.RegionSpace regionSpace, ulong offset)
            {
                uint result;
                switch (regionSpace) {
                    case AcpiObject.RegionSpace.SystemMemory:
                        IoMemory region = IoMemory.MapPhysicalMemory(offset, 4, true/*readable*/, false/*writable*/);
                        result = region.Read32(0);
                        break;

                    case AcpiObject.RegionSpace.SystemIO:
                        IoPort port = new IoPort((ushort)offset, 4, Access.Read);
                        result = port.Read32();
                        break;

                    case AcpiObject.RegionSpace.PCI_Config:
                        pciConfigAddressPort.Write32(PciConfigEnableMask | (uint)offset);
                        result = pciConfigDataPort.Read32();
                        break;

                    default:
                        throw new Exception("Unimplemented operation region type" + regionSpace);
                }
#if DUMP_RAW_READ_WRITES
                DebugStub.WriteLine("ACPI read: space: " + regionSpace + ", offset: " + offset + ", bytes: " + 4 + ", result: " + result.ToString("X"));
#endif
                return result;
            }

            public void Write32(AcpiObject.RegionSpace regionSpace, ulong offset, uint value)
            {
#if DUMP_RAW_READ_WRITES
                DebugStub.WriteLine("ACPI write: space: " + regionSpace + ", offset: " + offset + ", bytes: " + 4 + ", value: " + value.ToString("X"));
#endif
                switch (regionSpace) {
                    case AcpiObject.RegionSpace.SystemMemory:
                        IoMemory region = IoMemory.MapPhysicalMemory(offset, 4, true/*readable*/, true/*writable*/);
                        region.Write32(0, value);
                        break;

                    case AcpiObject.RegionSpace.SystemIO:
                        IoPort port = new IoPort((ushort)offset, 4, Access.ReadWrite);
                        port.Write32(value);
                        break;

                    case AcpiObject.RegionSpace.PCI_Config:
                        pciConfigAddressPort.Write32(PciConfigEnableMask | (uint)offset);
                        pciConfigDataPort.Write32(value);
                        break;

                    default:
                        throw new Exception("Unimplemented operation region type" + regionSpace);
                }
            }

            public byte[] ReadBytes(AcpiObject.RegionSpace regionSpace, ulong offset, ulong length)
            {
                byte[] result = new byte[length];

                switch (regionSpace) {
                    case AcpiObject.RegionSpace.SystemMemory:
                        IoMemory region = IoMemory.MapPhysicalMemory(offset, length, true/*readable*/, false/*writable*/);
                        for (ulong i = 0; i < length; i++) {
                            result[i] = region.Read8((int)i);
                        }
                        break;

                    default:
                        throw new Exception("ReadBytes() only supported for SystemMemory regions");
                }

#if DUMP_RAW_READ_WRITES
                DebugStub.Write("ACPI read: space: " + regionSpace + ", offset: " + offset + ", bytes: " + length + ", result: {");
                for (int i = 0; i < result.Length; i++) {
                    DebugStub.Write(result[i].ToString("X"));
                    if (i < result.Length - 1) {
                        DebugStub.Write(",");
                    }
                }
                DebugStub.WriteLine("}");
#endif

                return result;
            }
        }
    }

    public class AcpiDevice
    {
        string deviceId;
        ResourceDescriptor[] resourceDescriptors;

        public AcpiDevice(string deviceId, ResourceDescriptor[] resourceDescriptors)
        {
            this.deviceId = deviceId;
            this.resourceDescriptors = resourceDescriptors;
        }

        public string DeviceId
        {
            get
            {
                return deviceId;
            }
        }

        public ResourceDescriptor[] ResourceDescriptors {
            get
            {
                return resourceDescriptors;
            }
        }
    }
}
