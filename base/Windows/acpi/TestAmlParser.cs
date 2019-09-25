using System;
using System.Collections;
using System.Diagnostics;
using System.IO;

using Microsoft.Singularity.Hal.Acpi;
using AcpiObject = Microsoft.Singularity.Hal.Acpi.AcpiObject;

namespace AppReader
{
    public class FileStreamAmlStreamAdapter : IAmlStream
    {
        private FileStream stream;

        public FileStreamAmlStreamAdapter(FileStream stream)
        {
            this.stream = stream;
        }

        public byte ReadByteData(ref int offset)
        {
            stream.Seek(offset, SeekOrigin.Begin);
            offset++;
            return (byte)stream.ReadByte();
        }

        public bool TryReadByteData(ref int offset, out byte result)
        {
            if (offset > stream.Length) {
                result = 0;
                return false;
            }
            else {
                stream.Seek(offset, SeekOrigin.Begin);
                offset++;
                result = (byte)stream.ReadByte();
                return true;
            }
        }

        public char ReadChar(ref int offset)
        {
            stream.Seek(offset, SeekOrigin.Begin);
            offset++;
            return (char)stream.ReadByte();
        }

        public byte[] ReadByteDataArray(ref int offset, int length)
        {
            stream.Seek(offset, SeekOrigin.Begin);
            offset += length;

            byte[] result = new byte[length];
            stream.Read(result, 0, length);
            return result;
        }

        public bool TryReadByteDataArray(ref int offset, int length, out byte[] result)
        {
            if (offset + length > stream.Length) {
                result = null;
                return false;
            }
            else {
                stream.Seek(offset, SeekOrigin.Begin);
                offset += length;

                result = new byte[length];
                stream.Read(result, 0, length);
                return true;
            }
        }

        public ushort ReadWordData(ref int offset)
        {
            stream.Seek(offset, SeekOrigin.Begin);
            offset += 2;

            byte[] result = new byte[2];
            stream.Read(result, 0, result.Length);
            return (ushort)(result[0] +
                            (((ushort)result[1]) << 8));
        }

        public uint ReadDWordData(ref int offset)
        {
            stream.Seek(offset, SeekOrigin.Begin);
            offset += 4;

            byte[] result = new byte[4];
            stream.Read(result, 0, result.Length);
            return (uint)(result[0] +
                          (((uint)result[1]) << 8) +
                          (((uint)result[2]) << 16) +
                          (((uint)result[3]) << 24));
        }

        public ulong ReadQWordData(ref int offset)
        {
            stream.Seek(offset, SeekOrigin.Begin);
            offset += 8;

            byte[] result = new byte[8];
            stream.Read(result, 0, result.Length);
            return (ulong)(result[0] +
                           (((ulong)result[1]) << 8) +
                           (((ulong)result[2]) << 16) +
                           (((ulong)result[3]) << 24) +
                           (((ulong)result[4]) << 32) +
                           (((ulong)result[5]) << 40) +
                           (((ulong)result[6]) << 48) +
                           (((ulong)result[7]) << 56));
        }
    }

    public class MismatchedTraceException : Exception
    {
        public MismatchedTraceException()
            : base("Read/write requests do not match supplied trace") { }
    }

    // Uses a trace from a run on a real machine to ensure identical results offline
    public class TraceOperationRegionAccessor : AcpiObject.IOperationRegionAccessor
    {
        StreamReader trace;

        bool isDone;
        bool isRead;
        bool isWrite;
        AcpiObject.RegionSpace regionSpace;
        ulong offset;
        ulong length;
        ulong value;
        byte[] valueSequence;

        public TraceOperationRegionAccessor(Stream traceStream)
        {
            trace = new StreamReader(traceStream);
            ReadNext();
        }

        private void ReadNext()
        {
            string line = trace.ReadLine();
            isDone = (line == null || line.Trim() == "");

            if (!isDone) {
                string[] fields = line.Trim().Split(new char[] {' '});
                isRead = fields[0].StartsWith("r");
                isWrite = !isRead; // Just for readability
                regionSpace = (AcpiObject.RegionSpace)int.Parse(fields[1]);
                offset = ulong.Parse(fields[2]);
                length = ulong.Parse(fields[3]);
                if (fields.Length > 4) {
                    value = ulong.Parse(fields[4]);
                }

                if (fields.Length != 5) {
                    valueSequence = new byte[fields.Length - 4];
                    for (int i = 0; i < valueSequence.Length; i++) {
                        valueSequence[i] = byte.Parse(fields[4 + i]);
                    }
                }
            }
        }

        public byte Read8(AcpiObject.RegionSpace regionSpace, ulong offset)
        {
            Console.WriteLine("Read8 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            if (!(isRead && length == 1 && regionSpace == this.regionSpace && offset == this.offset)) {
                throw new MismatchedTraceException();
            }
            byte result = (byte)value;
            ReadNext();
            return result;
        }

        public void Write8(AcpiObject.RegionSpace regionSpace, ulong offset, byte value)
        {
            Console.WriteLine("Write8 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            if (!(isWrite && length == 1 && regionSpace == this.regionSpace && offset == this.offset && value == this.value)) {
                throw new MismatchedTraceException();
            }
            ReadNext();
        }

        public ushort Read16(AcpiObject.RegionSpace regionSpace, ulong offset)
        {
            Console.WriteLine("Read16 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            if (!(isRead && length == 2 && regionSpace == this.regionSpace && offset == this.offset)) {
                throw new MismatchedTraceException();
            }
            ushort result = (ushort)value;
            ReadNext();
            return result;
        }

        public void Write16(AcpiObject.RegionSpace regionSpace, ulong offset, ushort value)
        {
            Console.WriteLine("Write16 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            if (!(isWrite && length == 2 && regionSpace == this.regionSpace && offset == this.offset && value == this.value)) {
                throw new MismatchedTraceException();
            }
            ReadNext();
        }

        public uint Read32(AcpiObject.RegionSpace regionSpace, ulong offset)
        {
            Console.WriteLine("Read32 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            if (!(isRead && length == 4 && regionSpace == this.regionSpace && offset == this.offset)) {
                throw new MismatchedTraceException();
            }
            uint result = (uint)value;
            ReadNext();
            return result;
        }

        public void Write32(AcpiObject.RegionSpace regionSpace, ulong offset, uint value)
        {
            Console.WriteLine("Write32 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            if (!(isWrite && length == 4 && regionSpace == this.regionSpace && offset == this.offset && value == this.value)) {
                throw new MismatchedTraceException();
            }
            ReadNext();
        }

        public byte[] ReadBytes(AcpiObject.RegionSpace regionSpace, ulong offset, ulong length)
        {
            Console.WriteLine("Read " + length + " bytes at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            if (!(isRead && length == (ulong)valueSequence.Length && regionSpace == this.regionSpace && offset == this.offset)) {
                throw new MismatchedTraceException();
            }
            byte[] result = valueSequence;
            ReadNext();
            return valueSequence;
        }
    }
    
    public class TestOperationRegionAccessor : AcpiObject.IOperationRegionAccessor
    {
        public byte Read8(AcpiObject.RegionSpace regionSpace, ulong offset)
        {
            Console.WriteLine("Read8 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            return 10;
        }

        public void Write8(AcpiObject.RegionSpace regionSpace, ulong offset, byte value)
        {
            Console.WriteLine("Write8 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
        }

        public ushort Read16(AcpiObject.RegionSpace regionSpace, ulong offset)
        {
            Console.WriteLine("Read16 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            return 1024;
        }

        public void Write16(AcpiObject.RegionSpace regionSpace, ulong offset, ushort value)
        {
            Console.WriteLine("Write16 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
        }

        public uint Read32(AcpiObject.RegionSpace regionSpace, ulong offset)
        {
            Console.WriteLine("Read32 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            return 1024;
        }

        public void Write32(AcpiObject.RegionSpace regionSpace, ulong offset, uint value)
        {
            Console.WriteLine("Write32 at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
        }

        public byte[] ReadBytes(AcpiObject.RegionSpace regionSpace, ulong offset, ulong length)
        {
            Console.WriteLine("Read " + length + " bytes at " + regionSpace.ToString() + ":0x" + offset.ToString("X"));
            byte[] result = new byte[length];
            for (ulong i = 0; i < length; i++) {
                result[i] = 10;
            }
            return result;
        }
    }
    
    public class ReaderMain
    {
        static void Usage()
        {
            Console.WriteLine("AppReader.exe <manifestfile | (-d | -s) manifestdirectory | -r appdirectory>");
            return;
        }

        [STAThread]
        public static void Main(string[] args)
        {
            if (args.Length < 1) {
                Usage();
                Environment.Exit(1);
            }

            try {
                AcpiNamespace acpiNamespace = new AcpiNamespace();
                ReservedObjects reservedObjects = new ReservedObjects(acpiNamespace);
                reservedObjects.CreateReservedObjects();

                AcpiObject.IOperationRegionAccessor operationRegionAccessor =
                    new TestOperationRegionAccessor();
                AmlInterpreter interpreter = new AmlInterpreter(acpiNamespace, operationRegionAccessor);

                foreach (string flag in args) {
                    if (flag.StartsWith("/tracefile=")) {
                        operationRegionAccessor =
                            new TraceOperationRegionAccessor(new FileStream(flag.Substring("/tracefile=".Length),
                                                                            FileMode.Open, FileAccess.Read));
                    }
                    else if (flag.StartsWith("/")) {
                        Console.WriteLine("Unrecognized flag '" + flag + "'");
                        Environment.Exit(1);
                    }
                }

                AmlParser.ParseSuccess parseSuccess = AmlParser.ParseSuccess.Success;
                foreach (string dumpFilename in args) {
                    if (dumpFilename.StartsWith("/")) {
                        continue;
                    }

                    using (FileStream reader = new FileStream(dumpFilename, FileMode.Open, FileAccess.Read)) {
                        AmlParser.AMLCode result;
                        int offset = 0x24; // Skip header
                        AmlParser parser = new AmlParser(new FileStreamAmlStreamAdapter(reader), null, null);
                        parseSuccess =
                            parser.ParseAMLCode(out result, ref offset, (int)(new FileInfo(dumpFilename).Length));

                        if (parseSuccess == AmlParser.ParseSuccess.Success) {
                            AmlLoader loader = new AmlLoader(acpiNamespace, operationRegionAccessor);
                            loader.Load(result);
                        }
                        else {
                            break;
                        }
                    }
                }

                if (parseSuccess == AmlParser.ParseSuccess.Success) {
                    parseSuccess = interpreter.ParseMethodBodies();
                }

                if (parseSuccess == AmlParser.ParseSuccess.Success) {
                    LoadDeviceInfo(acpiNamespace, operationRegionAccessor);
                }

                if (parseSuccess == AmlParser.ParseSuccess.Success) {
                    Console.WriteLine("Parsed successfully");
                    Environment.Exit(0);
                }
                else {
                    Console.WriteLine("Encountered error during parse");
                    Environment.Exit(1);
                }
            }
            catch (Exception e) {
                Console.WriteLine("Encountered exception: " + e.Message);
                Console.WriteLine(e.StackTrace);
                Environment.Exit(1);
            }
        }

        private static void LoadDeviceInfo(AcpiNamespace acpiNamespace,
                                           AcpiObject.IOperationRegionAccessor operationRegionAccessor)
        {
            AmlInterpreter interpreter = new AmlInterpreter(acpiNamespace, operationRegionAccessor);

            foreach (AcpiNamespace.Node crsNode in acpiNamespace.GetAllNodes()) {
                if (crsNode.Name != "_CRS") {
                    continue;
                }

                Console.Write("Loading resource descriptors for ACPI device ");
                Console.WriteLine(crsNode.Path.RemoveSegment().ToString());

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

                    Console.WriteLine("Loaded resource descriptor for device " + deviceId);
                }
                else {
                    Console.WriteLine("No resource descriptor for device " + deviceId);
                }
            }
        }

        private static string HidObjectToDeviceId(AcpiObject.AcpiObject obj)
        {
            AcpiObject.AcpiObjectType type =
                (AcpiObject.AcpiObjectType)((AcpiObject.Integer)(obj.ObjectType())).Value;
            string hid;

            if (obj is AcpiObject.Integer)
            {
                // Swap byte order so that all fields are contiguous
                ulong eisaId = ByteOrderSwap((uint)(((AcpiObject.Integer)obj).Value));
                hid = String.Format("{0}{1}{2}{3:X}{4:X}{5:X}{6:X}",
                                    (char)(((eisaId >> 26) & 0x1F) + '@'),
                                    (char)(((eisaId >> 21) & 0x1F) + '@'),
                                    (char)(((eisaId >> 16) & 0x1F) + '@'),
                                    (eisaId >> 12) & 0xF,
                                    (eisaId >> 8) & 0xF,
                                    (eisaId >> 4) & 0xF,
                                    (eisaId >> 0) & 0xF);
            }
            else if (obj is AcpiObject.String) {
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

        private static uint ByteOrderSwap(uint i)
        {
            return (((i >> 24) & 0xFF) << 0) |
                   (((i >> 16) & 0xFF) << 8) |
                   (((i >>  8) & 0xFF) << 16) |
                   (((i >>  0) & 0xFF) << 24);
        }

        private static void PrintResult(AcpiObject.AcpiObject result) {
            Console.WriteLine(result.ToString());
        }
    }
}
