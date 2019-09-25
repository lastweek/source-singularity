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

using TermObj = Microsoft.Singularity.Hal.Acpi.AmlParserUnions.TermObj;
using Microsoft.Singularity.Hal.Acpi.StackIR;
using Microsoft.Singularity.Hal.Acpi.AmlParserUnions;

namespace Microsoft.Singularity.Hal.Acpi.AcpiObject
{
    //
    // Based roughly on Table 17-6 from the ACPI Specification 3.0b, the
    // following class hierarchy describes ACPI objects, which constitute
    // the values assigned to each named node in the ACPI namespace as well
    // as all values assigned to temporary objects, local objects, and so on.
    // They are created and used at both load time and run time.
    //

    /// <summary>
    /// Values returned by ObjectType operator as described in section
    /// 17.5.86 of the ACPI specification 3.0b.
    /// </summary>
    public enum AcpiObjectType
    {
        Uninitialized = 0,
        Integer = 1,
        String = 2,
        Buffer = 3,
        Package = 4,
        FieldUnit = 5,
        Device = 6,
        Event = 7,
        Method = 8,
        Mutex = 9,
        OperationRegion = 10,
        PowerResource = 11,
        Processor = 12,
        ThermalZone = 13,
        BufferField = 14,
        DdbHandle = 15,
        DebugObject = 16
    }

    public abstract class AcpiObject
    {
        public abstract Integer ObjectType();

        public abstract void Write(AcpiObject value);

        /// <summary>
        /// Get the value referred to by this value, for creating indirection.
        /// Returns self for concrete types.
        /// </summary>
        public virtual AcpiObject GetTarget()
        {
            return this;
        }

        public virtual Integer GetAsInt()
        {
            throw new AmlTypeException();
        }

        public virtual String GetAsString()
        {
            throw new AmlTypeException();
        }

        public virtual Buffer GetAsBuffer()
        {
            throw new AmlTypeException();
        }

        public virtual Method GetAsMethod()
        {
            throw new AmlTypeException();
        }

        public virtual Mutex GetAsMutex()
        {
            throw new AmlTypeException();
        }

        public virtual Device GetAsDevice()
        {
            throw new AmlTypeException();
        }

        public virtual ulong Size
        {
            get
            {
                throw new AmlTypeException();
            }
        }

        public virtual AcpiObject Dereference()
        {
            throw new AmlTypeException();
        }

        public virtual AcpiObject Index(ulong index)
        {
            throw new AmlTypeException();
        }

        public virtual AcpiObject[] GetObjects()
        {
            throw new AmlTypeException();
        }

        public virtual void SetIndex(ulong index, AcpiObject value)
        {
            throw new AmlTypeException();
        }
    }

    /// <summary>
    /// Contains a reference to an AcpiObject - this added level of indirection
    /// is necessary to permit AcpiObject objects to be modified through
    /// ObjectReference objects.
    /// </summary>
    public class AcpiObjectCell
    {
        AcpiObject containedValue;

        public AcpiObjectCell(AcpiObject containedValue)
        {
            this.containedValue = containedValue;
        }

        public AcpiObject Value
        {
            get
            {
                return containedValue;
            }
            set
            {
                if (containedValue is UninitializedObject) {
                    containedValue = value;
                }
                else {
                    containedValue.Write(value);
                }
            }
        }
    }

    /// <summary>
    /// An uninitialized ACPI object.
    /// </summary>
    /// <remarks>From Table 17-6: No assigned type or value. This is the type
    /// of all control method LocalX variables and unused ArgX variables at
    /// the beginning of method execution, as well as all uninitialized
    /// Package elements. Uninitialized objects must be initialized (via
    /// Store or CopyObject) before they may be used as source operands in
    /// ASL expressions.</remarks>
    public class UninitializedObject : AcpiObject
    {
        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.Uninitialized);
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("Cannot write to uninitialized object");
        }
    }

    /// <summary>
    /// An ACPI buffer object representing an array of bytes.
    /// </summary>
    /// <remarks>From Table 17-6: An array of bytes. Uninitialized elements
    /// are zero by default.</remarks>
    public class Buffer : AcpiObject
    {
        byte[] contents;

        public Buffer(byte[] contents)
        {
            this.contents = contents;
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.Buffer);
        }

        public override AcpiObject Index(ulong index)
        {
            return new Integer(contents[index]);
        }

        public override void SetIndex(ulong index, AcpiObject value)
        {
            contents[index] = (byte)value.GetAsInt().Value;
        }

        public byte[] Contents
        {
            get
            {
                return (byte[])contents.Clone();
            }
        }

        public override Buffer GetAsBuffer()
        {
            return this;
        }

        public override string ToString()
        {
            StringBuilder result = new StringBuilder();
            result.Append("{");
            bool first = true;
            foreach (byte b in contents) {
                if (first) {
                    first = false;
                }
                else {
                    result.Append(", ");
                }
                result.Append(b.ToString("x"));
            }
            result.Append("}");
            return result.ToString();
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("TODO");
        }
    }

    /// <summary>
    /// An ACPI buffer field object representing a portion of a buffer.
    /// </summary>
    /// <remarks>From Table 17-6: Portion of a buffer created using
    /// CreateBitField, CreateByteField, CreateWordField, CreateQWordField,
    /// CreateField, or returned by the Index operator.</remarks>
    public class BufferField : AcpiObject
    {
        AcpiObject sourceBuffer = null;
        ulong startBitIndex;
        ulong numBits;

        public BufferField(AcpiObject sourceBuffer, ulong startBitIndex, ulong numBits)
        {
            if (numBits > sizeof(ulong) * 8) {
                throw new AmlTypeException("Tried to create field with more than maximum number of bits");
            }

            this.sourceBuffer = sourceBuffer;
            this.startBitIndex = startBitIndex;
            this.numBits = numBits;
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.BufferField);
        }

        public override Integer GetAsInt()
        {
            return (Integer)Dereference();
        }

        public override AcpiObject Dereference()
        {
            if ((startBitIndex % 8) != 0 || (numBits % 8) != 0) {
                throw new AmlTypeException("TODO: Non-byte-aligned buffer fields");
            }

            ulong result = 0;
            // Loop from first byte to last
            for(ulong idx = startBitIndex/8u; idx < startBitIndex/8u + numBits/8u; idx++) {
                result = (result << 8) | sourceBuffer.Index(idx).GetAsInt().Value;
            }
            return new Integer(result);
        }

        public override void Write(AcpiObject valueObj)
        {
            if ((startBitIndex % 8) != 0 || (numBits % 8) != 0) {
                throw new AmlTypeException("TODO: Non-byte-aligned buffer fields");
            }

            ulong value = valueObj.GetAsInt().Value;

            // We ignore high bits above the number of bits fitting in the field.
            // Used to check this, but some code actually depends on the behavior of
            // truncating high bits, like this from VPC:

            // Method (_CRS, 0, NotSerialized)
            // {
            //     CreateDWordField (CRS, \_SB.SYSM._Y10._BAS, BAS4)
            //     CreateDWordField (CRS, \_SB.SYSM._Y10._LEN, LEN4)
            //     Subtract (0x00, BAS4, LEN4)
            // }

            // NB write in little endian byte-order
            ulong end = startBitIndex/8u + numBits/8u;
            for (ulong idx = startBitIndex / 8u; idx < end; idx++) {
                sourceBuffer.SetIndex(idx, new Integer(value & 0xFF));
                value >>= 8;
            }
        }
    }

    /// <summary>
    /// An ACPI DDB handle object referring to a Differentiated Definition Block.
    /// </summary>
    /// <remarks>From Table 17-6: Definition block handle returned
    /// by the Load operator [and passed to the Unload operator].</remarks>
    public class DdbHandle : AcpiObject
    {
        // TODO: The representation of this will come from the table loading code
        // and depend on the implementation of Load and Unload.

        private DdbHandle() { } // Prevent construction until completed

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.DdbHandle);
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("TODO");
        }
    }

    /// <summary>
    /// An ACPI debug object used for formatting and printing debug output.
    /// </summary>
    /// <remarks>From Table 17-6: Debug output object. Formats an object
    /// and prints it to the system debug port. Has no effect if debugging
    /// is not active. Section 17.5.23: The debug data object is a virtual
    /// data object. Writes to this object provide debugging information.
    /// On at least debug versions of the interpreter, any writes into this
    /// object are appropriately displayed on the system’s native kernel
    /// debugger. All writes to the debug object are otherwise benign. If
    /// the system is in use without a kernel debugger, then writes to the
    /// debug object are ignored.</remarks>
    public class DebugObject : AcpiObject
    {
        private DebugObject() { }

        public readonly DebugObject Instance = new DebugObject();

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.DebugObject);
        }

        public override void Write(AcpiObject value)
        {
#if SINGULARITY_KERNEL
            DebugStub.Write(value.ToString());
#else
            Console.Write(value.ToString());
#endif
        }
    }

    /// <summary>
    /// An ACPI device object representing a device or bus.
    /// </summary>
    /// <remarks>From Table 17-6: Device or bus object</remarks>
    public class Device : AcpiObject
    {
        AcpiNamespace.AbsoluteNodePath path;

        public Device(AcpiNamespace.AbsoluteNodePath path)
        {
            this.path = path;
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.Device);
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("TODO");
        }

        public AcpiNamespace.AbsoluteNodePath Path
        {
            get
            {
                return path;
            }
        }

        public override Device GetAsDevice()
        {
            return this;
        }
    }

    /// <summary>
    /// An ACPI event synchronization object
    /// </summary>
    /// <remarks>From Table 17-6: Event synchronization object</remarks>
    public class Event : AcpiObject
    {
        public Event()
        {
            // No data - an event is described entirely by its name
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.Event);
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("TODO");
        }
    }

    //
    // Enums based on FieldFlags rule in AML grammar,
    // ACPI specification 3.0b section 18.2.5.2
    //

    public enum AccessType
    {
        AnyAcc = 0,
        ByteAcc = 1,
        WordAcc = 2,
        DWordAcc = 3,
        QWordAcc = 4,
        BufferAcc = 5,
        Reserved1 = 6,
        Reserved2 = 7,
        Reserved3 = 8,
        Reserved4 = 9,
        Reserved5 = 10,
        Reserved6 = 11,
        Reserved7 = 12,
        Reserved8 = 13,
        Reserved9 = 14,
        Reserved10 = 15
    }

    public enum LockRule
    {
        NoLock = 0,
        Lock = 1
    }

    public enum UpdateRule
    {
        Preserved = 0,
        WriteAsOnes = 1,
        WriteAsZeros = 2,
        Invalid = 3
    }

    public enum AccessAttrib
    {
        SMBNone               = 0x00,
        SMBQuick              = 0x02,
        SMBSendReceive        = 0x04,
        SMBByte               = 0x06,
        SMBWord               = 0x08,
        SMBBlock              = 0x0A,
        SMBProcessCall        = 0x0C,
        SMBBlockProcessCall   = 0x0D
    }

    /// <summary>
    /// An ACPI field unit object referring to a portion of an address space.
    /// </summary>
    /// <remarks>From Table 17-6: (within an Operation Region) Portion of an
    /// address space, bit-aligned and of one-bit granularity. Created using
    /// Field, BankField, or IndexField.</remarks>
    public class FieldUnit : AcpiObject
    {
        OperationRegion operationRegion;
        int startBitIndex;
        int numBits;
        AccessType accessType;
        AccessAttrib accessAttrib;
        LockRule lockRule;
        UpdateRule updateRule;

        public FieldUnit(OperationRegion operationRegion, int startBitIndex, int numBits,
                         AccessType accessType, AccessAttrib accessAttrib,
                         LockRule lockRule, UpdateRule updateRule)
        {
            if (startBitIndex < 0 || (startBitIndex + numBits + 7)/8 > (int)operationRegion.Length) {
                throw new ArgumentException("Field unit not in bounds of operation region");
            }

            this.operationRegion = operationRegion;
            this.startBitIndex = startBitIndex;
            this.numBits = numBits;
            this.accessType = accessType;
            this.accessAttrib = accessAttrib;
            this.lockRule = lockRule;
            this.updateRule = updateRule;
        }

        public override Integer GetAsInt()
        {
            return new Integer(Read());
        }

        public override Buffer GetAsBuffer()
        {
            if ((startBitIndex % 8) == 0) {
                return new Buffer(operationRegion.ReadBytes((ulong)(startBitIndex / 8),
                                                            (ulong)(numBits + 7)/8));
            }
            else {
                throw new Exception("Unimplemented conversion of unaligned field to buffer");
            }
        }

        public ulong Read()
        {
            if (numBits == 8 && (startBitIndex % 8) == 0) {
                return operationRegion.Read8At((ulong)(startBitIndex / 8));
            }
            else if (numBits == 16 && (startBitIndex % 8) == 0) {
                return operationRegion.Read16At((ulong)(startBitIndex / 8));
            }
            else if (numBits == 32 && (startBitIndex % 8) == 0) {
                return operationRegion.Read32At((ulong)(startBitIndex / 8));
            }
            else {
                // Small field or unaligned, do general case
                int bitIndex = startBitIndex;
                int remainingBits = numBits;

                uint result = 0;
                while (remainingBits > 0) {
                    byte b = operationRegion.Read8At((ulong)(bitIndex / 8));
                    for (int bitInWord = bitIndex % 8;
                         bitInWord < 8 && remainingBits > 0;
                         bitInWord++, bitIndex++, remainingBits--) {
                        result = (result << 1) | (uint)((b >> (7 - bitInWord)) & 1);
                    }
                }

                return result;
            }
        }

        /// <summary>
        /// This is currently just used by IndexField, will probably become accessible
        /// from AML when implementing stores.
        /// </summary>
        public override void Write(AcpiObject valueObj)
        {
            ulong value = valueObj.GetAsInt().Value;

            Debug.Assert(AcpiObjectUtils.GetNumBits(value) <= (ulong)numBits, "Writing value too large for field");

            if (numBits == 8 && (startBitIndex % 8) == 0) {
                operationRegion.Write8At((ulong)(startBitIndex / 8), (byte)value);
            }
            else if (numBits == 16 && (startBitIndex % 8) == 0) {
                operationRegion.Write16At((ulong)(startBitIndex / 8), (byte)value);
            }
            else if (numBits == 32 && (startBitIndex % 8) == 0) {
                operationRegion.Write32At((ulong)(startBitIndex / 8), (byte)value);
            }
            else {
                throw new Exception("Unimplemented operation region field size");
            }
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.FieldUnit);
        }

        // SortedList will be Dictionary<string, FieldUnit> when generics are available
        public static SortedList CreateFromFieldList(OperationRegion operationRegionNode,
                                                     FieldElement[] fieldList,
                                                     AccessType initialAccessType,
                                                     AccessAttrib initialAccessAttrib,
                                                     LockRule lockRule,
                                                     UpdateRule updateRule
                                                    )
        {
            SortedList result = new SortedList(); // = new Dictionary<string, FieldUnit>();
            AccessType accessType = initialAccessType;
            AccessAttrib accessAttrib = initialAccessAttrib;
            int bitIndex = 0;

            foreach (FieldElement fieldElement in fieldList) {
                switch (fieldElement.Tag) {
                    case FieldElement.TagValue.NamedField:
                        AmlParser.NamedField namedField = fieldElement.GetAsNamedField();
                        result.Add(namedField.nameSeg.data,
                                   new FieldUnit(operationRegionNode,
                                                 bitIndex, namedField.bitWidth,
                                                 accessType, accessAttrib, lockRule, updateRule));
                        bitIndex += namedField.bitWidth;
                        break;
                    case FieldElement.TagValue.ReservedField:
                        AmlParser.ReservedField reservedField = fieldElement.GetAsReservedField();
                        bitIndex += reservedField.bitWidth;
                        break;
                    case FieldElement.TagValue.AccessField:
                        AmlParser.AccessField accessField = fieldElement.GetAsAccessField();
                        accessType   = accessField.accessType;
                        accessAttrib = accessField.accessAttrib;
                        break;
                    default:
                        throw new LoadException("Unhandled alternative in switch over 'FieldElement'");
                }
            }

            return result;
        }
    }

    /// <summary>
    /// This operation region accessor accesses internal device registers
    /// through an index/data pair (typically a pair of I/O ports inside an
    /// I/O operation region). It is used by IndexField definitions, which
    /// create FieldUnits inside these internal operation regions. The
    /// RegionSpace type is ignored.
    /// </summary>
    public class IndexFieldOperationRegionAccessor : IOperationRegionAccessor
    {
        FieldUnit index;
        FieldUnit data;

        public IndexFieldOperationRegionAccessor(FieldUnit index, FieldUnit data)
        {
            this.index = index;
            this.data = data;
        }

        public byte Read8(RegionSpace regionSpace, ulong offset)
        {
            index.Write(new Integer(offset));
            return (byte)data.Read();
        }

        public void Write8(RegionSpace regionSpace, ulong offset, byte value)
        {
            index.Write(new Integer(offset));
            data.Write(new Integer(value));
        }

        public ushort Read16(RegionSpace regionSpace, ulong offset)
        {
            index.Write(new Integer(offset));
            return (ushort)data.Read();
        }

        public void Write16(RegionSpace regionSpace, ulong offset, ushort value)
        {
            index.Write(new Integer(offset));
            data.Write(new Integer(value));
        }

        public uint Read32(RegionSpace regionSpace, ulong offset)
        {
            index.Write(new Integer(offset));
            return (uint)data.Read();
        }

        public void Write32(RegionSpace regionSpace, ulong offset, uint value)
        {
            index.Write(new Integer(offset));
            data.Write(new Integer(value));
        }

        public byte[] ReadBytes(RegionSpace regionSpace, ulong offset, ulong length)
        {
            throw new Exception("Unimplemented ReadBytes() from index field");
        }
    }

    /// <summary>
    /// An ACPI integer object
    /// </summary>
    /// <remarks>From Table 17-6: An n-bit little-endian unsigned integer.
    /// In ACPI 1.0 this was at least 32 bits. In ACPI 2.0 and later, this
    /// is 64 bits.</remarks>
    public class Integer : AcpiObject
    {
        ulong value;

        public Integer(ulong value)
        {
            this.value = value;
        }

        public ulong Value
        {
            get
            {
                return value;
            }
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.Integer);
        }

        public override Integer GetAsInt()
        {
            if (this == IntegerConstant.Zero ||
                this == IntegerConstant.One ||
                this == IntegerConstant.Ones) {
                // Reading an IntegerConstant does not get the singleton object
                // but just the value in it.
                return new Integer(value);
            }
            return this;
        }

        public override void Write(AcpiObject value)
        {
            if (this == IntegerConstant.Zero ||
                this == IntegerConstant.One ||
                this == IntegerConstant.Ones) {
                throw new AmlTypeException("Cannot write to reserved integer constant objects");
            }
            this.value = value.GetAsInt().Value;
        }

        public override string ToString()
        {
            return value.ToString();
        }
    }

    /// <summary>
    /// Wrapper class for some static methods referring to ACPI integer
    /// constant built-in integer constants.
    /// </summary>
    /// <remarks>From Table 17-6: Created by the ASL terms "Zero", "One",
    /// "Ones", and "Revision". We did not create a subclass for these
    /// because ObjectType has no "IntegerConstant" type, only Integer.</remarks>
    public class IntegerConstant
    {
        private IntegerConstant() { } // Don't allow construction

        public readonly static Integer Zero     = new Integer(0UL);
        public readonly static Integer One      = new Integer(1UL);
        public readonly static Integer Ones     = new Integer(~(0UL));
        public readonly static Integer Revision = new Integer(0); // TODO: What's the right value for this?
    }

    //
    // Enum based on MethodFlags rule in AML grammar,
    // ACPI specification 3.0b section 18.2.5.2
    //

    public enum SerializeFlag
    {
        NotSerialized = 0,
        Serialized = 1
    }

    /// <summary>
    /// An ACPI method object referring to an invokable method.
    /// </summary>
    /// <remarks>From Table 17-6: Control Method (Executable AML function)</remarks>
    public abstract class Method : AcpiObject
    {
        byte argCount;
        SerializeFlag serializeFlag;
        byte syncLevel;

        public Method(byte argCount, SerializeFlag serializeFlag, byte syncLevel)
        {
            this.argCount = argCount;
            this.serializeFlag = serializeFlag;
            this.syncLevel = syncLevel;
        }

        public byte ArgCount
        {
            get
            {
                return argCount;
            }
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.Method);
        }

        public override Method GetAsMethod()
        {
            return this;
        }

        public abstract void Invoke(AmlInterpreterThread thread, AcpiObject[] parameters, AcpiNamespace acpiNamespace);

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("Cannot write to method");
        }
    }

    /// <summary>
    /// A method whose body is represented using AML bytecode which can be parsed
    /// and interpreted.
    /// </summary>
    public class BytecodeMethod : Method
    {
        byte[] unparsedTermList;
        StackIRNode[] body;

        public BytecodeMethod(byte argCount, SerializeFlag serializeFlag, byte syncLevel, byte[] unparsedTermList)
            : base(argCount, serializeFlag, syncLevel)
        {
            this.unparsedTermList = unparsedTermList;
            this.body = null;
        }

        public AmlParser.ParseSuccess Parse(AcpiNamespace acpiNamespace, AcpiNamespace.AbsoluteNodePath initialNodePath)
        {
            int offset = 0;
            TermObj[] termList;
            if (new AmlParser(new ByteBufferAmlStreamAdapter(unparsedTermList), acpiNamespace, initialNodePath).
                ParseTermList(out termList, ref offset, unparsedTermList.Length) == AmlParser.ParseSuccess.Failure) {
                return AmlParser.ParseSuccess.Failure;
            }
            Debug.Assert(offset == unparsedTermList.Length, "offset == unparsedTermList.Length");

            AmlToStackIRVisitor amlToStackIRVisitor = new AmlToStackIRVisitor();
            amlToStackIRVisitor.VisitSequence(termList);
            body = amlToStackIRVisitor.Result;

            return AmlParser.ParseSuccess.Success;
        }

        public override void Invoke(AmlInterpreterThread thread, AcpiObject[] parameters, AcpiNamespace acpiNamespace)
        {
            if (body == null) {
                AcpiNamespace.Node node = acpiNamespace.FindValue(this);
                if (Parse(acpiNamespace, node.Path) == AmlParser.ParseSuccess.Failure) {
                    throw new InterpretException("AML parser failure while just-in-time parsing AML method body");
                }
            }
            thread.PushFrame(new AmlStackFrame(body, parameters));
        }
    }

    /// <summary>
    /// A reserved method implemented directly by the operating system.
    /// </summary>
    public class ReservedMethod : Method
    {
        public delegate AcpiObject AcpiMethodImpl(AcpiObject[] arguments);

        private AcpiMethodImpl impl;

        public ReservedMethod(byte argCount, SerializeFlag serializeFlag, byte syncLevel, AcpiMethodImpl impl)
            : base(argCount, serializeFlag, syncLevel)
        {
            this.impl = impl;
        }

        public override void Invoke(AmlInterpreterThread thread, AcpiObject[] parameters, AcpiNamespace acpiNamespace)
        {
            thread.Push(new ValueIoLocation(impl(parameters)));
        }
    }

    /// <summary>
    /// An ACPI mutex synchronization object
    /// </summary>
    /// <remarks>From Table 17-6: Mutex synchronization object</remarks>
    public class Mutex : AcpiObject
    {
        private class AmlInterpreterThreadSet : IEnumerable
        {
            ArrayList set = new ArrayList();

            public void Add(AmlInterpreterThread thread) {
                set.Add(thread);
            }

            public IEnumerator GetEnumerator() {
                return set.GetEnumerator();
            }

            public void Clear() {
                set.Clear();
            }
        }

        byte syncLevel;
        AmlInterpreterThread owner = null;
        AmlInterpreterThreadSet waitingThreads = new AmlInterpreterThreadSet();

        public Mutex(byte syncLevel)
        {
            this.syncLevel = syncLevel;
        }

        public void Acquire(AmlInterpreterThread thread) {
            if (owner == null) {
                owner = thread;
            }
            else {
                waitingThreads.Add(thread);
                thread.Block();
            }
        }

        public void Release(AmlInterpreterThread thread) {
            if (owner == null) {
                throw new InterpretException("Attempt to release unlocked mutex");
            }
            owner = null;

            foreach (AmlInterpreterThread waitingThread in waitingThreads) {
                waitingThread.Notify();
            }
            waitingThreads.Clear();
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.Mutex);
        }

        public override Mutex GetAsMutex()
        {
            return this;
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("Cannot write to mutex");
        }
    }

    /// <summary>
    /// See AmlLoader.LoadTimeEvaluate(AmlParser.UserTermObj userTermObj)
    /// for an explanation of the existence of this object type, which is
    /// not defined in the specification.
    /// </summary>
    public class NodePathReference : AcpiObject
    {
        private AcpiNamespace acpiNamespace;
        private AcpiNamespace.AbsoluteNodePath nodePath;

        public NodePathReference(AcpiNamespace acpiNamespace,
                                 AcpiNamespace.AbsoluteNodePath nodePath)
        {
            this.acpiNamespace = acpiNamespace;
            this.nodePath = nodePath;
        }

        public override Integer ObjectType()
        {
            return GetTarget().ObjectType();
        }

        public override AcpiObject GetTarget()
        {
            return acpiNamespace.LookupNode(nodePath).Value;
        }

        public override Integer GetAsInt()
        {
            return GetTarget().GetAsInt();
        }

        public override Device GetAsDevice()
        {
            return GetTarget().GetAsDevice();
        }

        public override void Write(AcpiObject value)
        {
            GetTarget().Write(value);
        }
    }

    /// <summary>
    /// An ACPI object reference object referring to some other AcpiObject
    /// </summary>
    /// <remarks>From Table 17-6: Reference to an object created using the
    /// RefOf, Index, or CondRefOf operators</remarks>
    public class ObjectReference : AcpiObject
    {
        AcpiObjectCell target;

        public ObjectReference(AcpiObjectCell target)
        {
            this.target = target;
        }

        public override Integer ObjectType()
        {
            // From 17.5.86: if this operation is performed on an object
            // reference [...] the object type of the base object is returned.
            return GetTarget().ObjectType();
        }

        public override AcpiObject GetTarget()
        {
            return target.Value;
        }

        public override Integer GetAsInt()
        {
            return GetTarget().GetAsInt();
        }

        public override Device GetAsDevice()
        {
            return GetTarget().GetAsDevice();
        }

        public override void Write(AcpiObject value)
        {
            GetTarget().Write(value);
        }
    }

    /// <summary>
    /// From 17.5.89, describes the built-in region spaces in which an
    /// operation region can be created.
    /// </summary>
    public enum RegionSpace
    {
        SystemMemory = 0,
        SystemIO = 1,
        PCI_Config = 2,
        EmbeddedControl = 3,
        SMBus = 4,
        CMOS = 5,
        PCIBARTarget = 6
    }

    /// <summary>
    /// Abstracts away reading of operation regions such as arbitrary
    /// memory read/writes, I/O, and PCI configuration space access.
    /// </summary>
    public interface IOperationRegionAccessor
    {
        byte[] ReadBytes(RegionSpace regionSpace, ulong offset, ulong length);
        byte Read8(RegionSpace regionSpace, ulong offset);
        void Write8(RegionSpace regionSpace, ulong offset, byte value);
        ushort Read16(RegionSpace regionSpace, ulong offset);
        void Write16(RegionSpace regionSpace, ulong offset, ushort value);
        uint Read32(RegionSpace regionSpace, ulong offset);
        void Write32(RegionSpace regionSpace, ulong offset, uint value);
    }

    /// <summary>
    /// An ACPI operation region object, representing a region within an
    /// address space.
    /// </summary>
    /// <remarks>From Table 17-6: Reference to an object created using the
    /// RefOf, Index, or CondRefOf operators</remarks>
    public class OperationRegion : AcpiObject
    {
        IOperationRegionAccessor accessor;
        RegionSpace regionSpace;
        ulong startByteIndex;
        ulong numBytes;

        public OperationRegion(IOperationRegionAccessor accessor,
                               RegionSpace regionSpace, ulong startByteIndex, ulong numBytes)
        {
            this.accessor = accessor;
            this.regionSpace = regionSpace;
            this.startByteIndex = startByteIndex;
            this.numBytes = numBytes;
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.OperationRegion);
        }

        public ulong Length
        {
            get
            {
                return numBytes;
            }
        }

        //
        // These should only be used by FieldUnit.
        //

        public byte[] ReadBytes(ulong offset, ulong length)
        {
            if (offset < 0 || offset + length > numBytes) {
                throw new ArgumentOutOfRangeException();
            }
            return accessor.ReadBytes(regionSpace, startByteIndex + offset, length);
        }

        public byte Read8At(ulong offset)
        {
            if (offset < 0 || offset >= numBytes) {
                throw new ArgumentOutOfRangeException();
            }
            return accessor.Read8(regionSpace, startByteIndex + offset);
        }

        public uint Read16At(ulong offset)
        {
            if (offset < 0 || offset >= numBytes) {
                throw new ArgumentOutOfRangeException();
            }
            return accessor.Read16(regionSpace, startByteIndex + offset);
        }

        public uint Read32At(ulong offset)
        {
            if (offset < 0 || offset >= numBytes) {
                throw new ArgumentOutOfRangeException();
            }
            return accessor.Read32(regionSpace, startByteIndex + offset);
        }

        public void Write8At(ulong offset, byte value)
        {
            if (offset < 0 || offset >= numBytes) {
                throw new ArgumentOutOfRangeException();
            }
            accessor.Write8(regionSpace, startByteIndex + offset, value);
        }

        public void Write16At(ulong offset, ushort value)
        {
            if (offset < 0 || offset >= numBytes) {
                throw new ArgumentOutOfRangeException();
            }
            accessor.Write16(regionSpace, startByteIndex + offset, value);
        }

        public void Write32At(ulong offset, uint value)
        {
            if (offset < 0 || offset >= numBytes) {
                throw new ArgumentOutOfRangeException();
            }
            accessor.Write32(regionSpace, startByteIndex + offset, value);
        }

        public override void Write(AcpiObject value)
        {
            // Must first create fields inside operation region and then write to those
            throw new AmlTypeException("Cannot write directly to operation region");
        }
    }

    /// <summary>
    /// An ACPI package object, a fixed-length list of other AcpiObject objects
    /// </summary>
    /// <remarks>From Table 17-6: Collection of ASL objects with a fixed
    /// number of elements (up to 255).</remarks>
    public class Package : AcpiObject
    {
        AcpiObjectCell[] objectList;

        public Package(AcpiObjectCell[] objectList)
        {
            this.objectList = objectList;
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.Package);
        }

        public override AcpiObject Index(ulong index)
        {
            return objectList[index].Value;
        }

        public override AcpiObject[] GetObjects()
        {
            AcpiObject[] result = new AcpiObject[objectList.Length];
            for (ulong index = 0; index < (ulong) objectList.Length; index++) {
                result[index] = this.Index(index);
            }
            return result;
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("Cannot write to package object");
        }
    }

    /// <summary>
    /// An ACPI power resource description object.
    /// </summary>
    /// <remarks>From Table 17-6: Power Resource description object</remarks>
    public class PowerResource : AcpiObject
    {
        public byte systemLevel;
        public int resourceOrder;

        public PowerResource(byte systemLevel, int resourceOrder)
        {
            this.systemLevel = systemLevel;
            this.resourceOrder = resourceOrder;
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.PowerResource);
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("Cannot write to power resource object");
        }
    }

    /// <summary>
    /// An ACPI processor description object.
    /// </summary>
    /// <remarks>From Table 17-6: Processor description object. See
    /// section 17.5.93.</remarks>
    public class Processor : AcpiObject
    {
        byte processorId;
        uint pblkAddress;
        byte pblkLength;

        public Processor(byte processorId, uint pblkAddress, byte pblkLength)
        {
            this.processorId = processorId;
            this.pblkAddress = pblkAddress;
            this.pblkLength = pblkLength;
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.Processor);
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("Cannot write to processor object");
        }
    }

    /// <summary>
    /// An ACPI string object.
    /// </summary>
    /// <remarks>From Table 17-6: Null-terminated ASCII string.</remarks>
    public class String : AcpiObject
    {
        string contents;

        public String(string contents)
        {
            for (int i = 0; i < contents.Length; i++) {
                if (contents[i] == '\0') {
                    Debug.Assert(false, "ACPI string contains embedded null");
                }
            }
            this.contents = contents;
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.String);
        }

        public override ulong Size
        {
            get
            {
                return (ulong)contents.Length;
            }
        }

        public override AcpiObject Index(ulong index)
        {
            return new Integer(contents[(int)index]);
        }

        public string Value
        {
            get
            {
                return contents;
            }
        }

        public override String GetAsString()
        {
            return this;
        }

        public override string ToString()
        {
            return contents;
        }

        public override void Write(AcpiObject value)
        {
            this.contents = value.GetAsString().Value;
        }
    }

    /// <summary>
    /// An ACPI thermal zone description object.
    /// </summary>
    /// <remarks>From Table 17-6: Thermal Zone description object</remarks>
    public class ThermalZone : AcpiObject
    {
        public ThermalZone()
        {
            // No data - a thermal zone is described entirely by its name and children
        }

        public override Integer ObjectType()
        {
            return new Integer((ulong)AcpiObjectType.ThermalZone);
        }

        public override void Write(AcpiObject value)
        {
            throw new AmlTypeException("Cannot write to thermal zone object");
        }
    }

    internal class AcpiObjectUtils
    {
        public static ulong GetNumBits(ulong value)
        {
            ulong numBits = 0;
            while (value != 0) {
                value >>= 1;
                numBits++;
            }
            return numBits;
        }
    }
}
