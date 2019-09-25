// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

namespace System
{
    using System.Reflection;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using Microsoft.Bartok.Runtime;

#if false
    [StructLayout(LayoutKind.Sequential)]
    [AccessedByRuntime("ok")]
    sealed class RuntimeType : Type
    {
        private int _pData = 0;
        [RequiredByBartok]
        private readonly Module module;
        [RequiredByBartok]
        private readonly String enclosingTypeName;
        [RequiredByBartok]
        private readonly String name;
        [RequiredByBartok]
        private readonly RuntimeType[] genericTypeArguments;
        [RequiredByBartok]
        private readonly String nameSpace;
        [RequiredByBartok]
        internal readonly RuntimeType baseType;
        [RequiredByBartok]
        internal readonly RuntimeType[] interfaces;

        [RequiredByBartok]
        internal readonly VTable classVtable;
        [NoHeapAllocation]
        public override bool IsSubclassOf(Type c) { throw null; }
        public override String Name {
            [NoHeapAllocation]
            get { throw null; }
        }
        public override String FullName {
            [NoHeapAllocation]
            get { throw null; }
        }
        public override String AssemblyQualifiedName {
            [NoHeapAllocation]
            get { throw null; }
        }
        public override Type BaseType {
            [NoHeapAllocation]
            get { throw null; }
        }
        [NoHeapAllocation]
        public override int GetArrayRank() { throw null; }
        [NoHeapAllocation]
        public override Type[] GetInterfaces() { throw null; }
        [NoHeapAllocation]
        protected override bool IsArrayImpl() { throw null; }
        [NoHeapAllocation]
        protected override bool IsPrimitiveImpl() { throw null; }
        [NoHeapAllocation]
        public override Type GetElementType() { throw null; }
        [NoHeapAllocation]
        protected override bool HasElementTypeImpl() { throw null; }
        public override String Namespace {
            [NoHeapAllocation]
            get { throw null; }
        }
        public override Type UnderlyingSystemType {
            [NoHeapAllocation]
            get { throw null; }
        }
    }
#endif

    public sealed class LocalDataStoreSlot {}
    public class WeakReference {}
    public struct TypedReference {}
    public delegate void AsyncCallback(IAsyncResult result);
    public sealed class STAThreadAttribute : Attribute {}
    //class Encoding {}
    public static class Convert {
        public static char ToChar(int value) { return (char)value; } // TODO
        public static int ToInt32(char value) { return value; }
    }
    public class EventSource {
    }

    [RequiredByBartok]
    internal struct InterfaceInfo {
        [RequiredByBartok]
        internal System.RuntimeType type;
        [RequiredByBartok]
        internal IntPtr offset;
    }

    public enum StructuralType {
        None            = 0x00,
        Reference       = 0x01,
        UntracedPointer = 0x02,
        Struct          = 0x03,
        Bool            = 0x04,
        Char            = 0x05,
        Int8            = 0x06,
        Int16           = 0x07,
        Int32           = 0x08,
        Int64           = 0x09,
        UInt8           = 0x0a,
        UInt16          = 0x0b,
        UInt32          = 0x0c,
        UInt64          = 0x0d,
        Float32         = 0x0e,
        Float64         = 0x0f,
        IntPtr          = 0x10,
        UIntPtr         = 0x11,
        Void            = 0x12,
    };

    public enum StringState {
        Undetermined =  0, // Undetermined == 0 assumed in MultiUseWord.cs
        HighChars =     8,
        FastOps =      16,
        SpecialSort =  24,
    }

    [StructLayout(LayoutKind.Sequential)]
    [AccessedByRuntime("ok")]
    class VTable
    {
        static bool enableLibraryOptions;
        static internal void throwNewArgumentOutOfRangeException() {throw new ArgumentOutOfRangeException();}
        static internal void DebugBreak() {throw null;}

        [RequiredByBartok]
        [NoBarriers]
        public readonly VTable depth1;
        [NoBarriers]
        [RequiredByBartok]
        public readonly VTable depth2;
        [NoBarriers]
        [RequiredByBartok]
        public readonly VTable depth3;
        [NoBarriers]
        [RequiredByBartok]
        public readonly VTable depth4;
        [NoBarriers]
        [RequiredByBartok]
        public readonly VTable depth5;
        [NoBarriers]
        [RequiredByBartok]
        public readonly VTable depth6;
        [NoBarriers]
        public VTable posCache;
        [RequiredByBartok]
        [NoBarriers]
        public int depth;
        [RequiredByBartok]
        [NoBarriers]
        public readonly StructuralType arrayOf;

        // May be the element type of an array OR the referent type of a pointer
        [RequiredByBartok]
        [NoBarriers]
        public readonly VTable elementVTable;

        [RequiredByBartok]
        [NoBarriers]
        public readonly int arrayElementSize;
        [RequiredByBartok]
        [NoBarriers]
        public readonly InterfaceInfo[] interfaces;
        [RequiredByBartok]
        [NoBarriers]
        public readonly uint baseLength;
        [RequiredByBartok]
        [NoBarriers]
        public readonly uint baseAlignment;
        [RequiredByBartok]
        [NoBarriers]
        public readonly UIntPtr pointerTrackingMask;
        [RequiredByBartok]
        [NoBarriers]
        public readonly StructuralType structuralView;
        [AccessedByRuntime("ok")]
        [NoBarriers]
        public readonly RuntimeType vtableType;
        [RequiredByBartok]
        [NoBarriers]
        public readonly int marshalSize;
        [RequiredByBartok]
        [NoBarriers]
        public readonly VTable vectorClass;

        // This method is generated by Bartok.
        // It calls all the auto init class constructors.
        [MethodImpl(MethodImplOptions.InternalCall)]
        [RequiredByBartok]
        internal static extern void Initialize();

        [NoInline]
        [RequiredByBartok]
        internal static void throwNewIndexOutOfRangeException() {
            throw new IndexOutOfRangeException();
        }

        [NoInline]
        [RequiredByBartok]
        internal static void throwNewOverflowException() {
            throw new OverflowException();
        }

        [NoInline]
        [RequiredByBartok]
        internal static void throwNewDivideByZeroException() {
            throw new DivideByZeroException();
        }

        [NoInline]
        [RequiredByBartok]
        internal static void throwNewArithmeticException() {
            throw new ArithmeticException();
        }

        [NoInline]
        [RequiredByBartok]
        internal static void throwNewStringIndexOutOfRangeException() {
            throw new ArgumentOutOfRangeException();
        }

        //[RequiredByBartok]
        //[CalledRarely]
        //internal extern static void initType(RuntimeType ty);

        [System.Diagnostics.Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        [NoStackLinkCheckTrans]
        public static void Assert(bool expr) {
            if (VTable.enableLibraryOptions && EnableLibraryAsserts() && !expr) {
                failAssert(null);
            }
        }

        [System.Diagnostics.Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        public static void Assert(bool expr, String s) {
            if (VTable.enableLibraryOptions && EnableLibraryAsserts() && !expr) {
                failAssert(s);
            }
        }

        public static void NotReached(String s) {
            throw new Exception(s);
        }

        [NoHeapAllocation]
        public static bool EnableLibraryAsserts() {
            return(true);
        }

        [NoStackLinkCheckTransCut]
        [NoHeapAllocation]
        private static void failAssert(String s) {
            throw new Exception(s);
        }

        [Intrinsic]
        internal static extern ulong mulUIntUIntToULong(uint x, uint y);

        [RequiredByBartok]
        // unsigned 64-bit multiplication with no overflow checking
        static public ulong mulUnsigned64Bit(ulong x,ulong y) {
            uint loX = (uint) x;
            uint hiX = (uint) (x >> 32);
            uint loY = (uint) y;
            uint hiY = (uint) (y >> 32);
            ulong result = mulUIntUIntToULong(loY, loX);
            result =  result + (((ulong) (loX * hiY)) << 32);
            result =  result + (((ulong) (loY * hiX)) << 32);
            return result;
        }
    }

    class GC
    {
        // Placeholder for Bartok (real definitions provided by TAL checker)
        [InterruptsDisabled]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        extern private static Object AllocateObject(VTable vtable);

        // Placeholder for Bartok (real definitions provided by TAL checker)
        [InterruptsDisabled]
        [RequiredByBartok]
        [MethodImpl(MethodImplOptions.InternalCall)]
        extern private static Array AllocateVector(VTable vtable, int numElements);

        // Bartok and TAL set the real type: all A. (VTable<A,AllocObject>)->BlankObject<A>
        // Note: only used for initialization.  (Can't GC with interrupts disabled)
        [InterruptsDisabled]
        [RequiredByBartok]
        private static Object AllocateObjectInterruptsDisabled(VTable vtable) {
            CompilerIntrinsics.Cli(); // TODO: superfluous
            for(;;) {
                Object o = AllocateObject(vtable);
                if (o != null) {
                    return o;
                }
                throw null;
            }
        }

        // Bartok and TAL set the real type: all A. (VTable<A,AllocObject>)->BlankObject<A>
        [RequiredByBartok]
        private static Object AllocateObjectInterruptsEnabled(VTable vtable) {
            CompilerIntrinsics.Cli();
            for(;;) {
                Object o = AllocateObject(vtable);
                if (o != null) {
                    CompilerIntrinsics.Sti();
                    return o;
                }
                Kernel.Collect();
                CompilerIntrinsics.Cli(); // TODO: superfluous
            }
        }

        // Bartok and TAL set the real type: all A. (VTable<A,AllocVector>,int)->A
        // Note: only used for initialization.  (Can't GC with interrupts disabled)
        [InterruptsDisabled]
        [RequiredByBartok]
        private static Array AllocateVectorInterruptsDisabled(VTable vtable, int len) {
            CompilerIntrinsics.Cli(); // TODO: superfluous
            for(;;) {
                Array o = AllocateVector(vtable, len);
                if (o != null) {
                    return o;
                }
                throw null;
            }
        }

        // Bartok and TAL set the real type: all A. (VTable<A,AllocVector>,int)->A
        [RequiredByBartok]
        private static Array AllocateVectorInterruptsEnabled(VTable vtable, int len) {
            CompilerIntrinsics.Cli();
            for(;;) {
                Array o = AllocateVector(vtable, len);
                if (o != null) {
                    CompilerIntrinsics.Sti();
                    return o;
                }
                Kernel.Collect();
                CompilerIntrinsics.Cli(); // TODO: superfluous
            }
        }
    }

    class DebugStub
    {
        static uint offset;

        internal static void Init() {
            offset = 80;
        }

        internal static void Break() {
            throw null;
        }

        internal static void Print(char c) {
            CompilerIntrinsics.Cli();
            NucleusCalls.VgaTextWrite(offset, (uint)(0x1e00 | c));
            offset++;
            if (offset == 40 * 80) {
                offset = 80;
            }
            NucleusCalls.VgaTextWrite(offset, (uint)(0x3b00 | 33));
            CompilerIntrinsics.Sti();
        }

        internal static void Print(String s) {
            foreach (char c in s) {
                Print(c);
            }
        }

        internal static void Print(String s, object o) {
            Print(s + o);
        }

        internal static void WriteLine(String s) {
            Print(s);
        }

        internal static void WriteLine(String s, object o) {
            Print(s + o);
        }

        // To cope with old debugging spew:
        internal static object ArgList(object o1) {return o1;}
        internal static object ArgList(object o1, object o2) {return o1;}
        internal static object ArgList(object o1, object o2, object o3) {return o1;}
        internal static object ArgList(object o1, object o2, object o3, object o4) {return o1;}
        internal static object ArgList(object o1, object o2, object o3, object o4, object o5) {return o1;}
        internal static object ArgList(object o1, object o2, object o3, object o4, object o5, object o6) {return o1;}
        internal static object ArgList(object o1, object o2, object o3, object o4, object o5, object o6, object o7) {return o1;}
        internal static object ArgList(object o1, object o2, object o3, object o4, object o5, object o6, object o7, object o8) {return o1;}
        internal static object ArgList(object o1, object o2, object o3, object o4, object o5, object o6, object o7, object o8, object o9) {return o1;}

        [System.Diagnostics.Conditional("DEBUG")]
        public static void Assert(bool truth)
        {
            VTable.Assert(truth);
        }

        [System.Diagnostics.Conditional("DEBUG")]
        public static void Assert(bool truth, string statement)
        {
            VTable.Assert(truth, statement);
        }
    }

    public class TRef
    {
        System.Threading.MonitorLock thisLock = new System.Threading.MonitorLock();
        Object o;

        public TRef(Object o) {
            VTable.Assert(o != null);
            this.o = o;
        }

        public Object Acquire() {
            thisLock.Acquire();
            return o;
        }

        public void Release(Object v) {
            o = v;
            thisLock.Release();
        }
    }
}

namespace Microsoft.Bartok.Runtime
{
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    [RequiredByBartok]
    [AccessedByRuntime("ok")]
    struct PreHeader
    {
        [AccessedByRuntime("ok")]
        internal int muw;
    }

    [RequiredByBartok]
    [AccessedByRuntime("ok")]
    struct PostHeader
    {
        [RequiredByBartok]
        [AccessedByRuntime("ok")]
        internal VTable vtableObject;
    }
}

namespace Microsoft.Contracts
{
    [System.AttributeUsage(System.AttributeTargets.Constructor, AllowMultiple = false)]
    public sealed class NotDelayedAttribute : System.Attribute {
    }
}

namespace Microsoft.SingSharp {}

namespace Microsoft.Singularity
{
    using System;

    public class Tracing
    {

        public const byte Fatal   = 0xe; // system crashed.
        public const byte Error   = 0xc; // system will crash.
        public const byte Warning = 0xa; // cause for immediate concern.
        public const byte Notice  = 0x8; // might be cause for concern.
        public const byte Trace   = 0x6; // may be of use in crash.
        public const byte Audit   = 0x4; // impact on performance.
        public const byte Debug   = 0x2; // used only for debugging.

        public static void Log(byte severity, string msg)
        {
        }
    }

    public class Bytes
    {
        public readonly byte[] Array;
        public readonly int Start;
        public readonly int Length;

        public Bytes(byte[] Array): this(Array, 0, Array.Length) {}

        public Bytes(byte[] Array, int Start, int Length)
        {
            VTable.Assert(Length >= 0);
            VTable.Assert(Start >= 0);
            VTable.Assert(Start + Length < Array.Length);
            this.Array = Array;
            this.Start = Start;
            this.Length = Length;
        }

        public byte this[int index]
        {
            get
            {
                VTable.Assert((uint)index < (uint)Length);
                return Array[Start + index];
            }

            set
            {
                VTable.Assert((uint)index < (uint)Length);
                Array[Start + index] = value;
            }
        }
    }

    public class Bitter
    {
        public static Bytes
        FromByteArray(byte[] buffer)
        {
            Bytes retval = new Bytes(new byte[buffer.Length]);
            FromByteArray(retval, 0, buffer.Length, buffer, 0);
            return retval;
        }

        public static Bytes
        FromByteArray(byte[] buffer, int offset, int length)
        {
            Bytes retval = new Bytes(new byte[length]);
            FromByteArray(retval, 0, length, buffer, offset);
            return retval;
        }

        public static void FromByteArray(Bytes buffer,
                                                int offset, int length,
                                                byte[] array, int aoffset)

        {
            VTable.Assert(offset >= 0);
            VTable.Assert(length >= 0);
            VTable.Assert(offset + length <= buffer.Length);
            Buffer.MoveMemory(buffer.Array, array, buffer.Start + offset, aoffset, length);
        }

        public static void FromByteArray(byte[] buffer,
                                                int offset, int length,
                                                byte[] array, int aoffset)

        {
            Buffer.MoveMemory(buffer, array, offset, aoffset, length);
        }

/*
        public static void FromIoMemory(Bytes buffer, int offset,
                                               int length, Microsoft.Singularity.Io.IoMemory memory, int aoffset)
        {
            if (buffer == null || memory == null ||
                offset < 0 || offset + length > buffer.Length ||
                aoffset < 0 || aoffset + length > memory.Length) {

                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_Index");
            }

            memory.Read8(aoffset, buffer.Array, buffer.Start + offset, length);
        }

        public static void FromIoMemory(byte[] buffer, int offset,
                                               int length, Microsoft.Singularity.Io.IoMemory memory, int aoffset)
        {
            if (buffer == null || memory == null ||
                offset < 0 || offset + length > buffer.Length ||
                aoffset < 0 || aoffset + length > memory.Length) {

                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_Index");
            }

            memory.Read8(aoffset, buffer, offset, length);
        }
*/

        public static byte[] ToByteArray(byte[] buffer)
        {
            byte[] retval = new byte[buffer.Length];
            int length = buffer.Length;

            Buffer.MoveMemory(retval, buffer, 0, 0, length);
            return retval;
        }

        public static byte[] ToByteArray(Bytes buffer)
        {
            byte[] retval = new byte[buffer.Length];
            int length = buffer.Length;

            Buffer.MoveMemory(retval, buffer.Array, 0, buffer.Start, length);
            return retval;
        }

        public static void ToByteArray(byte[] buffer, int offset,
                                              int length, byte[] array, int aoffset)
        {
            Buffer.MoveMemory(array, buffer, aoffset, offset, length);
        }

        public static void ToByteArray(Bytes buffer, int offset,
                                              int length, byte[] array, int aoffset)
        {
            VTable.Assert(offset + length <= buffer.Length);
            Buffer.MoveMemory(array, buffer.Array, aoffset, buffer.Start + offset, length);
        }

        public static void Copy(Bytes dest, int destOffset, int length, Bytes source, int sourceOffset)
        {
            VTable.Assert(destOffset >= 0);
            VTable.Assert(sourceOffset >= 0);
            VTable.Assert(length >= 0);
            VTable.Assert(destOffset + length <= dest.Length);
            VTable.Assert(sourceOffset + length <= source.Length);
            Buffer.MoveMemory(dest.Array, source.Array, dest.Start + destOffset, source.Start + sourceOffset, length);
        }

        public static Bytes SplitOff(ref Bytes original, int offset)
        {
            Bytes b = original;
            original = new Bytes(b.Array, b.Start, offset);
            return new Bytes(b.Array, b.Start + offset, b.Length - offset);
        }
    }
}

namespace Microsoft.Singularity.Channels {}
namespace Microsoft.Singularity.Directory {}
namespace Microsoft.Singularity.V1.Services {}

namespace Microsoft.Singularity.Io
{
    public class PciMemory
    {
        uint id;
        int size;

        internal PciMemory(uint id)
        {
            this.id = id;
            try {
                CompilerIntrinsics.Cli();
                size = (int)NucleusCalls.PciMemSetup(id);
            }
            finally {
                CompilerIntrinsics.Sti();
            }
            System.DebugStub.Print("PCI size = 0x" + size.ToString("X") + ". ");
        }

        public uint Read32(int offset)
        {
            try {
                CompilerIntrinsics.Cli();
                return NucleusCalls.PciMemRead32(id, (uint)offset);
            }
            finally {
                CompilerIntrinsics.Sti();
            }
        }

        public void Write32(int offset, uint val)
        {
            try {
                CompilerIntrinsics.Cli();
                NucleusCalls.PciMemWrite32(id, (uint)offset, val);
            }
            finally {
                CompilerIntrinsics.Sti();
            }
        }
    }

    public class DmaMemory
    {
        private static uint ioPhysical; // physical address of ioMemory[0]
        private static byte[] ioMemory;
        private static int allocOffset; // offset from ioMemory[0]

        private int length;
        private int offset; // offset from ioMemory[0]

        public int Length { get { return length; } }

        internal static void Setup()
        {
            System.DebugStub.Print("Dma.Setup 1. ");
            try {
                CompilerIntrinsics.Cli();
                ioMemory = NucleusCalls.PciDmaBuffer();
                ioPhysical = NucleusCalls.PciDmaPhysicalAddr();
                // The IO-MMU tables map 2MB, aligned by 2MB
                uint superPageSize = 0x200000;
                uint ioSuperPage = (ioPhysical + 2 * superPageSize) - (ioPhysical & (superPageSize - 1));
                allocOffset = (int)(ioSuperPage - ioPhysical);
            }
            finally {
                CompilerIntrinsics.Sti();
            }
            System.DebugStub.Print("Dma.Setup 2. ioPhysical = 0x" + ioPhysical.ToString("X") + " allocOffset = 0x" + allocOffset.ToString("X") + ". ");
        }

        internal DmaMemory(int length)
        {
            System.VTable.Assert(length >= 0);
            try {
                CompilerIntrinsics.Cli();
                this.offset = allocOffset;
                this.length = length;
                if (allocOffset + length <= ioMemory.Length) {
                    allocOffset += length;
                }
            } finally {
                CompilerIntrinsics.Sti();
            }
            if (offset + length > ioMemory.Length) {
                throw new System.Exception("DmaMemory");
            }
        }

        internal void CheckBounds(int aoffset, int len)
        {
            if (aoffset < 0 || aoffset + len > length) {
                throw new System.Exception("DmaMemory: CheckBounds");
            }
        }

        public uint PhysicalAddress { get { return (uint)(ioPhysical + offset); } }

        public Bytes BytesRef()
        {
            return new Bytes(ioMemory, offset, length);
        }

        public Bytes BytesRef(int boffset, int len)
        {
            System.VTable.Assert(boffset >= 0);
            System.VTable.Assert(len >= 0);
            System.VTable.Assert(boffset + len <= length);
            return new Bytes(ioMemory, offset + boffset, len);
        }

        public void Read8(int aoffset, byte[] buffer, int boffset, int len)
        {
            CheckBounds(aoffset, len);
            System.Buffer.MoveMemory(buffer, ioMemory, boffset, offset + aoffset, len);
        }

        public uint Read32(int aoffset)
        {
            CheckBounds(aoffset, 4);
            return System.BitConverter.ToUInt32(ioMemory, offset + aoffset);
        }

        public ulong Read64(int aoffset)
        {
            CheckBounds(aoffset, 8);
            return System.BitConverter.ToUInt64(ioMemory, offset + aoffset);
        }

        public void Write8(int aoffset, byte[] buffer, int boffset, int len)
        {
            CheckBounds(aoffset, len);
            System.Buffer.MoveMemory(ioMemory, buffer, offset + aoffset, boffset, len);
        }

        public void Write32(int aoffset, uint value)
        {
            CheckBounds(aoffset, 4);
            System.BitConverter.GetBytes(value, ioMemory, offset + aoffset);
        }

        public void Write64(int aoffset, ulong value)
        {
            CheckBounds(aoffset, 8);
            System.BitConverter.GetBytes(value, ioMemory, offset + aoffset);
        }
    }

    public class IoMemoryRange
    {
    }

    public class IoIrqRange
    {
    }

    public class IoIrq
    {
    }

    public class PciDeviceConfig
    {
        public ushort       VendorId;               // 00..01 (ro)
        public ushort       DeviceId;               // 02..03 (ro)

/*
        protected byte      RevisionId;             // 08..08 (ro)
        public byte         Interface;              // 09..09 (ro)
        protected byte      SubClassId;             // 0a..0a (ro)
        protected byte      ClassId;                // 0b..0b (ro)
        public byte         CacheLineSize;          // 0c..0c (ro+)
        protected byte      LatencyTimer;           // 0d..0d (ro+)
        protected byte      HeaderType;             // 0e..0e (ro)
        protected byte      BIST;                   // 0f..0f Built in self test

        protected ulong[]   BaseAddresses;          // 10..17 or ..27 [2 or 6]
        protected ulong[]   BaseAddrSizes;

        protected ushort    SubsystemVendorId;      // 2c..2d (devices only)
        protected ushort    SubsystemDeviceId;      // 2e..2f (devices only)
*/
        public byte         Capabilities;               // 34..34
/*
        protected uint      ROMBaseAddress;         // 38..3b or 30.33
        protected byte      InterruptPin;           // 3d..3d
*/
        private readonly ushort id;

/*TODO
        public byte Read8(int offset) {
            return (byte)(Read32(offset));
        }

        public ushort Read16(int offset) {
            return (ushort)(Read32(offset));
        }
*/

        public uint Read32(int offset) {
            System.VTable.Assert((offset & 3) == 0);
            try {
                CompilerIntrinsics.Cli();
                return NucleusCalls.PciConfigRead32(id, (uint)offset);
            }
            finally {
                CompilerIntrinsics.Sti();
            }
        }

        internal PciDeviceConfig(ushort id) {
            uint word0 = Read32(0);
            VendorId = (ushort)(word0);
            DeviceId = (ushort)(word0 >> 16);
            uint word34 = Read32(0x34);
            Capabilities = (byte)(word34);
            System.DebugStub.Print("PCI word0 = " + word0.ToString("X") + ". ");
            System.DebugStub.Print("PCI word34 = " + word34.ToString("X") + ". ");
        }
    }

    public class PciConfig
    {
        //
        // Bit encodings for  PCI_COMMON_CONFIG.HeaderType
        //
        public const uint PCI_MULTIFUNCTION   = 0x800000; // full dword
        public const uint PCI_TYPE_MASK       = 0x7f0000; // full dword
        public const uint PCI_DEVICE_TYPE     = 0x000000; // full dword
        public const uint PCI_BRIDGE_TYPE     = 0x010000; // full dword
        public const uint PCI_CARDBUS_TYPE    = 0x020000; // full dword

        private const int PCI_CONTROL_OFFSET  = 0x0004;
        private const int PCI_STATUS_OFFSET   = 0x0006;

        //
        // Bit encodings for PCI_COMMON_CONFIG.Control
        //
        public const uint PCI_ENABLE_IO_SPACE               = 0x0001;
        public const uint PCI_ENABLE_MEMORY_SPACE           = 0x0002;
        public const uint PCI_ENABLE_BUS_MASTER             = 0x0004;
        public const uint PCI_ENABLE_SPECIAL_CYCLES         = 0x0008;
        public const uint PCI_ENABLE_WRITE_AND_INVALIDATE   = 0x0010;
        public const uint PCI_ENABLE_VGA_COMPATIBLE_PALETTE = 0x0020;
        public const uint PCI_ENABLE_PARITY                 = 0x0040; // (ro+)
        public const uint PCI_ENABLE_WAIT_CYCLE             = 0x0080; // (ro+)
        public const uint PCI_ENABLE_SERR                   = 0x0100; // (ro+)
        public const uint PCI_ENABLE_FAST_BACK_TO_BACK      = 0x0200; // (ro)
        public const uint PCI_DISABLE_INTERRUPTS            = 0x0400;

        //
        // Bit encodings for PCI_COMMON_CONFIG.Status
        //
        const uint PCI_STATUS_FAST_BACK_TO_BACK        = 0x0080;  // (ro)
        const uint PCI_STATUS_DATA_PARITY_DETECTED     = 0x0100;
        const uint PCI_STATUS_DEVSEL                   = 0x0600;  // 2 bits wide
        const uint PCI_STATUS_SIGNALED_TARGET_ABORT    = 0x0800;
        const uint PCI_STATUS_RECEIVED_TARGET_ABORT    = 0x1000;
        const uint PCI_STATUS_RECEIVED_MASTER_ABORT    = 0x2000;
        const uint PCI_STATUS_SIGNALED_SYSTEM_ERROR    = 0x4000;
        const uint PCI_STATUS_DETECTED_PARITY_ERROR    = 0x8000;

        // Bit encodes for PCI_COMMON_CONFIG.u.type0.BaseAddresses
        //
        const uint PCI_BAR_TYPE_MASK     = 0xf;
        const uint PCI_BAR_TYPE_IO       = 0x1;
        const uint PCI_BAR_TYPE_MEM20    = 0x2;
        const uint PCI_BAR_TYPE_MEM32    = 0x0;
        const uint PCI_BAR_TYPE_MEM64    = 0x4;
        const uint PCI_BAR_TYPE_MEMMASK  = 0x6;
        const uint PCI_BAR_TYPE_PREFETCH = 0x8;

        const uint PCI_ROMADDRESS_ENABLED              = 0x00000001;

        const uint PCI_ENABLE_BRIDGE_PARITY_ERROR        = 0x0001;
        const uint PCI_ENABLE_BRIDGE_SERR                = 0x0002;
        const uint PCI_ENABLE_BRIDGE_ISA                 = 0x0004;
        const uint PCI_ENABLE_BRIDGE_VGA                 = 0x0008;
        const uint PCI_ENABLE_BRIDGE_MASTER_ABORT_SERR   = 0x0020;
        const uint PCI_ASSERT_BRIDGE_RESET               = 0x0040;
        const uint PCI_ENABLE_BRIDGE_FAST_BACK_TO_BACK   = 0x0080;

        const byte PCI_CLASS_STORAGE            = 0x01;
        const byte PCI_CLASS_NETWORK            = 0x02;
        const byte PCI_CLASS_DISPLAY            = 0x03;
        const byte PCI_CLASS_MULTIMEDIA         = 0x04;
        const byte PCI_CLASS_MEMORY             = 0x05;
        const byte PCI_CLASS_BRIDGE             = 0x06;
        const byte PCI_CLASS_COMMUNICATION      = 0x07;
        const byte PCI_CLASS_SYSTEM             = 0x08;
        const byte PCI_CLASS_INPUT              = 0x09;
        const byte PCI_CLASS_DOCKING            = 0x0a;
        const byte PCI_CLASS_PROCESSOR          = 0x0b;
        const byte PCI_CLASS_SERIAL             = 0x0c;
        const byte PCI_CLASS_WIRELESS           = 0x0d;
        const byte PCI_CLASS_I2O                = 0x0e;
        const byte PCI_CLASS_SATELLITE          = 0x0f;
        const byte PCI_CLASS_ENCRYPTION         = 0x10;
        const byte PCI_CLASS_ACQUISITION        = 0x11;
        const byte PCI_CLASS_OTHERS             = 0xff;

        const byte PCI_CLASS_STORAGE_SCSI       = 0x00;
        const byte PCI_CLASS_STORAGE_IDE        = 0x01; // NB: Interface
        const byte PCI_CLASS_STORAGE_FLOPPY     = 0x02;
        const byte PCI_CLASS_STORAGE_IPI        = 0x03;
        const byte PCI_CLASS_STORAGE_RAID       = 0x04;
        const byte PCI_CLASS_STORAGE_ATA        = 0x05; // NB: Interface
        const byte PCI_CLASS_STORAGE_OTHER      = 0x80;

        const byte PCI_CLASS_NETWORK_ETHERNET   = 0x00;
        const byte PCI_CLASS_NETWORK_RING       = 0x01;
        const byte PCI_CLASS_NETWORK_FDDI       = 0x02;
        const byte PCI_CLASS_NETWORK_ATM        = 0x03;
        const byte PCI_CLASS_NETWORK_ISDN       = 0x04;
        const byte PCI_CLASS_NETWORK_FIP        = 0x05;
        const byte PCI_CLASS_NETWORK_PICMG      = 0x06; // NB: Interface
        const byte PCI_CLASS_NETWORK_OTHER      = 0x80;

        const byte PCI_CLASS_DISPLAY_VGA        = 0x00; // NB: Interface
        const byte PCI_CLASS_DISPLAY_XGA        = 0x01;
        const byte PCI_CLASS_DISPLAY_3D         = 0x02;
        const byte PCI_CLASS_DISPLAY_OTHER      = 0x80;

        const byte PCI_CLASS_MULTIMEDIA_VIDEO   = 0x00;
        const byte PCI_CLASS_MULTIMEDIA_AUDIO   = 0x01;
        const byte PCI_CLASS_MULTIMEDIA_TELEPHONY   = 0x02;
        const byte PCI_CLASS_MULTIMEDIA_OTHER   = 0x80;

        const byte PCI_CLASS_MEMORY_RAM         = 0x00;
        const byte PCI_CLASS_MEMORY_FLASH       = 0x01;
        const byte PCI_CLASS_MEMORY_OTHER       = 0x80;

        const byte PCI_CLASS_BRIDGE_HOST        = 0x00;
        const byte PCI_CLASS_BRIDGE_ISA         = 0x01;
        const byte PCI_CLASS_BRIDGE_EISA        = 0x02;
        const byte PCI_CLASS_BRIDGE_MC          = 0x03;
        const byte PCI_CLASS_BRIDGE_PCI         = 0x04; // NB: Interface
        const byte PCI_CLASS_BRIDGE_PCMCIA      = 0x05;
        const byte PCI_CLASS_BRIDGE_NUBUS       = 0x06;
        const byte PCI_CLASS_BRIDGE_CARDBUS     = 0x07;
        const byte PCI_CLASS_BRIDGE_RACEWAY     = 0x08; // NB: Interface
        const byte PCI_CLASS_BRIDGE_SEMIPCI     = 0x09; // NB: Interface
        const byte PCI_CLASS_BRIDGE_INFINIBAND  = 0x0a;
        const byte PCI_CLASS_BRIDGE_OTHER       = 0x80;

        const byte PCI_CLASS_COMMUNICATION_SERIAL       = 0x00; // NB: Interface
        const byte PCI_CLASS_COMMUNICATION_PARALLEL     = 0x01; // NB: Interface
        const byte PCI_CLASS_COMMUNICATION_MULTIPORT    = 0x02;
        const byte PCI_CLASS_COMMUNICATION_MODEM        = 0x03; // NB: Interface
        const byte PCI_CLASS_COMMUNICATION_GPIB         = 0x04;
        const byte PCI_CLASS_COMMUNICATION_SMARTCARD    = 0x05;
        const byte PCI_CLASS_COMMUNICATION_OTHER        = 0x80;

        const byte PCI_CLASS_SYSTEM_PIC         = 0x00; // NB: Interface
        const byte PCI_CLASS_SYSTEM_DMA         = 0x01; // NB: Interface
        const byte PCI_CLASS_SYSTEM_TIMER       = 0x02; // NB: Interface
        const byte PCI_CLASS_SYSTEM_RTC         = 0x03; // NB: Interface
        const byte PCI_CLASS_SYSTEM_PCIHP       = 0x04;
        const byte PCI_CLASS_SYSTEM_OTHER       = 0x80;

        const byte PCI_CLASS_INPUT_KEYBOARD     = 0x00;
        const byte PCI_CLASS_INPUT_PEN          = 0x01;
        const byte PCI_CLASS_INPUT_MOUSE        = 0x02;
        const byte PCI_CLASS_INPUT_SCANNER      = 0x03;
        const byte PCI_CLASS_INPUT_GAMEPORT     = 0x04; // NB: Interface
        const byte PCI_CLASS_INPUT_OTHER        = 0x80;

        const byte PCI_CLASS_SERIAL_FIREWIRE    = 0x00; // NB: Interface
        const byte PCI_CLASS_SERIAL_ACCESS      = 0x01;
        const byte PCI_CLASS_SERIAL_SSA         = 0x02;
        const byte PCI_CLASS_SERIAL_USB         = 0x03; // NB: Interface
        const byte PCI_CLASS_SERIAL_FIBRE       = 0x04;
        const byte PCI_CLASS_SERIAL_SMBUS       = 0x05;
        const byte PCI_CLASS_SERIAL_INFINIBAND  = 0x06;
        const byte PCI_CLASS_SERIAL_IPMI        = 0x07; // NB: Interface
        const byte PCI_CLASS_SERIAL_SERCOS      = 0x08;
        const byte PCI_CLASS_SERIAL_CANBUS      = 0x09;

        const byte PCI_CLASS_WIRELESS_IRDA      = 0x00;
        const byte PCI_CLASS_WIRELESS_IR        = 0x01;
        const byte PCI_CLASS_WIRELESS_RF        = 0x10;
        const byte PCI_CLASS_WIRELESS_BLUETOOTH = 0x11;
        const byte PCI_CLASS_WIRELESS_BROADBAND = 0x12;
        const byte PCI_CLASS_WIRELESS_OTHER     = 0x80;

        const byte PCI_CLASS_I2O_I2O            = 0x00; // NB: Interface

        const byte PCI_CLASS_SATELLITE_TV       = 0x01;
        const byte PCI_CLASS_SATELLITE_AUDIO    = 0x02;
        const byte PCI_CLASS_SATELLITE_VOICE    = 0x03;
        const byte PCI_CLASS_SATELLITE_DATA     = 0x04;

        const byte PCI_CLASS_ENCRYPTION_NETWORK = 0x00;
        const byte PCI_CLASS_ENCRYPTION_ENTERTAINMENT = 0x10;
        const byte PCI_CLASS_ENCRYPTION_OTHER   = 0x80;

        const byte PCI_CLASS_ACQUISITION_DPIO   = 0x00;
        const byte PCI_CLASS_ACQUISITION_PERF   = 0x01;
        const byte PCI_CLASS_ACQUISITION_COMM   = 0x10;
        const byte PCI_CLASS_ACQUISITION_MGMT   = 0x20;
        const byte PCI_CLASS_ACQUISITION_OTHER  = 0x80;

        const int PCI_INTERRUPT_LINE = 0x3c;

        const int PCI_INTERRUPT_PIN  = 0x3d;
        const byte PCI_INTERRUPT_PIN_A = 1;
        const byte PCI_INTERRUPT_PIN_B = 2;
        const byte PCI_INTERRUPT_PIN_C = 3;
        const byte PCI_INTERRUPT_PIN_D = 4;
    }
}

namespace System.Diagnostics
{
    //| <include path='docs/doc[@for="ConditionalAttribute"]/*' />
    [AttributeUsage(AttributeTargets.Method, AllowMultiple=true)]
    public sealed class ConditionalAttribute : Attribute
    {
        //| <include path='docs/doc[@for="ConditionalAttribute.ConditionalAttribute"]/*' />
        public ConditionalAttribute(String conditionString)
        {
            m_conditionString = conditionString;
        }

        //| <include path='docs/doc[@for="ConditionalAttribute.ConditionString"]/*' />
        public String ConditionString {
            get {
                return m_conditionString;
            }
        }

        private String m_conditionString;
    }

    public sealed class Debug
    {
        [Conditional("DEBUG")]
        public static void Assert(bool truth)
        {
            VTable.Assert(truth);
        }

        [Conditional("DEBUG")]
        public static void Assert(bool truth, string statement)
        {
            VTable.Assert(truth, statement);
        }
    }
}

// Placeholders for Bartok (real definitions provided by TAL checker)
namespace System.GCs
{
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    internal struct CompressedFrameDescriptor {}

    internal class StaticData
    {
        [RequiredByBartok]
        private static int sectionCount;
        [RequiredByBartok]
        private static UIntPtr dataSectionEnd; // unmanaged uint**[]
        [RequiredByBartok]
        private static UIntPtr dataSectionBase; // unmanaged uint**[]
        [RequiredByBartok]
        private static UIntPtr roDataSectionEnd; // unmanaged uint**[]
        [RequiredByBartok]
        private static UIntPtr roDataSectionBase; // unmanaged uint**[]
        [RequiredByBartok]
        private static UIntPtr staticDataPointerBitMap; // unmanaged uint*[]
    }

    internal class CallStack
    {
        [RequiredByBartok]
        private static int callSiteTableCount;
        [RequiredByBartok]
        private static UIntPtr codeBaseStartTable;
        [RequiredByBartok]
        private static UIntPtr returnAddressToCallSiteSetNumbers;
        [RequiredByBartok]
        private static UIntPtr callSiteSetCount;
        [RequiredByBartok]
        private static UIntPtr callSetSiteNumberToIndex;
        [RequiredByBartok]
        private static UIntPtr activationDescriptorTable;
    }
}

namespace System.Text
{
//    public class StringBuilder {}
}

namespace System.Reflection
{
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    [AttributeUsage(AttributeTargets.Class | AttributeTargets.Struct | AttributeTargets.Interface)]
    public sealed class DefaultMemberAttribute : Attribute
    {
        // The name of the member
        private String m_memberName;

        // You must provide the name of the member, this is required
        //| <include path='docs/doc[@for="DefaultMemberAttribute.DefaultMemberAttribute"]/*' />
        public DefaultMemberAttribute(String memberName) {m_memberName = memberName;}

        // A get accessor to return the name from the attribute.
        // NOTE: There is no setter because the name must be provided
        //  to the constructor.  The name is not optional.
        //| <include path='docs/doc[@for="DefaultMemberAttribute.MemberName"]/*' />
        public String MemberName {
            get {return m_memberName;}
        }
    }

    [RequiredByBartok]
    internal class Module
    {
    }
}

namespace System.Collections
{
/*
    [System.Runtime.InteropServices.Guid("496B0ABF-CDEE-11d3-88E8-00902754C43A")]
    public interface IEnumerator
    {
        bool MoveNext();
        Object Current { get; }
        void Reset();
    }

    public interface IEnumerable
    {
        IEnumerator GetEnumerator();
    }
*/
}


namespace System.Runtime.InteropServices
{
    public enum GCOption {
        NONE = 0,
        GCFRIEND = 1,
        NOGC = 2,
        NOSTGC = 3,
    }

    [AttributeUsage(AttributeTargets.Method, Inherited = false)]
    [System.Runtime.CompilerServices.RequiredByBartok]
    public sealed class GCAnnotationAttribute : Attribute {
        internal GCOption _options;
        public GCAnnotationAttribute(GCOption options ) {_options = options;}
    }
}

// Currently this is only used to handle array initialization in the MDIL code
// paths.

namespace System {

  using System.Runtime.CompilerServices;

  // These should only be used for RVA statics.  Furthermore, they should only
  // be used as the target of a RuntimeFieldHandle which is returned by ldtoken
  // and then passed to RuntimeHelpers.InitializeArrayImpl when the compiler is
  // not recognizing that sequence and constructing an actual array object with
  // the initializing data.  The compiler can not do that when targeting MDIL.

  [RequiredByBartok]
  internal struct RuntimeField {
      [RequiredByBartok]
      internal UIntPtr PointerToData; // only set for RVA statics
      [RequiredByBartok]
      internal uint Size;
  }
}

