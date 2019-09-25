// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

#if BOILER_PLATE
namespace Bartok.Marshal
{
    public class CheapState {
#endif // BOILER_PLATE
        private static CheapState latest;

        private const uint Limit = 16;

        public CheapState(int indent)
        {
            used = 0;
            read = 0;
            this.indent = indent;

            loadPtrs = new object[128 * 1024];

            regionSize = 8 * 1024 * 1024;
            region = VirtualAlloc(0, regionSize, MEM_COMMIT, PAGE_READWRITE);
            Console.WriteLine("Region = {0:x8}", region);

            latest = this;
        }

        public CheapState(CheapState other)
        {
            region = other.region;
            regionSize = other.regionSize;

            used = 0;
            read = 0;
            indent = 0;

            loadPtrs = new object[16 * 1024];

            latest = this;
        }

        [System.Runtime.InteropServices.DllImport("kernel32.dll", SetLastError=true)]
        private static extern uint VirtualAlloc(uint lpAddress,
                                                uint dwSize,
                                                uint flAllocationType,
                                                uint flProtect);
        private const uint MEM_COMMIT = 0x1000;
        private const uint PAGE_READWRITE = 0x04;

        private uint        region;
        private uint        regionSize;

        private uint        used;
        private uint        read;

        private ObjectIDGenerator   oig;

        private object[]    loadPtrs;
        private uint        loadCount;

        private uint        usedTrace;
        private uint        readTrace;
        private int         indent;

        public static System.Collections.Hashtable writeHash;
        public static System.Collections.Hashtable readHash;

        public void WriteOpen()
        {
            oig = new ObjectIDGenerator();
#if false
            unsafe {
                byte *ptr = (byte *)region;
                for (uint i = 0; i < used; i++) {
                    ptr[i] = 0xdd;
                }
            }
#endif

            used = 0;
            usedTrace = 0;
            indent = 0;

            WriteRaw(used);
            TraceWrite("Zero Buffer Size");
        }

        public void WriteClose()
        {
            unsafe {
                uint * p = (uint *)region;
                *p = used;
            }
            Trace(0, 4, "Wrote Buffer Size: {0}", used);
            used = 0;
            read = 0;
        }

        public void ReadOpen()
        {
            read = 0;
            readTrace = 0;
            indent = 0;

#if false
            for (uint i = 0; i < loadCount; i++) {
                loadPtrs[i] = null;
            }
#endif
            loadPtrs[0] = null;
            loadCount = 1;

            used = 4;    // set to 4 so our read don't fail.
            ReadRaw(out used);
            TraceRead("Read Buffer Size: {0}", used);
        }

        public void ReadClose()
        {
            if (used != read) {
                throw new ArgumentOutOfRangeException();
            }
            read = 0;
            used = 0;
        }

        [System.Diagnostics.Conditional("TRACE_CHEAP_STATE")]
        public void Trace(uint offset, uint size, string text)
        {
            if (offset > Limit) {
                return;
            }

#if !USE_DOT_INDENT
            Console.Write("{0,8:d}: {1}{2}", offset, new String('.', indent), text);
            if (indent + text.Length < 32) {
                Console.Write(new String(' ', 32 - (indent + text.Length)));
            }
#else
            Console.Write("{0,8:d}: {1,3} {2,-20} ", offset, indent, text);
#endif
            if (size > 0) {
                if (offset + size > regionSize) {
                    throw new ArgumentOutOfRangeException();
                }
                for (uint i = 0; i < size; i++) {
                    unsafe {
                        byte *p = (byte *)region + offset + i;
                        Console.Write("{0:x2}", *p);
                    }
                }
            }
            Console.WriteLine();
        }

        [System.Diagnostics.Conditional("TRACE_CHEAP_STATE")]
        public void Trace(uint offset, uint size, string text, params object[] args)
        {
            Trace(offset, size, String.Format(text, args));
        }

        [System.Diagnostics.Conditional("TRACE_CHEAP_STATE")]
        public void TraceRead(string text)
        {
            uint offset = readTrace;
            uint size = read - readTrace;
            readTrace = read;

            Trace(offset, size, text);
        }

        [System.Diagnostics.Conditional("TRACE_CHEAP_STATE")]
        public void TraceRead(string text, params object[] args)
        {
            TraceRead(String.Format(text, args));
        }

        [System.Diagnostics.Conditional("TRACE_CHEAP_STATE")]
        public void TraceWrite(string text)
        {
            uint offset = usedTrace;
            uint size = used - usedTrace;
            usedTrace = used;

            Trace(offset, size, text);
        }

        [System.Diagnostics.Conditional("TRACE_CHEAP_STATE")]
        public void TraceWrite(string text, params object[] args)
        {
            TraceWrite(String.Format(text, args));
        }

        [System.Diagnostics.Conditional("TRACE_CHEAP_STATE")]
        public void Trace(string text)
        {
            if (read == 0 && used > Limit) {
                return;
            }
            else if (read > Limit) {
                return;
            }

#if !USE_DOT_INDENT
            Console.WriteLine("        : {0}{1}", new String('.', indent), text);
#else
            Console.WriteLine("        : {0,3} {1}", indent, text);
#endif
        }

        [System.Diagnostics.Conditional("TRACE_CHEAP_STATE")]
        public void Trace(string text, params object[] args)
        {
            Trace(String.Format(text, args));
        }

        [System.Diagnostics.Conditional("TRACE_CHEAP_STATE")]
        public void Trace()
        {
            Console.WriteLine();
        }

        //////////////////////////////////////////////////////////////////////////////
        //
        public bool SavePtr(uint id, object ptr)
        {
            bool first;
            long oid = oig.GetId(ptr, out first);
            if (!first) {
                id |= 0x8000;
                WriteType(id);
                WriteRaw(unchecked((uint)oid));
                TraceWrite("** pointer {0} of 0x{1:x}", oid, id);;
                WriteTypeEnd(id);
                return false;   // already marshaled.
            }
            else {
                TraceWrite("** Save pointer: {0} of 0x{1:x}", oid, id);;
            }
            return true;        // needs to be marshaled.
        }

        // Remember the pointer as we unmarshal an object.
        public uint AddPtr(object ptr, uint id)
        {
            loadPtrs[loadCount] = ptr;
            Trace(read, 0, "** Load pointer: {0} of 0x{1:x}", loadCount, id);
            return loadCount++;
        }

        // Only a pointer was saved because the object was already unmarshaled.
        public object LoadPtr(uint id)
        {
            if ((id & 0x8000) == 0) {
                throw new Exception("Bad id for pointer: " + id);
            }
            uint pi;
            ReadRaw(out pi);
            TraceRead("** pointer {0} of 0x{1:x}", pi, id);
            ReadTypeEnd(id);

            if (pi == 0 || pi > loadCount) {
                throw new Exception("Unexpected object pi: " + pi);
            }
            return loadPtrs[pi];
        }

        public void WriteRaw(ulong u)
        {
            unsafe {
                if (used + sizeof(ulong) > regionSize) {
                    throw new ArgumentOutOfRangeException();
                }
                byte *p = (byte *)region + used;
                *((ulong *)p) = u;
                used += sizeof(ulong);
            }
        }

        public void WriteRaw(uint u)
        {
            unsafe {
                if (used + sizeof(uint) > regionSize) {
                    throw new ArgumentOutOfRangeException();
                }
                byte *p = (byte *)region + used;
                *((uint *)p) = u;
                used += sizeof(uint);
            }
        }

        public void WriteRaw(ushort u)
        {
            unsafe {
                if (used + sizeof(ushort) > regionSize) {
                    throw new ArgumentOutOfRangeException();
                }
                byte *p = (byte *)region + used;
                *((ushort *)p) = u;
                used += sizeof(ushort);
            }
        }

        public void WriteRaw(byte u)
        {
            unsafe {
                if (used + sizeof(byte) > regionSize) {
                    throw new ArgumentOutOfRangeException();
                }
                byte *p = (byte *)region + used;
                *((byte *)p) = u;
                used += sizeof(byte);
            }
        }

        public void ReadRaw(out ulong u)
        {
            unsafe {
                if (read + sizeof(ulong) > used) {
                    throw new ArgumentOutOfRangeException();
                }
                byte *p = (byte *)region + read;
                u = *((ulong *)p);
                read += sizeof(ulong);
            }
        }

        public void ReadRaw(out uint u)
        {
            unsafe {
                if (read + sizeof(uint) > used) {
                    throw new ArgumentOutOfRangeException();
                }
                byte *p = (byte *)region + read;
                u = *((uint *)p);
                read += sizeof(uint);
            }
        }

        public void ReadRaw(out ushort u)
        {
            unsafe {
                if (read + sizeof(ushort) > used) {
                    throw new ArgumentOutOfRangeException();
                }
                byte *p = (byte *)region + read;
                u = *((ushort *)p);
                read += sizeof(ushort);
            }
        }

        public void ReadRaw(out byte u)
        {
            unsafe {
                if (read + sizeof(byte) > used) {
                    throw new ArgumentOutOfRangeException();
                }
                byte *p = (byte *)region + read;
                u = *((byte *)p);
                read += sizeof(byte);
            }
        }

        //////////////////////////////////////////////////////////////////////////////
        //
        public void WriteType(uint type)
        {
            WriteRaw(type | 0xbbbb0000);
            TraceWrite("WriteType 0x{0:x}", type);
            if (type != 0) {
                indent++;
            }
        }

        public void WriteTypeEnd(uint type)
        {
            if (type == 0) {
                throw new Exception("Null type can be an end.");
            }
            indent--;
            WriteRaw(type | 0xeeee0000);
            TraceWrite("WriteTypeEnd 0x{0:x}", type);
        }

        public uint ReadType()
        {
            uint type;
            ReadRaw(out type);
            TraceRead("ReadType ~0x{0:x}", (type & 0xffff));
            if ((type & 0xffff0000) != 0xbbbb0000) {
                throw new Exception("Missing beg type");
            }
            type &= 0x0000ffff;

            if (type != 0) {
                indent++;
            }
            return type;
        }

        public uint ReadType(uint id)
        {
            uint type;
            ReadRaw(out type);
            TraceRead("ReadType 0x{0:x}", id);
            if ((type & 0xffff0000) != 0xbbbb0000) {
                throw new Exception("Missing beg type");
            }
            type &= 0x0000ffff;

            if (type != 0) {
                indent++;
            }
            if (type != id) {
                throw new Exception("Invalid beg type");
            }
            return type;
        }

        public uint ReadTypeOrNull(uint id)
        {
            uint type;
            ReadRaw(out type);
            TraceRead("ReadTypeOrNull 0x{0:x}", id);
            if ((type & 0xffff0000) != 0xbbbb0000) {
                throw new Exception("Missing beg type");
            }
            type &= 0x0000ffff;

            if (type == 0) {
                return 0;
            }
            else if (type == id || type == (id | 0x8000)) {
                indent++;
                return type;
            }
            else {
                throw new Exception("Invalid beg type");
            }
        }

        public void ReadTypeEnd(uint id)
        {
            uint type;
            indent--;
            ReadRaw(out type);
            TraceRead("ReadTypeEnd 0x{0:x}", id);
            if ((type & 0xffff0000) != 0xeeee0000) {
                throw new Exception("Missing end type");
            }
            type &= 0x0000ffff;

            if (id != 0 && type != id) {
                throw new Exception("Invalid end type");
            }
        }

        //////////////////////////////////////////////////////////////////////////////
        //
        public void Write(bool value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Bool);
#endif
            if (value) {
                WriteRaw(unchecked((byte)1));
                TraceWrite("true");
            }
            else {
                WriteRaw(unchecked((byte)0));
                TraceWrite("false");
            }
#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Bool);
#endif
        }

        public void Read(out bool value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Bool);
#endif
            byte t;
            ReadRaw(out t);
            TraceRead("bool");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Bool);
#endif
            value = (t != 0);
        }

        public void CheapRead(out bool value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Bool);
#endif
            byte t;
            ReadRaw(out t);
            TraceRead("bool");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Bool);
#endif
            value = (t != 0);
        }

        public void Write(sbyte value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Sbyte);
#endif
            WriteRaw(unchecked((byte)value));
            TraceWrite("sbyte");
#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Sbyte);
#endif
        }

        public void Read(out sbyte value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Sbyte);
#endif
            byte t;
            ReadRaw(out t);
            TraceRead("sbyte");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Sbyte);
#endif
            value = unchecked((sbyte)t);
        }

        public void Write(byte value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Byte);
#endif
            WriteRaw(value);
            TraceWrite("byte");
#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Byte);
#endif
        }

        public void Read(out byte value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Byte);
#endif
            ReadRaw(out value);
            TraceRead("byte");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Byte);
#endif
        }

        public void Write(short value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Short);
#endif
            WriteRaw(unchecked((ushort)value));
            TraceWrite("short");
#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Short);
#endif
        }

        public void Read(out short value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Short);
#endif
            ushort t;
            ReadRaw(out t);
            TraceRead("short");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Short);
#endif
            value = unchecked((short)t);
        }

        public void Write(char value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Char);
#endif
            WriteRaw(unchecked((ushort)value));
            TraceWrite("char");
#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Char);
#endif
        }

        public void Read(out char value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Char);
#endif
            ushort t;
            ReadRaw(out t);
            TraceRead("char");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Char);
#endif
            value = unchecked((char)t);
        }

        public void Write(ushort value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Ushort);
#endif
            WriteRaw(value);
            TraceWrite("ushort");
#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Ushort);
#endif
        }

        public void Read(out ushort value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Ushort);
#endif
            ReadRaw(out value);
            TraceRead("ushort");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Ushort);
#endif
        }

        public void Write(int value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Int);
#endif
            WriteRaw(unchecked((uint)value));
            TraceWrite("int");
#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Int);
#endif
        }

        public void Read(out int value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Int);
#endif
            uint t;
            ReadRaw(out t);
            TraceRead("int");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Int);
#endif
            value = unchecked((int)t);
        }

        public void Write(uint value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Uint);
#endif
            WriteRaw(value);
            TraceWrite("uint");
#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Uint);
#endif
        }

        public void Read(out uint value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Uint);
#endif
            ReadRaw(out value);
            TraceRead("uint");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Uint);
#endif
        }

        public void Write(long value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Long);
#endif
            WriteRaw(unchecked((ulong)value));
            TraceWrite("long");

#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Long);
#endif
        }

        public void Read(out long value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Long);
#endif
            ulong t;
            ReadRaw(out t);
            TraceRead("long");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Long);
#endif
            value = unchecked((long)t);
        }

        public void Write(ulong value)
        {
#if USE_TYPE_IDS_ON_VALUES
            WriteType((uint)Types.Ulong);
#endif
            WriteRaw(value);
            TraceWrite("ulong");
#if USE_TYPE_IDS_ON_VALUES
            WriteTypeEnd((uint)Types.Ulong);
#endif
        }

        public void Read(out ulong value)
        {
#if USE_TYPE_IDS_ON_VALUES
            ReadType((uint)Types.Ulong);
#endif
            ReadRaw(out value);
            TraceRead("ulong");
#if USE_TYPE_IDS_ON_VALUES
            ReadTypeEnd((uint)Types.Ulong);
#endif
        }

        public void Write(string value)
        {
            if (value == null) {
                WriteType(0);
            }
            else if (SavePtr((uint)Types.String, value)) {
                int len = value.Length;
                WriteType((uint)Types.String);
                WriteRaw(unchecked((uint)len));
                for (int i = 0; i < len; i++) {
                    WriteRaw(unchecked((ushort)value[i]));
                }
                TraceWrite("string");
                WriteTypeEnd((uint)Types.String);
            }
        }

        public void Read(out string value)
        {
            uint id = ReadTypeOrNull((uint)Types.String);
            if ((id & 0x8000) != 0) {
                value = (string)LoadPtr(id);
            }
            else if (id != 0) {
                uint len;
                ReadRaw(out len);
                char[] ta = new char [len];
                for (uint i = 0; i < len; i++) {
                    ushort t;
                    ReadRaw(out t);
                    ta[i] = unchecked((char)t);
                }
                TraceRead("string");
                ReadTypeEnd((uint)Types.String);
                value = new String(ta);
                AddPtr(value, (uint)Types.String);
            }
            else {
                value = null;
            }
        }

        public void Write(object[] value) {
            Trace("Write object[]");
            if (value == null) {
                WriteType(0);
            }
            else if (SavePtr((uint)Types.ObjectArray, value)) {
                WriteType((uint)Types.ObjectArray);
                WriteRaw((uint)value.Length);
                TraceWrite("[].Length");
                for (int i = 0; i < value.Length; i++) {
                    if (value[i] == null) {
                        WriteType(0);
                    }
                    else {
                        Write(value[i]);
                    }
                }
                WriteTypeEnd((uint)Types.ObjectArray);
            }
        }

        public void Read(out object[] value) {
            Trace("Read object[] [outer]");
            uint id = ReadTypeOrNull((uint)Types.ObjectArray);
            if ((id & 0x8000) != 0) {
                value = (object[])LoadPtr(id);
            }
            else if (id != 0) {
                uint len;
                ReadRaw(out len);
                TraceRead("[].Length");
                value = new object [len];
                AddPtr(value, (uint)Types.ObjectArray);
                for (int i = 0; i < len; i++) {
                    Read(out value[i]);
                }
                ReadTypeEnd((uint)Types.ObjectArray);
            }
            else {
                value = null;
            }
        }

        public void Write(int[] value) {
            Trace("Write int[]");
            if (value == null) {
                WriteType(0);
            }
            else if (SavePtr((uint)Types.IntArray, value)) {
                WriteType((uint)Types.IntArray);
                WriteRaw((uint)value.Length);
                for (int i = 0; i < value.Length; i++) {
                    WriteRaw(unchecked((uint)value[i]));
                }
                TraceWrite("[]");
                WriteTypeEnd((uint)Types.IntArray);
            }
        }

        public void Read(out int[] value) {
            Trace("Read int[] [outer]");
            uint id = ReadTypeOrNull((uint)Types.IntArray);
            if ((id & 0x8000) != 0) {
                value = (int[])LoadPtr(id);
            }
            else if (id != 0) {
                uint len;
                ReadRaw(out len);
                value = new int [len];
                AddPtr(value, (uint)Types.IntArray);
                for (int i = 0; i < len; i++) {
                    uint v;
                    ReadRaw(out v);
                    value[i] = unchecked((int)v);
                }
                TraceRead("[]");
                ReadTypeEnd((uint)Types.IntArray);
            }
            else {
                value = null;
            }
        }

        public void Write(uint[] value) {
            Trace("Write uint[]");
            if (value == null) {
                WriteType(0);
            }
            else if (SavePtr((uint)Types.UintArray, value)) {
                WriteType((uint)Types.UintArray);
                WriteRaw((uint)value.Length);
                for (int i = 0; i < value.Length; i++) {
                    WriteRaw(value[i]);
                }
                TraceWrite("[]");
                WriteTypeEnd((uint)Types.UintArray);
            }
        }

        public void Read(out uint[] value) {
            Trace("Read uint[] [outer]");
            uint id = ReadTypeOrNull((uint)Types.UintArray);
            if ((id & 0x8000) != 0) {
                value = (uint[])LoadPtr(id);
            }
            else if (id != 0) {
                uint len;
                ReadRaw(out len);
                value = new uint [len];
                AddPtr(value, (uint)Types.UintArray);
                for (int i = 0; i < len; i++) {
                    ReadRaw(out value[i]);
                }
                TraceRead("[]");
                ReadTypeEnd((uint)Types.UintArray);
            }
            else {
                value = null;
            }
        }

        public void Write(object value)
        {
            Trace("Write object");
            if (value == null) {
                WriteType(0);
            }
            else {
                CheapWriteDelegate wd = writeHash[value.GetType()] as CheapWriteDelegate;
                if (wd != null) {
                    wd(this, value);
                }
                else {
                    throw new Exception("Unknown type " + value.GetType());
                }
            }
        }

        public void Read(out object value)
        {
            Trace("Read object");
            uint __id = ReadType();
            if (__id == 0) {
                value = null;
                return;
            }
            if ((__id & 0x8000) != 0) {
                value = LoadPtr(__id);
                return;
            }

            CheapReadDelegate rd = readHash[(uint)(__id & 0x7fff)] as CheapReadDelegate;
            if (rd != null) {
                value = rd(__id, this);
                return;
            }
            throw new Exception("Unknown type id " + __id);
        }
#if BOILER_PLATE
    } // class
} // namespace
#endif // BOILER_PLATE
