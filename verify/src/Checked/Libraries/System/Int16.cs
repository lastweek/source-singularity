// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Int16.cool
//
// Purpose: This class will encapsulate a short and provide an
//          Object representation of it.
//
//===========================================================  

namespace System
{

    using System;
    using System.Globalization;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    //| <include path='docs/doc[@for="Int16"]/*' />
    [StructLayout(LayoutKind.Sequential)]
    public struct Int16 : IComparable, IFormattable
    {
        internal short m_value;

        //| <include path='docs/doc[@for="Int16.MaxValue"]/*' />
        public const short MaxValue = (short)0x7FFF;
        //| <include path='docs/doc[@for="Int16.MinValue"]/*' />
        public const short MinValue = unchecked((short)0x8000);

        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type Int16, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="Int16.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }

            if (value is Int16) {
                return m_value - ((Int16)value).m_value;
            }

            throw new ArgumentException("Arg_MustBeInt16");
        }

        //| <include path='docs/doc[@for="Int16.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is Int16)) {
                return false;
            }
            return m_value == ((Int16)obj).m_value;
        }

        // Returns a HashCode for the Int16
        //| <include path='docs/doc[@for="Int16.GetHashCode"]/*' />
        public override int GetHashCode() {
            return ((int)((ushort)m_value) | (((int)m_value) << 16));
        }


        //| <include path='docs/doc[@for="Int16.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }

        //| <include path='docs/doc[@for="Int16.ToString2"]/*' />
        public String ToString(String format) {
            if (m_value < 0 && format != null && format.Length > 0 && (format[0] =='X' || format[0] =='x')) {
                uint temp = (uint)(m_value & 0x0000FFFF);
                return Number.FormatUInt32(temp,format);
            }
            return Number.FormatInt32(m_value, format);
        }

        //| <include path='docs/doc[@for="Int16.Parse"]/*' />
        public static short Parse(String s) {
            return Parse(s, NumberStyles.Integer);
        }

        //| <include path='docs/doc[@for="Int16.Parse3"]/*' />
        public static short Parse(String s, NumberStyles style) {
            NumberFormatInfo.ValidateParseStyle(style);

            int i = Number.ParseInt32(s, style);

            // We need this check here since we don't allow signs to specified in hex numbers. So we fixup the result
            // for negative numbers
            if (((style & NumberStyles.AllowHexSpecifier) != 0) && (i <= UInt16.MaxValue)) // We are parsing a hexadecimal number
                return (short)i;

            if (i < MinValue || i > MaxValue) throw new OverflowException("Overflow_Int16");
            return (short)i;
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Int16.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode() {
            return TypeCode.Int16;
        }

        //
        // This is just designed to prevent compiler warnings.
        // This field is used from native, but we need to prevent the compiler warnings.
        //
#if _DEBUG
        private void DontTouchThis() {
            m_value = 0;
        }
#endif
    }
}
