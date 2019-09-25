// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Int64.cool
//
// Purpose: This class will encapsulate a long and provide an
//          Object representation of it.
//
//===========================================================  
namespace System
{

    using System;
    using System.Globalization;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    //| <include path='docs/doc[@for="Int64"]/*' />
    [StructLayout(LayoutKind.Sequential)]
    public struct Int64 : IComparable, IFormattable
    {
        internal long m_value;

        //| <include path='docs/doc[@for="Int64.MaxValue"]/*' />
        public const long MaxValue = 0x7fffffffffffffffL;
        //| <include path='docs/doc[@for="Int64.MinValue"]/*' />
        public const long MinValue = unchecked((long)0x8000000000000000L);

        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type Int64, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="Int64.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }
            if (value is Int64) {
                // Need to use compare because subtraction will wrap
                // to positive for very large neg numbers, etc.
                long i = (long)value;
                if (m_value < i) return -1;
                if (m_value > i) return 1;
                return 0;
            }
            throw new ArgumentException ("Arg_MustBeInt64");
        }

        //| <include path='docs/doc[@for="Int64.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is Int64)) {
                return false;
            }
            return m_value == ((Int64)obj).m_value;
        }

        // The value of the lower 32 bits XORed with the upper 32 bits.
        //| <include path='docs/doc[@for="Int64.GetHashCode"]/*' />
        public override int GetHashCode() {
            return ((int)m_value ^ (int)(m_value >> 32));
        }

        //| <include path='docs/doc[@for="Int64.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }

        //| <include path='docs/doc[@for="Int64.ToString2"]/*' />
        public String ToString(String format) {
            return Number.FormatInt64(m_value, format);
        }

        //| <include path='docs/doc[@for="Int64.Parse"]/*' />
        public static long Parse(String s) {
            return Parse(s, NumberStyles.Integer);
        }

        // Parses a long from a String in the given style.  If
        // a NumberFormatInfo isn't specified, the current culture's
        // NumberFormatInfo is assumed.
        //
        //| <include path='docs/doc[@for="Int64.Parse3"]/*' />
        public static long Parse(String s, NumberStyles style) {
            NumberFormatInfo.ValidateParseStyle(style);
            return Number.ParseInt64(s, style);
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Int64.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode()
        {
            return TypeCode.Int64;
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
