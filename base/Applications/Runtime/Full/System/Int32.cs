// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Int32
//
// Purpose: A representation of a 32 bit 2's complement
//          integer.
//
//===========================================================  
namespace System
{

    using System;
    using System.Globalization;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    //| <include path='docs/doc[@for="Int32"]/*' />
    [StructLayout(LayoutKind.Sequential)]
    public struct Int32 : IComparable, IFormattable
    {
        internal int m_value;

        //| <include path='docs/doc[@for="Int32.MaxValue"]/*' />
        public const int MaxValue = 0x7fffffff;
        //| <include path='docs/doc[@for="Int32.MinValue"]/*' />
        public const int MinValue = unchecked((int)0x80000000);

        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this < object, equal to zero
        // if this == object, and greater than one if this > object.
        // null is considered to be less than any instance.
        // If object is not of type Int32, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="Int32.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }
            if (value is Int32) {
                // Need to use compare because subtraction will wrap
                // to positive for very large neg numbers, etc.
                int i = (int)value;
                if (m_value < i) return -1;
                if (m_value > i) return 1;
                return 0;
            }
            throw new ArgumentException ("Arg_MustBeInt32");
        }

        //| <include path='docs/doc[@for="Int32.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is Int32)) {
                return false;
            }
            return m_value == ((Int32)obj).m_value;
        }

        // The absolute value of the int contained.
        //| <include path='docs/doc[@for="Int32.GetHashCode"]/*' />
        public override int GetHashCode() {
            return m_value;
        }


        //| <include path='docs/doc[@for="Int32.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }

        //| <include path='docs/doc[@for="Int32.ToString2"]/*' />
        public String ToString(String format) {
            return Number.FormatInt32(m_value, format);
        }

        //| <include path='docs/doc[@for="Int32.Parse"]/*' />
        public static int Parse(String s) {
            return Number.ParseInt32(s, NumberStyles.Integer);
        }

        // Parses an integer from a String in the given style.  If
        // a NumberFormatInfo isn't specified, the current culture's
        // NumberFormatInfo is assumed.
        //
        //| <include path='docs/doc[@for="Int32.Parse3"]/*' />
        public static int Parse(String s, NumberStyles style) {
            NumberFormatInfo.ValidateParseStyle(style);
            return Number.ParseInt32(s, style);
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Int32.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode()
        {
            return TypeCode.Int32;
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
