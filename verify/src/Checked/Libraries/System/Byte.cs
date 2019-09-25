// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Byte
//
// Purpose: This class will encapsulate a byte and provide an
//          Object representation of it.
//
//===========================================================  

namespace System
{

    using System;
    using System.Globalization;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    // The Byte class extends the Value class and
    // provides object representation of the byte primitive type.
    //
    //| <include path='docs/doc[@for="Byte"]/*' />
    [StructLayout(LayoutKind.Sequential)]
    public struct Byte : IComparable, IFormattable
    {
        private byte m_value;

        // The maximum value that a Byte may represent: 255.
        //| <include path='docs/doc[@for="Byte.MaxValue"]/*' />
        public const byte MaxValue = (byte)0xFF;

        // The minimum value that a Byte may represent: 0.
        //| <include path='docs/doc[@for="Byte.MinValue"]/*' />
        public const byte MinValue = 0;


        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type byte, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="Byte.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }
            if (!(value is Byte)) {
                throw new ArgumentException("Arg_MustBeByte");
            }

            return m_value - (((Byte)value).m_value);
        }

        // Determines whether two Byte objects are equal.
        //| <include path='docs/doc[@for="Byte.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is Byte)) {
                return false;
            }
            return m_value == ((Byte)obj).m_value;
        }

        // Gets a hash code for this instance.
        //| <include path='docs/doc[@for="Byte.GetHashCode"]/*' />
        public override int GetHashCode() {
            return m_value;
        }

        //| <include path='docs/doc[@for="Byte.Parse"]/*' />
        public static byte Parse(String s) {
            return Parse(s, NumberStyles.Integer);
        }

        // Parses an unsigned byte from a String in the given style.  If
        // a NumberFormatInfo isn't specified, the current culture's
        // NumberFormatInfo is assumed.
        //| <include path='docs/doc[@for="Byte.Parse3"]/*' />
        public static byte Parse(String s, NumberStyles style) {
            NumberFormatInfo.ValidateParseStyle(style);
            int i = Number.ParseInt32(s, style);
            if (i < MinValue || i > MaxValue) throw new OverflowException("Overflow_Byte");
            return (byte)i;
        }

        //| <include path='docs/doc[@for="Byte.ToString"]/*' />
        public override String ToString() {
            return Number.FormatInt32(m_value, null);
        }

        //| <include path='docs/doc[@for="Byte.ToString1"]/*' />
        public String ToString(String format) {
            return Number.FormatInt32(m_value, format);
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Byte.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode() {
            return TypeCode.Byte;
        }

        //
        // This is just designed to prevent compiler warnings.
        // This field is used from native, but we need to prevent the compiler warnings.
        //
#if _DEBUG
        private void DontTouchThis() {
            m_value = m_value;
        }
#endif
    }
}
