// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  SByte
//
// Purpose:
//
//===========================================================  
namespace System
{
    using System.Globalization;
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    // A place holder class for signed bytes.
    //| <include path='docs/doc[@for="SByte"]/*' />
    [CLSCompliant(false)]
    [System.Runtime.InteropServices.StructLayout(LayoutKind.Sequential)]
    public struct SByte : IComparable, IFormattable
    {
        private sbyte m_value;

        // The maximum value that a Byte may represent: 127.
        //| <include path='docs/doc[@for="SByte.MaxValue"]/*' />
        public const sbyte MaxValue = (sbyte)0x7F;

        // The minimum value that a Byte may represent: -128.
        //| <include path='docs/doc[@for="SByte.MinValue"]/*' />
        public const sbyte MinValue = unchecked((sbyte)0x80);


        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type SByte, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="SByte.CompareTo"]/*' />
        public int CompareTo(Object obj) {
            if (obj == null) {
                return 1;
            }
            if (!(obj is SByte)) {
                throw new ArgumentException ("Arg_MustBeSByte");
            }
            return m_value - ((SByte)obj).m_value;
        }

        // Determines whether two Byte objects are equal.
        //| <include path='docs/doc[@for="SByte.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is SByte)) {
                return false;
            }
            return m_value == ((SByte)obj).m_value;
        }


        // Gets a hash code for this instance.
        //| <include path='docs/doc[@for="SByte.GetHashCode"]/*' />
        public override int GetHashCode() {
            return ((int)m_value ^ (int)m_value << 8);
        }


        // Provides a string representation of a byte.
        //| <include path='docs/doc[@for="SByte.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }

        //| <include path='docs/doc[@for="SByte.ToString1"]/*' />
        public String ToString(String format) {
            if (m_value < 0 && format != null && format.Length > 0 && (format[0] =='X' || format[0] =='x')) {
                uint temp = (uint)(m_value & 0x000000FF);
                return Number.FormatUInt32(temp,format);
            }
            return Number.FormatInt32(m_value, format);
        }

        //| <include path='docs/doc[@for="SByte.Parse"]/*' />
        [CLSCompliant(false)]
        public static sbyte Parse(String s) {
            return Parse(s, NumberStyles.Integer);
        }

        // Parses a signed byte from a String in the given style.  If
        // a NumberFormatInfo isn't specified, the current culture's
        // NumberFormatInfo is assumed.
        //
        //| <include path='docs/doc[@for="SByte.Parse3"]/*' />
        [CLSCompliant(false)]
        public static sbyte Parse(String s, NumberStyles style) {
            NumberFormatInfo.ValidateParseStyle(style);
            int i = Number.ParseInt32(s, style);

            if (((style & NumberStyles.AllowHexSpecifier) != 0) && (i <= Byte.MaxValue)) // We are parsing a hexadecimal number
                    return (sbyte)i;

            if (i < MinValue || i > MaxValue) throw new OverflowException("Overflow_SByte");
            return (sbyte)i;
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="SByte.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode()
        {
            return TypeCode.SByte;
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
