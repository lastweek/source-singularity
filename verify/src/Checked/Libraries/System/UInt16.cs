// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  UInt16
//
// Purpose: This class will encapsulate a short and provide an
//          Object representation of it.
//
//===========================================================  
namespace System
{
    using System.Globalization;
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    // Wrapper for unsigned 16 bit integers.
    //| <include path='docs/doc[@for="UInt16"]/*' />
    [CLSCompliant(false)]
    [System.Runtime.InteropServices.StructLayout(LayoutKind.Sequential)]
    public struct UInt16 : IComparable, IFormattable
    {
        private ushort m_value;

        //| <include path='docs/doc[@for="UInt16.MaxValue"]/*' />
        public const ushort MaxValue = (ushort)0xFFFF;
        //| <include path='docs/doc[@for="UInt16.MinValue"]/*' />
        public const ushort MinValue = 0;


        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type UInt16, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="UInt16.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }
            if (value is UInt16) {
                return ((int)m_value - (int)(((UInt16)value).m_value));
            }
            throw new ArgumentException("Arg_MustBeUInt16");
        }

        //| <include path='docs/doc[@for="UInt16.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is UInt16)) {
                return false;
            }
            return m_value == ((UInt16)obj).m_value;
        }

        // Returns a HashCode for the UInt16
        //| <include path='docs/doc[@for="UInt16.GetHashCode"]/*' />
        public override int GetHashCode() {
            return (int)m_value;
        }

        // Converts the current value to a String in base-10 with no extra padding.
        //| <include path='docs/doc[@for="UInt16.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }

        //| <include path='docs/doc[@for="UInt16.ToString2"]/*' />
        public String ToString(String format) {
            return Number.FormatUInt32(m_value, format);
        }

        //| <include path='docs/doc[@for="UInt16.Parse"]/*' />
        [CLSCompliant(false)]
        public static ushort Parse(String s) {
            return Parse(s, NumberStyles.Integer);
        }

        //| <include path='docs/doc[@for="UInt16.Parse3"]/*' />
        [CLSCompliant(false)]
        public static ushort Parse(String s, NumberStyles style) {
            NumberFormatInfo.ValidateParseStyle(style);
            uint i = Number.ParseUInt32(s, style);
            if (i > MaxValue) throw new OverflowException("Overflow_UInt16");
            return (ushort)i;
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="UInt16.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode()
        {
            return TypeCode.UInt16;
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
