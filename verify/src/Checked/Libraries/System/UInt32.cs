// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  UInt32
//
// Purpose: This class will encapsulate an uint and
//          provide an Object representation of it.
//
//===========================================================  
namespace System
{
    using System.Globalization;
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    // * Wrapper for unsigned 32 bit integers.
    //| <include path='docs/doc[@for="UInt32"]/*' />
    [CLSCompliant(false)]
    [System.Runtime.InteropServices.StructLayout(LayoutKind.Sequential)]
    public struct UInt32 : IComparable, IFormattable
    {
        private uint m_value;

        //| <include path='docs/doc[@for="UInt32.MaxValue"]/*' />
        public const uint MaxValue = (uint)0xffffffff;
        //| <include path='docs/doc[@for="UInt32.MinValue"]/*' />
        public const uint MinValue = 0U;


        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type UInt32, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="UInt32.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }
            if (value is UInt32) {
                // Need to use compare because subtraction will wrap
                // to positive for very large neg numbers, etc.
                uint i = (uint)value;
                if (m_value < i) return -1;
                if (m_value > i) return 1;
                return 0;
            }
            throw new ArgumentException("Arg_MustBeUInt32");
        }

        //| <include path='docs/doc[@for="UInt32.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is UInt32)) {
                return false;
            }
            return m_value == ((UInt32)obj).m_value;
        }

        // The absolute value of the int contained.
        //| <include path='docs/doc[@for="UInt32.GetHashCode"]/*' />
        public override int GetHashCode() {
            return ((int) m_value);
        }

        // The base 10 representation of the number with no extra padding.
        //| <include path='docs/doc[@for="UInt32.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }

        //| <include path='docs/doc[@for="UInt32.ToString2"]/*' />
        public String ToString(String format) {
            return Number.FormatUInt32(m_value, format);
        }

        //| <include path='docs/doc[@for="UInt32.Parse"]/*' />
        [CLSCompliant(false)]
        public static uint Parse(String s) {
            return Parse(s, NumberStyles.Integer);
        }

        //| <include path='docs/doc[@for="UInt32.Parse3"]/*' />
        [CLSCompliant(false)]
        public static uint Parse(String s, NumberStyles style) {
            NumberFormatInfo.ValidateParseStyle(style);
            return Number.ParseUInt32(s, style);
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="UInt32.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode()
        {
            return TypeCode.UInt32;
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
