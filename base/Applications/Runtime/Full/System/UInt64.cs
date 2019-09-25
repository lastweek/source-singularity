// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  UInt64
//
// Purpose: This class will encapsulate an unsigned long and
//          provide an Object representation of it.
//
//===========================================================  
namespace System
{
    using System.Globalization;
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    // Wrapper for unsigned 64 bit integers.
    //| <include path='docs/doc[@for="UInt64"]/*' />
    [CLSCompliant(false)]
    [System.Runtime.InteropServices.StructLayout(LayoutKind.Sequential)]
    public struct UInt64 : IComparable, IFormattable
    {
        private ulong m_value;

        //| <include path='docs/doc[@for="UInt64.MaxValue"]/*' />
        public const ulong MaxValue = (ulong) 0xffffffffffffffffL;
        //| <include path='docs/doc[@for="UInt64.MinValue"]/*' />
        public const ulong MinValue = 0x0;

        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type UInt64, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="UInt64.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }
            if (value is UInt64) {
                // Need to use compare because subtraction will wrap
                // to positive for very large neg numbers, etc.
                ulong i = (ulong)value;
                if (m_value < i) return -1;
                if (m_value > i) return 1;
                return 0;
            }
            throw new ArgumentException ("Arg_MustBeUInt64");
        }

        //| <include path='docs/doc[@for="UInt64.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is UInt64)) {
                return false;
            }
            return m_value == ((UInt64)obj).m_value;
        }

        // The value of the lower 32 bits XORed with the upper 32 bits.
        //| <include path='docs/doc[@for="UInt64.GetHashCode"]/*' />
        public override int GetHashCode() {
            return ((int)m_value) ^ (int)(m_value >> 32);
        }

        //| <include path='docs/doc[@for="UInt64.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }

        //| <include path='docs/doc[@for="UInt64.ToString2"]/*' />
        public String ToString(String format) {
            return Number.FormatUInt64(m_value, format);
        }

        //| <include path='docs/doc[@for="UInt64.Parse"]/*' />
        [CLSCompliant(false)]
        public static ulong Parse(String s) {
            return Parse(s, NumberStyles.Integer);
        }

        //| <include path='docs/doc[@for="UInt64.Parse2"]/*' />
        [CLSCompliant(false)]
        public static ulong Parse(String s, NumberStyles style) {
            NumberFormatInfo.ValidateParseStyle(style);
            return Number.ParseUInt64(s, style);
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="UInt64.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode()
        {
            return TypeCode.UInt64;
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
