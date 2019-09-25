// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Single
//
// Purpose: A wrapper class for the primitive type float.
//
//===========================================================  
namespace System
{

    using System.Globalization;
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="Single"]/*' />
    [System.Runtime.InteropServices.StructLayout(LayoutKind.Sequential)]
    public struct Single : IComparable, IFormattable
    {
        internal float m_value;

        //
        // Public constants
        //
        //| <include path='docs/doc[@for="Single.MinValue"]/*' />
        public const float MinValue = (float)-3.40282346638528859e+38;
        //| <include path='docs/doc[@for="Single.Epsilon"]/*' />
        public const float Epsilon = (float)1.4e-45;
        //| <include path='docs/doc[@for="Single.MaxValue"]/*' />
        public const float MaxValue = (float)3.40282346638528859e+38;
        //| <include path='docs/doc[@for="Single.PositiveInfinity"]/*' />
        public const float PositiveInfinity = (float)1.0 / (float)0.0;
        //| <include path='docs/doc[@for="Single.NegativeInfinity"]/*' />
        public const float NegativeInfinity = (float)-1.0 / (float)0.0;
        //| <include path='docs/doc[@for="Single.NaN"]/*' />
        public const float NaN = (float)0.0 / (float)0.0;

        //
        // Private constants
        //
        private const ulong PositiveInfinityAsUInt32 = 0x7f800000;
        private const ulong NegativeInfinityAsUInt32 = 0xff800000;

        private const ulong ExponentAsUInt32 = 0xff80000;
        private const ulong MantissaAsUInt32 = 0x007ffff;

        //
        // Native Declarations
        //
        //| <include path='docs/doc[@for="Single.IsInfinity"]/*' />
        public static bool IsInfinity(float f) {
            uint v = BitConverter.SingleToUInt32Bits(f);
            return (v == PositiveInfinityAsUInt32 ||
                    v == NegativeInfinityAsUInt32);
        }

        //| <include path='docs/doc[@for="Single.IsPositiveInfinity"]/*' />
        public static bool IsPositiveInfinity(float f) {
            uint v = BitConverter.SingleToUInt32Bits(f);
            return (v == PositiveInfinityAsUInt32);
        }

        //| <include path='docs/doc[@for="Single.IsNegativeInfinity"]/*' />
        public static bool IsNegativeInfinity(float f) {
            uint v = BitConverter.SingleToUInt32Bits(f);
            return (v == NegativeInfinityAsUInt32);
        }

        //| <include path='docs/doc[@for="Single.IsNa
        public static bool IsNaN(float f) {
            // See also Lightning\Src\ClassLibNative\Float\COMFloat::IsNAN
            uint v = BitConverter.SingleToUInt32Bits(f);
            return (((v & PositiveInfinityAsUInt32) == v) &&
                    ((v & MantissaAsUInt32) != 0));
        }

        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type Single, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="Single.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }
            if (value is Single) {
                float f = (float)value;
                if (m_value < f) return -1;
                if (m_value > f) return 1;
                if (m_value == f) return 0;

                // At least one of the values is NaN.
                if (IsNaN(m_value))
                    return (IsNaN(f) ? 0 : -1);
                else // f is NaN.
                    return 1;
            }
            throw new ArgumentException ("Arg_MustBeSingle");
        }

        //| <include path='docs/doc[@for="Single.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is Single)) {
                return false;
            }
            float temp = ((Single)obj).m_value;
            if (temp == m_value) {
                return true;
            }

            return IsNaN(temp) && IsNaN(m_value);
        }

        //| <include path='docs/doc[@for="Single.GetHashCode"]/*' />
        public override int GetHashCode() {
            return unchecked((int)BitConverter.SingleToUInt32Bits(m_value));
        }

        //| <include path='docs/doc[@for="Single.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }

        //| <include path='docs/doc[@for="Single.ToString1"]/*' />
        public String ToString(String format) {
            return Number.FormatSingle(m_value, format);
        }

        //| <include path='docs/doc[@for="Single.Parse"]/*' />
        public static float Parse(String s) {
            return Parse(s, NumberStyles.Float | NumberStyles.AllowThousands);
        }

        // Parses a float from a String in the given style.  If
        // a NumberFormatInfo isn't specified, the current culture's
        // NumberFormatInfo is assumed.
        //
        // This method will not throw an OverflowException, but will return
        // PositiveInfinity or NegativeInfinity for a number that is too
        // large or too small.
        //
        //| <include path='docs/doc[@for="Single.Parse3"]/*' />
        public static float Parse(String s, NumberStyles style) {
            try {
                return Number.ParseSingle(s, style);
            }
            catch (FormatException) {
                //If we caught a FormatException, it may be from one of our special strings.
                //Check the three with which we're concerned and rethrow if it's not one of
                //those strings.
                String sTrim = s.Trim();
                if (sTrim.Equals(NumberFormatInfo.positiveInfinitySymbol)) {
                    return PositiveInfinity;
                }
                if (sTrim.Equals(NumberFormatInfo.negativeInfinitySymbol)) {
                    return NegativeInfinity;
                }
                if (sTrim.Equals(NumberFormatInfo.nanSymbol)) {
                    return NaN;
                }
                //Rethrow the previous exception;
                throw;
            }
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Single.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode()
        {
            return TypeCode.Single;
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
