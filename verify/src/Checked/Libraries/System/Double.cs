// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Double
//
// Purpose: A representation of an IEEE double precision
//          floating point number.
//
//===========================================================  
namespace System
{

    using System;
    using System.Globalization;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="Double"]/*' />
    [StructLayout(LayoutKind.Sequential)]
    public struct Double : IComparable, IFormattable
    {
        internal double m_value;

        //
        // Public Constants
        //
        //| <include path='docs/doc[@for="Double.MinValue"]/*' />
        public const double MinValue = -1.7976931348623157E+308;
        //| <include path='docs/doc[@for="Double.MaxValue"]/*' />
        public const double MaxValue = 1.7976931348623157E+308;
        // Real value of Epsilon: 4.9406564584124654e-324 (0x1), but JVC misparses that
        // number, giving 2*Epsilon (0x2).
        //| <include path='docs/doc[@for="Double.Epsilon"]/*' />
        public const double Epsilon  = 4.9406564584124650E-324;
        //| <include path='docs/doc[@for="Double.NegativeInfinity"]/*' />
        public const double NegativeInfinity = (double)-1.0 / (double)(0.0);
        //| <include path='docs/doc[@for="Double.PositiveInfinity"]/*' />
        public const double PositiveInfinity = (double)1.0 / (double)(0.0);
        //| <include path='docs/doc[@for="Double.NaN"]/*' />
        public const double NaN = (double)0.0 / (double)0.0;

        //
        // Private constants
        //
        private const ulong PositiveInfinityAsUInt64 = 0x7ff0000000000000;
        private const ulong NegativeInfinityAsUInt64 = 0xfff0000000000000;

        private const ulong ExponentAsUInt64 = 0xfff0000000000000;
        private const ulong MantissaAsUInt64 = 0x000fffffffffffff;

        //
        // Native Declarations
        //
        //| <include path='docs/doc[@for="Double.IsInfinity"]/*' />
/*
        public static bool IsInfinity(double d) {
            ulong v = BitConverter.DoubleToUInt64Bits(d);
            return (v == PositiveInfinityAsUInt64 ||
                    v == NegativeInfinityAsUInt64);
        }

        //| <include path='docs/doc[@for="Double.IsPositiveInfinity"]/*' />
        public static bool IsPositiveInfinity(double d) {
            ulong v = BitConverter.DoubleToUInt64Bits(d);
            return (v == PositiveInfinityAsUInt64);
        }

        //| <include path='docs/doc[@for="Double.IsNegativeInfinity"]/*' />
        public static bool IsNegativeInfinity(double d) {
            ulong v = BitConverter.DoubleToUInt64Bits(d);
            return (v == NegativeInfinityAsUInt64);
        }

        //| <include path='docs/doc[@for="Double.IsNaN"]/*' />
        public static bool IsNaN(double d) {
            // See also Lightning\Src\ClassLibNative\Float\COMFloat::IsNAN
            ulong v = BitConverter.DoubleToUInt64Bits(d);
            return (((v & PositiveInfinityAsUInt64) == v) &&
                    ((v & MantissaAsUInt64) != 0));
        }
*/

        // Compares this object to another object, returning an instance of System.Relation.
        // Null is considered less than any instance.
        //
        // If object is not of type Double, this method throws an ArgumentException.
        //
        // Returns a value less than zero if this  object
        //
        //| <include path='docs/doc[@for="Double.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }
            if (value is Double) {
                double d = (double)value;
                if (m_value < d) return -1;
                if (m_value > d) return 1;
                if (m_value == d) return 0;

                // At least one of the values is NaN.
                throw new ArgumentException("Cannot compare NaN");
            }
            throw new ArgumentException("Arg_MustBeDouble");
        }

        // True if obj is another Double with the same value as the current instance.  This is
        // a method of object equality, that only returns true if obj is also a double.
        //| <include path='docs/doc[@for="Double.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is Double)) {
                return false;
            }
            double temp = ((Double)obj).m_value;
            // This code below is written this way for performance reasons i.e the != and == check is intentional.
            if (temp == m_value) {
                return true;
            }
            if (temp != m_value) {
                return false;
            }
            throw new ArgumentException("Cannot compare NaN");
        }

        //The hashcode for a double is the absolute value of the integer representation
        //of that double.
        //
        //| <include path='docs/doc[@for="Double.GetHashCode"]/*' />
/*
        public override int GetHashCode() {
            long value = unchecked((long)BitConverter.DoubleToUInt64Bits(m_value));
            return ((int)value) ^ ((int)(value >> 32));
        }
*/

        //| <include path='docs/doc[@for="Double.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }


        //| <include path='docs/doc[@for="Double.ToString1"]/*' />
        public String ToString(String format) {
            return "Double"; // TODO: Number.FormatDouble(m_value, format);
        }

        //| <include path='docs/doc[@for="Double.Parse"]/*' />
        public static double Parse(String s) {
            return Parse(s, NumberStyles.Float| NumberStyles.AllowThousands);
        }

        //| <include path='docs/doc[@for="Double.Parse1"]/*' />
        public static double Parse(String s, NumberStyles style) {
            try {
                return Number.ParseDouble(s, style);
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

        //| <include path='docs/doc[@for="Double.TryParse"]/*' />
        public static bool TryParse(String s, NumberStyles style, out double result) {
            if (s == null) {
                result = 0;
                return false;
            }
            bool success = Number.TryParseDouble(s, style, out result);
            if (!success) {
                String sTrim = s.Trim();
                if (sTrim.Equals(NumberFormatInfo.positiveInfinitySymbol)) {
                    result = PositiveInfinity;
                }
                else if (sTrim.Equals(NumberFormatInfo.negativeInfinitySymbol)) {
                    result = NegativeInfinity;
                }
                else if (sTrim.Equals(NumberFormatInfo.nanSymbol)) {
                    result = NaN;
                }
                else
                    return false; // We really failed
            }
            return true;
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Double.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode() {
            return TypeCode.Double;
        }
    }
}
