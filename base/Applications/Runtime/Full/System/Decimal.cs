// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    using System;
    using System.Diagnostics;
    using System.Globalization;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    // Implements the Decimal data type. The Decimal data type can
    // represent values ranging from -79,228,162,514,264,337,593,543,950,335 to
    // 79,228,162,514,264,337,593,543,950,335 with 28 significant digits. The
    // Decimal data type is ideally suited to financial calculations that
    // require a large number of significant digits and no round-off errors.
    //
    // The finite set of values of type Decimal are of the form m
    // / 10e, where m is an integer such that
    // -296 < m < 296, and e is an integer
    // between 0 and 28 inclusive.
    //
    // Contrary to the float and double data types, decimal
    // fractional numbers such as 0.1 can be represented exactly in the
    // Decimal representation. In the float and double
    // representations, such numbers are often infinite fractions, making those
    // representations more prone to round-off errors.
    //
    // The Decimal class implements widening conversions from the
    // ubyte, char, short, int, and long types
    // to Decimal. These widening conversions never loose any information
    // and never throw exceptions. The Decimal class also implements
    // narrowing conversions from Decimal to ubyte, char,
    // short, int, and long. These narrowing conversions round
    // the Decimal value towards zero to the nearest integer, and then
    // converts that integer to the destination type. An OverflowException
    // is thrown if the result is not within the range of the destination type.
    //
    // The Decimal class provides narrowing conversions to and from the
    // float and double types. A conversion from Decimal to
    // float or double may loose precision, but will not loose
    // information about the overall magnitude of the numeric value, and will never
    // throw an exception. A conversion from float or double to
    // Decimal throws an OverflowException if the value is not within
    // the range of the Decimal type.
    //| <include path='docs/doc[@for="Decimal"]/*' />
    [StructLayout(LayoutKind.Sequential)]
    [AccessedByRuntime("referenced in Decimal.cpp")]
    public struct Decimal : IFormattable, IComparable
    {
        // Sign mask for the flags field. A value of zero in this bit indicates a
        // positive Decimal value, and a value of one in this bit indicates a
        // negative Decimal value.
        //
        // Look at OleAut's DECIMAL_NEG constant to check for negative values
        // in native code.
        //| <include path='docs/doc[@for="Decimal.SignMask"]/*' />
        private const int SignMask  = unchecked((int)0x80000000);

        // Scale mask for the flags field. This byte in the flags field contains
        // the power of 10 to divide the Decimal value by. The scale byte must
        // contain a value between 0 and 28 inclusive.
        //| <include path='docs/doc[@for="Decimal.ScaleMask"]/*' />
        private const int ScaleMask = 0x00FF0000;

        // Number of bits scale is shifted by.
        private const int ScaleShift = 16;

        // Constant representing the Decimal value 0.
        //| <include path='docs/doc[@for="Decimal.Zero"]/*' />
        public const Decimal Zero = 0m;

        // Constant representing the Decimal value 1.
        //| <include path='docs/doc[@for="Decimal.One"]/*' />
        public const Decimal One = 1m;

        // Constant representing the Decimal value -1.
        //| <include path='docs/doc[@for="Decimal.MinusOne"]/*' />
        public const Decimal MinusOne = -1m;

        // Constant representing the largest possible Decimal value. The value of
        // this constant is 79,228,162,514,264,337,593,543,950,335.
        //| <include path='docs/doc[@for="Decimal.MaxValue"]/*' />
        public const Decimal MaxValue = 79228162514264337593543950335m;

        // Constant representing the smallest possible Decimal value. The value of
        // this constant is -79,228,162,514,264,337,593,543,950,335.
        //| <include path='docs/doc[@for="Decimal.MinValue"]/*' />
        public const Decimal MinValue = -79228162514264337593543950335m;


        // The lo, mid, hi, and flags fields contain the representation of the
        // Decimal value. The lo, mid, and hi fields contain the 96-bit integer
        // part of the Decimal. Bits 0-15 (the lower word) of the flags field are
        // unused and must be zero; bits 16-23 contain must contain a value between
        // 0 and 28, indicating the power of 10 to divide the 96-bit integer part
        // by to produce the Decimal value; bits 24-30 are unused and must be zero;
        // and finally bit 31 indicates the sign of the Decimal value, 0 meaning
        // positive and 1 meaning negative.
        //
        // NOTE: Do not change the order in which these fields are declared. The
        // native methods in this class rely on this particular order.
        private int flags;
        private int hi;
        private int lo;
        private int mid;

        internal short reserved {
            get { return unchecked((short) (this.flags & 0xFFFF)); }
            set { this.flags = ((this.flags & ~0xFFFF) | (value & 0xFFFF)); }
        }

        internal byte scale {
            get { return unchecked((byte) (this.flags >> 16)); }
            set { this.flags = ((this.flags & ~0xFF0000) | (value << 16)); }
        }

        internal bool negative {
            get { return (this.flags < 0); }
            set { this.flags = (value ? (this.flags & 0x00FFFFFF) : (this.flags | ~0x7FFFFFFF)); }
        }

        internal uint hi32 {
            get { return unchecked((uint) this.hi); }
            set { this.hi = unchecked((int) value); }
        }

        internal uint mid32 {
            get { return unchecked((uint) this.mid); }
            set { this.mid = unchecked((int) value); }
        }

        internal uint lo32 {
            get { return unchecked((uint) this.lo); }
            set { this.lo = unchecked((int) value); }
        }

        // Constructs a zero Decimal.
        //public Decimal() {
        //    lo = 0;
        //    mid = 0;
        //    hi = 0;
        //    flags = 0;
        //}

        // Constructs a Decimal from an integer value.
        //
        //| <include path='docs/doc[@for="Decimal.Decimal"]/*' />
        public Decimal(int value) {
            if (value >= 0) {
                flags = 0;
            }
            else {
                flags = SignMask;
                value = -value;
            }
            lo = value;
            mid = 0;
            hi = 0;
        }

        // Constructs a Decimal from an unsigned integer value.
        //
        //| <include path='docs/doc[@for="Decimal.Decimal1"]/*' />
        [CLSCompliant(false)]
        public Decimal(uint value) {
            flags = 0;
            lo = (int) value;
            mid = 0;
            hi = 0;
        }

        // Constructs a Decimal from a long value.
        //
        //| <include path='docs/doc[@for="Decimal.Decimal2"]/*' />
        public Decimal(long value) {
            if (value >= 0) {
                flags = 0;
            }
            else {
                flags = SignMask;
                value = -value;
            }
            lo = (int)value;
            mid = (int)(value >> 32);
            hi = 0;
        }

        // Constructs a Decimal from an unsigned long value.
        //
        //| <include path='docs/doc[@for="Decimal.Decimal3"]/*' />
        [CLSCompliant(false)]
        public Decimal(ulong value) {
            flags = 0;
            lo = (int)value;
            mid = (int)(value >> 32);
            hi = 0;
        }

        // Constructs a Decimal from a float value.
        //
        //| <include path='docs/doc[@for="Decimal.Decimal4"]/*' />
        public Decimal(float value) {
            // See also Lightning\Src\VM\COMDecimal.cpp::InitSingle
            if (DecimalFromFloat(value, out this) < 0) {
                throw new OverflowException("Overflow_Decimal");
            }
            this.reserved = 0;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [GCAnnotation(GCOption.NONE)]
        private static extern int DecimalFromFloat(float f, out Decimal result);

        // Constructs a Decimal from a double value.
        //
        //| <include path='docs/doc[@for="Decimal.Decimal5"]/*' />
        public Decimal(double value) {
            // See also Lightning\Src\VM\COMDecimal.cpp::InitDouble
            if (DecimalFromDouble(value, out this) < 0) {
                throw new OverflowException("Overflow_Decimal");
            }
            this.reserved = 0;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DecimalFromDouble(double d, out Decimal result);

        // Constructs a Decimal from an integer array containing a binary
        // representation. The bits argument must be a non-null integer
        // array with four elements. bits[0], bits[1], and
        // bits[2] contain the low, middle, and high 32 bits of the 96-bit
        // integer part of the Decimal. bits[3] contains the scale factor
        // and sign of the Decimal: bits 0-15 (the lower word) are unused and must
        // be zero; bits 16-23 must contain a value between 0 and 28, indicating
        // the power of 10 to divide the 96-bit integer part by to produce the
        // Decimal value; bits 24-30 are unused and must be zero; and finally bit
        // 31 indicates the sign of the Decimal value, 0 meaning positive and 1
        // meaning negative.
        //
        // Note that there are several possible binary representations for the
        // same numeric value. For example, the value 1 can be represented as {1,
        // 0, 0, 0} (integer value 1 with a scale factor of 0) and equally well as
        // {1000, 0, 0, 0x30000} (integer value 1000 with a scale factor of 3).
        // The possible binary representations of a particular value are all
        // equally valid, and all are numerically equivalent.
        //
        //| <include path='docs/doc[@for="Decimal.Decimal7"]/*' />
        public Decimal(int[] bits) {
            if (bits == null)
                throw new ArgumentNullException("bits");
            if (bits.Length == 4) {
                int f = bits[3];
                if ((f & ~(SignMask | ScaleMask)) == 0 && (f & ScaleMask) <= (28 << 16)) {
                    lo = bits[0];
                    mid = bits[1];
                    hi = bits[2];
                    flags = f;
                    return;
                }
            }
            throw new ArgumentException("Arg_DecBitCtor");
        }

        // Constructs a Decimal from its constituent parts.
        //
        //| <include path='docs/doc[@for="Decimal.Decimal8"]/*' />
        public Decimal(int lo, int mid, int hi, bool isNegative, byte scale) {
            if (scale > 28)
                throw new ArgumentOutOfRangeException("ArgumentOutOfRange_DecimalScale");
            this.lo = lo;
            this.mid = mid;
            this.hi = hi;
            this.flags = ((int)scale) << 16;
            if (isNegative)
                this.flags |= SignMask;
        }

        // Constructs a Decimal from its constituent parts.
        private Decimal(int lo, int mid, int hi, int flags) {
            this.lo = lo;
            this.mid = mid;
            this.hi = hi;
            this.flags = flags;
        }

        // Returns the absolute value of the given Decimal. If d is
        // positive, the result is d. If d is negative, the result
        // is -d.
        //
        //| <include path='docs/doc[@for="Decimal.Abs"]/*' />
        internal static Decimal Abs(Decimal d) {
            return new Decimal(d.lo, d.mid, d.hi, d.flags & ~SignMask);
        }

        // Adds two Decimal values.
        //
        //| <include path='docs/doc[@for="Decimal.Add"]/*' />
        public static Decimal Add(Decimal d1, Decimal d2) {
            // See also Lightning\Src\VM\COMDecimal.cpp::Add
            Decimal result;
            if (DecimalAdd(ref d2, ref d1, out result) < 0) {
                throw new OverflowException("Decimal.Add");
            }
            result.reserved = 0;
            return result;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DecimalAdd(ref Decimal d1, ref Decimal d2,
                                             out Decimal result);


        // Compares two Decimal values, returning an integer that indicates their
        // relationship.
        //
        //| <include path='docs/doc[@for="Decimal.Compare"]/*' />
        public static int Compare(Decimal d1, Decimal d2) {
            // See also Lightning\Src\VM\COMDecimal.cpp::Compare
            return (DecimalCompare(ref d2, ref d1) - 1);
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DecimalCompare(ref Decimal d1, ref Decimal d2);

        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type Decimal, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="Decimal.CompareTo"]/*' />
        public int CompareTo(Object value)
        {
            if (value == null)
                return 1;
            if (!(value is Decimal))
                throw new ArgumentException("Arg_MustBeDecimal");

            return Decimal.Compare(this, (Decimal)value);
        }

        // Divides two Decimal values.
        //
        //| <include path='docs/doc[@for="Decimal.Divide"]/*' />
        public static Decimal Divide(Decimal d1, Decimal d2) {
            // See also Lightning\Src\VM\COMDecimal.cpp::Divide
            Decimal result;
            if (DecimalDivide(ref d2, ref d1, out result) < 0) {
                throw new OverflowException("Decimal.Divide");
            }
            result.reserved = 0;
            return result;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DecimalDivide(ref Decimal d1, ref Decimal d2,
                                                out Decimal result);

        // Checks if this Decimal is equal to a given object. Returns true
        // if the given object is a boxed Decimal and its value is equal to the
        // value of this Decimal. Returns false otherwise.
        //
        //| <include path='docs/doc[@for="Decimal.Equals"]/*' />
        public override bool Equals(Object value) {
            if (value is Decimal) {
                return Compare(this, (Decimal)value) == 0;
            }
            return false;
        }


        // Returns the hash code for this Decimal.
        //
        //| <include path='docs/doc[@for="Decimal.GetHashCode"]/*' />
        public override int GetHashCode() {
            // See also Lightning\Src\VM\COMDecimal.cpp::GetHashCode
            double dbl;
            if (DoubleFromDecimal(ref this, out dbl) != 0) {
                throw new Exception("Decimal.GetHashCode failure");
            }
            return dbl.GetHashCode();
        }

        // Compares two Decimal values for equality. Returns true if the two
        // Decimal values are equal, or false if they are not equal.
        //
        //| <include path='docs/doc[@for="Decimal.Equals1"]/*' />
        public static bool Equals(Decimal d1, Decimal d2) {
            return Compare(d1, d2) == 0;
        }


        // Rounds a Decimal to an integer value. The Decimal argument is rounded
        // towards negative infinity.
        //
        //| <include path='docs/doc[@for="Decimal.Floor"]/*' />
        public static Decimal Floor(Decimal d) {
            // See also Lightning\Src\VM\COMDecimal.cpp::Floor
            Decimal result;
            DecimalFloor(ref d, out result);
            return result;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DecimalFloor(ref Decimal d, out Decimal result);

        // Converts this Decimal to a string. The resulting string consists of an
        // optional minus sign ("-") followed to a sequence of digits ("0" - "9"),
        // optionally followed by a decimal point (".") and another sequence of
        // digits.
        //
        //| <include path='docs/doc[@for="Decimal.ToString"]/*' />
        public override String ToString() {
            return ToString(null);
        }


        //| <include path='docs/doc[@for="Decimal.ToString1"]/*' />
        public String ToString(String format) {
            return Number.FormatDecimal(this, format);
        }


        // Converts a string to a Decimal. The string must consist of an optional
        // minus sign ("-") followed by a sequence of digits ("0" - "9"). The
        // sequence of digits may optionally contain a single decimal point (".")
        // character. Leading and trailing whitespace characters are allowed.
        // Parse also a trailing negative sign, and parentheses in the number.
        //
        //| <include path='docs/doc[@for="Decimal.Parse"]/*' />
        public static Decimal Parse(String s) {
            return Parse(s, NumberStyles.Number);
        }

        //| <include path='docs/doc[@for="Decimal.Parse1"]/*' />
        public static Decimal Parse(String s, NumberStyles style) {
            return Number.ParseDecimal(s, style);
        }

        // Returns a binary representation of a <i>Decimal</i>. The return value is an
        // integer array with four elements. Elements 0, 1, and 2 contain the low,
        // middle, and high 32 bits of the 96-bit integer part of the <i>Decimal</i>.
        // Element 3 contains the scale factor and sign of the <i>Decimal</i>: bits 0-15
        // (the lower word) are unused; bits 16-23 contain a value between 0 and
        // 28, indicating the power of 10 to divide the 96-bit integer part by to
        // produce the <i>Decimal</i> value; bits 24-30 are unused; and finally bit 31
        // indicates the sign of the <i>Decimal</i> value, 0 meaning positive and 1
        // meaning negative.
        //
        // @param d A <i>Decimal</i> value.
        // @return An integer array with four elements containing the binary
        // representation of the argument.
        // @see Decimal(int[])
        // 
        //| <include path='docs/doc[@for="Decimal.GetBits"]/*' />
        public static int[] GetBits(Decimal d) {
            return new int[] {d.lo, d.mid, d.hi, d.flags};
        }

        public static void GetBytes(Decimal d, byte [] buffer) {
            if (buffer == null || buffer.Length < 16) {
                throw new ArgumentException("Arg_MustBe16Bytes");
            }

            buffer[0] = (byte) d.lo;
            buffer[1] = (byte) (d.lo >> 8);
            buffer[2] = (byte) (d.lo >> 16);
            buffer[3] = (byte) (d.lo >> 24);

            buffer[4] = (byte) d.mid;
            buffer[5] = (byte) (d.mid >> 8);
            buffer[6] = (byte) (d.mid >> 16);
            buffer[7] = (byte) (d.mid >> 24);

            buffer[8] = (byte) d.hi;
            buffer[9] = (byte) (d.hi >> 8);
            buffer[10] = (byte) (d.hi >> 16);
            buffer[11] = (byte) (d.hi >> 24);

            buffer[12] = (byte) d.flags;
            buffer[13] = (byte) (d.flags >> 8);
            buffer[14] = (byte) (d.flags >> 16);
            buffer[15] = (byte) (d.flags >> 24);
        }

        public static decimal ToDecimal(byte [] buffer) {
            if (buffer == null || buffer.Length < 16) {
                throw new ArgumentException("Arg_MustBe16Bytes");
            }

            int lo = ((int)buffer[0]) | ((int)buffer[1] << 8) | ((int)buffer[2] << 16) | ((int)buffer[3] << 24);
            int mid = ((int)buffer[4]) | ((int)buffer[5] << 8) | ((int)buffer[6] << 16) | ((int)buffer[7] << 24);
            int hi = ((int)buffer[8]) | ((int)buffer[9] << 8) | ((int)buffer[10] << 16) | ((int)buffer[11] << 24);
            int flags = ((int)buffer[12]) | ((int)buffer[13] << 8) | ((int)buffer[14] << 16) | ((int)buffer[15] << 24);
            return new Decimal(lo,mid,hi,flags);
        }


        // Returns the larger of two Decimal values.
        //
        //| <include path='docs/doc[@for="Decimal.Max"]/*' />
        internal static Decimal Max(Decimal d1, Decimal d2) {
            return Compare(d1, d2) >= 0? d1: d2;
        }

        // Returns the smaller of two Decimal values.
        //
        //| <include path='docs/doc[@for="Decimal.Min"]/*' />
        internal static Decimal Min(Decimal d1, Decimal d2) {
            return Compare(d1, d2) < 0? d1: d2;
        }

        //| <include path='docs/doc[@for="Decimal.Remainder"]/*' />
        public static Decimal Remainder(Decimal d1, Decimal d2) {
            // See also Lightning\Src\VM\COMDecimal.cpp::Remainder
            Decimal tmp = Truncate(Divide(d1, d2));
            return Subtract(d1, Multiply(d2, tmp));
        }

        // Multiplies two Decimal values.
        //
        //| <include path='docs/doc[@for="Decimal.Multiply"]/*' />
        public static Decimal Multiply(Decimal d1, Decimal d2) {
            // See also Lightning\Src\VM\COMDecimal.cpp::Multiply
            Decimal result;
            if (DecimalMultiply(ref d1, ref d2, out result) < 0) {
                throw new OverflowException("Decimal.Multiply");
            }
            result.reserved = 0;
            return result;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DecimalMultiply(ref Decimal d1, ref Decimal d2,
                                                  out Decimal result);

        // Returns the negated value of the given Decimal. If d is non-zero,
        // the result is -d. If d is zero, the result is zero.
        //
        //| <include path='docs/doc[@for="Decimal.Negate"]/*' />
        public static Decimal Negate(Decimal d) {
            return new Decimal(d.lo, d.mid, d.hi, d.flags ^ SignMask);
        }

        // Rounds a Decimal value to a given number of decimal places. The value
        // given by d is rounded to the number of decimal places given by
        // decimals. The decimals argument must be an integer between
        // 0 and 28 inclusive.
        //
        // The operation Decimal.Round(d, dec) conceptually
        // corresponds to evaluating Decimal.Truncate(d *
        // 10^dec + delta) / 10^dec, where
        // delta is 0.5 for positive values of d and -0.5 for
        // negative values of d.
        //
        //| <include path='docs/doc[@for="Decimal.Round"]/*' />
        public static Decimal Round(Decimal d1, int decimals) {
            // See also Lightning\Src\VM\COMDecimal.cpp::Round
            Decimal result;
            if (decimals < 0 || decimals > 28) {
                throw new ArgumentOutOfRangeException("decimals");
            }
            if (DecimalRound(ref d1, decimals, out result) < 0) {
                throw new OverflowException("Decimal.Round");
            }
            result.reserved = 0;
            return result;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DecimalRound(ref Decimal d, int decimals,
                                               out Decimal result);

        // Subtracts two Decimal values.
        //
        //| <include path='docs/doc[@for="Decimal.Subtract"]/*' />
        public static Decimal Subtract(Decimal d1, Decimal d2) {
            // See also Lightning\Src\VM\COMDecimal.cpp::Subtract
            Decimal result;
            if (DecimalSubtract(ref d1, ref d2, out result) < 0) {
                throw new OverflowException("Decimal.Subtract");
            }
            result.reserved = 0;
            return result;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DecimalSubtract(ref Decimal d1, ref Decimal d2,
                                                  out Decimal result);

        // Converts a Decimal to an unsigned byte. The Decimal value is rounded
        // towards zero to the nearest integer value, and the result of this
        // operation is returned as a byte.
        //
        //| <include path='docs/doc[@for="Decimal.ToByte"]/*' />
        public static byte ToByte(Decimal value) {
            uint temp =  ToUInt32(value);
            if (temp < Byte.MinValue || temp > Byte.MaxValue) throw new OverflowException("Overflow_Byte");
            return (byte)temp;

        }

        // Converts a Decimal to a signed byte. The Decimal value is rounded
        // towards zero to the nearest integer value, and the result of this
        // operation is returned as a byte.
        //
        //| <include path='docs/doc[@for="Decimal.ToSByte"]/*' />
        [CLSCompliant(false)]
        public static sbyte ToSByte(Decimal value) {
            int temp =  ToInt32(value);
            if (temp < SByte.MinValue || temp > SByte.MaxValue) throw new OverflowException("Overflow_SByte");
            return (sbyte)temp;
        }

        // Converts a Decimal to a short. The Decimal value is
        // rounded towards zero to the nearest integer value, and the result of
        // this operation is returned as a short.
        //
        //| <include path='docs/doc[@for="Decimal.ToInt16"]/*' />
        public static short ToInt16(Decimal value) {
            int temp =  ToInt32(value);
            if (temp < Int16.MinValue || temp > Int16.MaxValue) throw new OverflowException("Overflow_Int16");
            return (short)temp;
        }

        // Converts a Decimal to a double. Since a double has fewer significant
        // digits than a Decimal, this operation may produce round-off errors.
        //
        //| <include path='docs/doc[@for="Decimal.ToDouble"]/*' />
        public static double ToDouble(Decimal d) {
            // See also Lightning\Src\VM\COMDecimal.cpp
            double result;
            DoubleFromDecimal(ref d, out result);
            return result;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DoubleFromDecimal(ref Decimal d, out double result);

        // Converts a Decimal to an integer. The Decimal value is rounded towards
        // zero to the nearest integer value, and the result of this operation is
        // returned as an integer.
        //
        //| <include path='docs/doc[@for="Decimal.ToInt32"]/*' />
        public static int ToInt32(Decimal d) {
            if ((d.flags & ScaleMask) != 0) d = Truncate(d);
            if (d.hi == 0 && d.mid == 0) {
                int i = d.lo;
                if (d.flags >= 0) {
                    if (i >= 0) return i;
                }
                else {
                    i = -i;
                    if (i <= 0) return i;
                }
            }
            throw new OverflowException("Overflow_Int32");
        }

        // Converts a Decimal to a long. The Decimal value is rounded towards zero
        // to the nearest integer value, and the result of this operation is
        // returned as a long.
        //
        //| <include path='docs/doc[@for="Decimal.ToInt64"]/*' />
        public static long ToInt64(Decimal d) {
            if ((d.flags & ScaleMask) != 0) d = Truncate(d);
            if (d.hi == 0) {
                long l = d.lo & 0xFFFFFFFFL | (long)d.mid << 32;
                if (d.flags >= 0) {
                    if (l >= 0) return l;
                }
                else {
                    l = -l;
                    if (l <= 0) return l;
                }
            }
            throw new OverflowException("Overflow_Int64");
        }

        // Converts a Decimal to an ushort. The Decimal
        // value is rounded towards zero to the nearest integer value, and the
        // result of this operation is returned as an ushort.
        //
        //| <include path='docs/doc[@for="Decimal.ToUInt16"]/*' />
        [CLSCompliant(false)]
        public static ushort ToUInt16(Decimal value) {
            uint temp =  ToUInt32(value);
            if (temp < UInt16.MinValue || temp > UInt16.MaxValue) throw new OverflowException("Overflow_UInt16");
            return (ushort)temp;
        }

        // Converts a Decimal to an unsigned integer. The Decimal
        // value is rounded towards zero to the nearest integer value, and the
        // result of this operation is returned as an unsigned integer.
        //
        //| <include path='docs/doc[@for="Decimal.ToUInt32"]/*' />
        [CLSCompliant(false)]
        public static uint ToUInt32(Decimal d) {
            if ((d.flags & ScaleMask) != 0) d = Truncate(d);
            if (d.hi == 0 && d.mid == 0) {
                uint i = (uint) d.lo;
                if (d.flags >= 0 || i == 0)
                    return i;
            }
            throw new OverflowException("Overflow_UInt32");
        }

        // Converts a Decimal to an unsigned long. The Decimal
        // value is rounded towards zero to the nearest integer value, and the
        // result of this operation is returned as a long.
        //
        //| <include path='docs/doc[@for="Decimal.ToUInt64"]/*' />
        [CLSCompliant(false)]
        public static ulong ToUInt64(Decimal d) {
            if ((d.flags & ScaleMask) != 0) d = Truncate(d);
            if (d.hi == 0) {
                ulong l = ((ulong)(uint)d.lo) | ((ulong)(uint)d.mid << 32);
                if (d.flags >= 0 || l == 0)
                    return l;
            }
            throw new OverflowException("Overflow_UInt64");
        }

        // Converts a Decimal to a float. Since a float has fewer significant
        // digits than a Decimal, this operation may produce round-off errors.
        //
        //| <include path='docs/doc[@for="Decimal.ToSingle"]/*' />
        public static float ToSingle(Decimal d) {
            // See also Lightning\Src\VM\COMDecimal.cpp
            float result;
            FloatFromDecimal(ref d, out result);
            return result;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int FloatFromDecimal(ref Decimal d, out float result);

        // Truncates a Decimal to an integer value. The Decimal argument is rounded
        // towards zero to the nearest integer value, corresponding to removing all
        // digits after the decimal point.
        //
        //| <include path='docs/doc[@for="Decimal.Truncate"]/*' />
        public static Decimal Truncate(Decimal d) {
            Decimal result;
            DecimalTruncate(ref d, out result);
            return result;
        }

        [AccessedByRuntime("Output to header:defined in Decimal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        private static extern int DecimalTruncate(ref Decimal d, out Decimal result);

        //| <include path='docs/doc[@for="Decimal.operatorDecimal"]/*' />
        public static implicit operator Decimal(byte value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDecimal1"]/*' />
        [CLSCompliant(false)]
        public static implicit operator Decimal(sbyte value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDecimal2"]/*' />
        public static implicit operator Decimal(short value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDecimal3"]/*' />
        [CLSCompliant(false)]
        public static implicit operator Decimal(ushort value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDecimal4"]/*' />
        public static implicit operator Decimal(char value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDecimal5"]/*' />
        public static implicit operator Decimal(int value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDecimal6"]/*' />
        [CLSCompliant(false)]
        public static implicit operator Decimal(uint value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDecimal7"]/*' />
        public static implicit operator Decimal(long value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDecimal8"]/*' />
        [CLSCompliant(false)]
        public static implicit operator Decimal(ulong value) {
            return new Decimal(value);
        }


        //| <include path='docs/doc[@for="Decimal.operatorDecimal9"]/*' />
        public static explicit operator Decimal(float value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDecimal10"]/*' />
        public static explicit operator Decimal(double value) {
            return new Decimal(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorbyte"]/*' />
        public static explicit operator byte(Decimal value) {
            return ToByte(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorsbyte"]/*' />
        [CLSCompliant(false)]
        public static explicit operator sbyte(Decimal value) {
            return ToSByte(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorchar"]/*' />
        public static explicit operator char(Decimal value) {
            return (char)ToUInt16(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorshort"]/*' />
        public static explicit operator short(Decimal value) {
            return ToInt16(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorushort"]/*' />
        [CLSCompliant(false)]
        public static explicit operator ushort(Decimal value) {
            return ToUInt16(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorint"]/*' />
        public static explicit operator int(Decimal value) {
            return ToInt32(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatoruint"]/*' />
        [CLSCompliant(false)]
        public static explicit operator uint(Decimal value) {
            return ToUInt32(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorlong"]/*' />
        public static explicit operator long(Decimal value) {
            return ToInt64(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorulong"]/*' />
        [CLSCompliant(false)]
        public static explicit operator ulong(Decimal value) {
            return ToUInt64(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorfloat"]/*' />
        public static explicit operator float(Decimal value) {
            return ToSingle(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatordouble"]/*' />
        public static explicit operator double(Decimal value) {
            return ToDouble(value);
        }

        //| <include path='docs/doc[@for="Decimal.operatorADD1"]/*' />
        public static Decimal operator +(Decimal d) {
            return d;
        }

        //| <include path='docs/doc[@for="Decimal.operatorSUB1"]/*' />
        public static Decimal operator -(Decimal d) {
            return Negate(d);
        }

        //| <include path='docs/doc[@for="Decimal.operatorINC"]/*' />
        public static Decimal operator ++(Decimal d) {
            return Add(d, One);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDEC"]/*' />
        public static Decimal operator --(Decimal d) {
            return Subtract(d, One);
        }

        //| <include path='docs/doc[@for="Decimal.operatorADD2"]/*' />
        public static Decimal operator +(Decimal d1, Decimal d2) {
            return Add(d1, d2);
        }

        //| <include path='docs/doc[@for="Decimal.operatorSUB2"]/*' />
        public static Decimal operator -(Decimal d1, Decimal d2) {
            return Subtract(d1, d2);
        }

        //| <include path='docs/doc[@for="Decimal.operatorMUL"]/*' />
        public static Decimal operator *(Decimal d1, Decimal d2) {
            return Multiply(d1, d2);
        }

        //| <include path='docs/doc[@for="Decimal.operatorDIV"]/*' />
        public static Decimal operator /(Decimal d1, Decimal d2) {
            return Divide(d1, d2);
        }

        //| <include path='docs/doc[@for="Decimal.operatorMOD"]/*' />
        public static Decimal operator %(Decimal d1, Decimal d2) {
            return Remainder(d1, d2);
        }

        //private static bool operator equals(Decimal d1, Decimal d2) {
        //return Compare(d1, d2) == 0;
        //}
//
        //private static int operator compare(Decimal d1, Decimal d2) {
        //int c = Compare(d1, d2);
        //if (c < 0) return -1;
        //if (c > 0) return 1;
        //return 0;
        //}  

        //| <include path='docs/doc[@for="Decimal.operatorEQ"]/*' />
        public static bool operator ==(Decimal d1, Decimal d2) {
            return Compare(d1, d2) == 0;
        }

        //| <include path='docs/doc[@for="Decimal.operatorNE"]/*' />
        public static bool operator !=(Decimal d1, Decimal d2) {
            return Compare(d1, d2) != 0;
        }

        //| <include path='docs/doc[@for="Decimal.operatorLT"]/*' />
        public static bool operator <(Decimal d1, Decimal d2) {
            return Compare(d1, d2) < 0;
        }

        //| <include path='docs/doc[@for="Decimal.operatorLE"]/*' />
        public static bool operator <=(Decimal d1, Decimal d2) {
            return Compare(d1, d2) <= 0;
        }

        //| <include path='docs/doc[@for="Decimal.operatorGT"]/*' />
        public static bool operator >(Decimal d1, Decimal d2) {
            return Compare(d1, d2) > 0;
        }

        //| <include path='docs/doc[@for="Decimal.operatorGE"]/*' />
        public static bool operator >=(Decimal d1, Decimal d2) {
            return Compare(d1, d2) >= 0;
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Decimal.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode() {
            return TypeCode.Decimal;
        }
    }
}
