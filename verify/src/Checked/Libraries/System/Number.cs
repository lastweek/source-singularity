// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System
{

    using System;
    using System.Globalization;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using NumberFormatInfo = System.Globalization.NumberFormatInfo;
    using NumberStyles = System.Globalization.NumberStyles;

    // The Number class implements methods for formatting and parsing
    // numeric values. To format and parse numeric values, applications should
    // use the Format and Parse methods provided by the numeric
    // classes (Byte, Int16, Int32, Int64,
    // Single, Double, and Decimal). Those
    // Format and Parse methods share a common implementation
    // provided by this class, and are thus documented in detail here.
    //
    // Formatting
    //
    // The Format methods provided by the numeric classes are all of the
    // form
    //
    //  public static String Format(XXX value, String format);
    //
    // where XXX is the name of the particular numeric class. The methods convert
    // the numeric value to a string using the format string given by the
    // format parameter. If the format parameter is null or
    // an empty string, the number is formatted as if the string "G" (general
    // format) was specified.
    //
    // Format strings fall into two categories: Standard format strings and
    // user-defined format strings. A format string consisting of a single
    // alphabetic character (A-Z or a-z), optionally followed by a sequence of
    // digits (0-9), is a standard format string. All other format strings are
    // used-defined format strings.
    //
    // A standard format string takes the form Axx, where A is an
    // alphabetic character called the format specifier and xx is a
    // sequence of digits called the precision specifier. The format
    // specifier controls the type of formatting applied to the number and the
    // precision specifier controls the number of significant digits or decimal
    // places of the formatting operation. The following table describes the
    // supported standard formats.
    //
    //
    // FormatDescription
    //
    // DdDecimal format. This format is
    // supported for integral types only. The number is converted to a string of
    // decimal digits, prefixed by a minus sign if the number is negative. The
    // precision specifier indicates the minimum number of digits desired in the
    // resulting string. If required, the number will be left-padded with zeros to
    // produce the number of digits given by the precision specifier.
    //
    // EeEngineering (scientific) format.
    // The number is converted to a string of the form
    // "-d.ddd...E+ddd" or "-d.ddd...e+ddd", where each
    // 'd' indicates a digit (0-9). The string starts with a minus sign if the
    // number is negative, and one digit always precedes the decimal point. The
    // precision specifier indicates the desired number of digits after the decimal
    // point. If the precision specifier is omitted, a default of 6 digits after
    // the decimal point is used. The format specifier indicates whether to prefix
    // the exponent with an 'E' or an 'e'. The exponent is always consists of a
    // plus or minus sign and three digits.
    //
    // FfFixed point format. The number is
    // converted to a string of the form "-ddd.ddd....", where each
    // 'd' indicates a digit (0-9). The string starts with a minus sign if the
    // number is negative. The precision specifier indicates the desired number of
    // decimal places. If the precision specifier is omitted, the default numeric
    // precision is used.
    //
    // GgGeneral format. The number is
    // converted to the shortest possible decimal representation using fixed point
    // or scientific format. The precision specifier determines the number of
    // significant digits in the resulting string. If the precision specifier is
    // omitted, the number of significant digits is determined by the type of the
    // number being converted (10 for int, 19 for long, 7 for
    // float, 15 for double, and 29 for
    // Decimal). Trailing zeros after the decimal point are removed, and the
    // resulting string contains a decimal point only if required. The resulting
    // string uses fixed point format if the exponent of the number is less than
    // the number of significant digits and greater than or equal to -4. Otherwise,
    // the resulting string uses scientific format, and the case of the format
    // specifier controls whether the exponent is prefixed with an 'E' or an
    // 'e'.
    //
    // NnNumber format. The number is
    // converted to a string of the form "-d,ddd,ddd.ddd....", where
    // each 'd' indicates a digit (0-9). The string starts with a minus sign if the
    // number is negative. Thousand separators are inserted between each group of
    // three digits to the left of the decimal point. The precision specifier
    // indicates the desired number of decimal places. If the precision specifier
    // is omitted, the default numeric precision is used.
    //
    // XxHexadecimal format. This format is
    // supported for integral types only. The number is converted to a string of
    // hexadecimal digits. The format specifier indicates whether to use upper or
    // lower case characters for the hexadecimal digits above 9 ('X' for 'ABCDEF',
    // and 'x' for 'abcdef'). The precision specifier indicates the minimum number
    // of digits desired in the resulting string. If required, the number will be
    // left-padded with zeros to produce the number of digits given by the
    // precision specifier.
    //
    //
    //
    // Some examples of standard format strings and their results are shown in the
    // table below.
    //
    //
    // ValueFormatResult
    // 12345.6789C$12,345.68
    // -12345.6789C($12,345.68)
    // 12345D12345
    // 12345D800012345
    // 12345.6789E1.234568E+004
    // 12345.6789E101.2345678900E+004
    // 12345.6789e41.2346e+004
    // 12345.6789F12345.68
    // 12345.6789F012346
    // 12345.6789F612345.678900
    // 12345.6789G12345.6789
    // 12345.6789G712345.68
    // 123456789G71.234568E8
    // 12345.6789N12,345.68
    // 123456789N4123,456,789.0000
    // 0x2c45ex2c45e
    // 0x2c45eX2C45E
    // 0x2c45eX80002C45E
    //
    //
    // Format strings that do not start with an alphabetic character, or that start
    // with an alphabetic character followed by a non-digit, are called
    // user-defined format strings. The following table describes the formatting
    // characters that are supported in user defined format strings.
    //
    //
    // CharacterDescription
    //
    // 0Digit placeholder. If the value being
    // formatted has a digit in the position where the '0' appears in the format
    // string, then that digit is copied to the output string. Otherwise, a '0' is
    // stored in that position in the output string. The position of the leftmost
    // '0' before the decimal point and the rightmost '0' after the decimal point
    // determines the range of digits that are always present in the output
    // string.
    //
    // #Digit placeholder. If the value being
    // formatted has a digit in the position where the '#' appears in the format
    // string, then that digit is copied to the output string. Otherwise, nothing
    // is stored in that position in the output string.
    //
    // .Decimal point. The first '.' character
    // in the format string determines the location of the decimal separator in the
    // formatted value; any additional '.' characters are ignored. The actual
    // character used as a the decimal separator in the output string is given by
    // the NumberFormatInfo used to format the number.
    //
    // ,Thousand separator and number scaling.
    // The ',' character serves two purposes. First, if the format string contains
    // a ',' character between two digit placeholders (0 or #) and to the left of
    // the decimal point if one is present, then the output will have thousand
    // separators inserted between each group of three digits to the left of the
    // decimal separator. The actual character used as a the decimal separator in
    // the output string is given by the NumberFormatInfo used to format the
    // number. Second, if the format string contains one or more ',' characters
    // immediately to the left of the decimal point, or after the last digit
    // placeholder if there is no decimal point, then the number will be divided by
    // 1000 times the number of ',' characters before it is formatted. For example,
    // the format string '0,,' will represent 100 million as just 100. Use of the
    // ',' character to indicate scaling does not also cause the formatted number
    // to have thousand separators. Thus, to scale a number by 1 million and insert
    // thousand separators you would use the format string '#,##0,,'.
    //
    // %Percentage placeholder. The presence of
    // a '%' character in the format string causes the number to be multiplied by
    // 100 before it is formatted. The '%' character itself is inserted in the
    // output string where it appears in the format string.
    //
    // E+E-e+e-Scientific notation.
    // If any of the strings 'E+', 'E-', 'e+', or 'e-' are present in the format
    // string and are immediately followed by at least one '0' character, then the
    // number is formatted using scientific notation with an 'E' or 'e' inserted
    // between the number and the exponent. The number of '0' characters following
    // the scientific notation indicator determines the minimum number of digits to
    // output for the exponent. The 'E+' and 'e+' formats indicate that a sign
    // character (plus or minus) should always precede the exponent. The 'E-' and
    // 'e-' formats indicate that a sign character should only precede negative
    // exponents.
    //
    // \Literal character. A backslash character
    // causes the next character in the format string to be copied to the output
    // string as-is. The backslash itself isn't copied, so to place a backslash
    // character in the output string, use two backslashes (\\) in the format
    // string.
    //
    // 'ABC'"ABC"Literal string. Characters
    // enclosed in single or double quotation marks are copied to the output string
    // as-is and do not affect formatting.
    //
    // ;Section separator. The ';' character is
    // used to separate sections for positive, negative, and zero numbers in the
    // format string.
    //
    // OtherAll other characters are copied to
    // the output string in the position they appear.
    //
    //
    //
    // For fixed point formats (formats not containing an 'E+', 'E-', 'e+', or
    // 'e-'), the number is rounded to as many decimal places as there are digit
    // placeholders to the right of the decimal point. If the format string does
    // not contain a decimal point, the number is rounded to the nearest
    // integer. If the number has more digits than there are digit placeholders to
    // the left of the decimal point, the extra digits are copied to the output
    // string immediately before the first digit placeholder.
    //
    // For scientific formats, the number is rounded to as many significant digits
    // as there are digit placeholders in the format string.
    //
    // To allow for different formatting of positive, negative, and zero values, a
    // user-defined format string may contain up to three sections separated by
    // semicolons. The results of having one, two, or three sections in the format
    // string are described in the table below.
    //
    //
    // SectionsResult
    //
    // OneThe format string applies to all
    // values.
    //
    // TwoThe first section applies to positive values
    // and zeros, and the second section applies to negative values. If the number
    // to be formatted is negative, but becomes zero after rounding according to
    // the format in the second section, then the resulting zero is formatted
    // according to the first section.
    //
    // ThreeThe first section applies to positive
    // values, the second section applies to negative values, and the third section
    // applies to zeros. The second section may be left empty (by having no
    // characters between the semicolons), in which case the first section applies
    // to all non-zero values. If the number to be formatted is non-zero, but
    // becomes zero after rounding according to the format in the first or second
    // section, then the resulting zero is formatted according to the third
    // section.
    //
    //
    //
    // For both standard and user-defined formatting operations on values of type
    // float and double, if the value being formatted is a NaN (Not
    // a Number) or a positive or negative infinity, then regardless of the format
    // string, the resulting string is given by the NaNSymbol,
    // PositiveInfinitySymbol, or NegativeInfinitySymbol property of
    // the NumberFormatInfo used to format the number.
    //
    // Parsing
    //
    // The Parse methods provided by the numeric classes are all of the form
    //
    //  public static XXX Parse(String s);
    //  public static XXX Parse(String s, int style);
    //
    // where XXX is the name of the particular numeric class. The methods convert a
    // string to a numeric value. The optional style parameter specifies the
    // permitted style of the numeric string. It must be a combination of bit flags
    // from the NumberStyles enumeration. The optional info parameter
    // specifies the NumberFormatInfo instance to use when parsing the
    // string. If the info parameter is null or omitted, the numeric
    // formatting information is obtained from the current culture.
    //
    // Numeric strings produced by the Format methods using the
    // Decimal, Engineering, Fixed point, General, or Number standard formats
    // (the C, D, E, F, G, and N format specifiers) are guaranteed to be parsable
    // by the Parse methods if the NumberStyles.Any style is
    // specified. Note, however, that the Parse methods do not accept
    // NaNs or Infinities.
    //

    [AccessedByRuntime("functions defined in Number.cpp")]
    internal class Number
    {
        private Number() {
        }

/*
        private Number(ref Decimal value) {
            this.precision = DecimalPrecision;
            this.negative = value.negative;
            int index = NumberMaxDigits;
            while (value.mid32 != 0 || value.hi32 != 0) {
                Int32ToDecChars(this.digits, ref index, DecDivMod1E9(ref value), 9);
            }
            Int32ToDecChars(this.digits, ref index, value.lo32, 0);
            int digitCount = NumberMaxDigits - index;
            this.scale = digitCount - value.scale;
            int destIndex = 0;
            while (digitCount > 0) {
                this.digits[destIndex] = this.digits[index];
                destIndex++;
                index++;
                digitCount--;
            }
            this.digits[destIndex] = '\0';
        }
*/

        private Number(int value) {
            this.precision = INT32_PRECISION;
            if (value >= 0) {
                this.negative = false;
            }
            else {
                this.negative = true;
                value = -value;
            }
            int index = INT32_PRECISION;
            Int32ToDecChars(this.digits, ref index, unchecked((uint) value), 0);
            int digitCount = INT32_PRECISION - index;
            int destIndex = 0;
            this.scale = digitCount;
            while (digitCount > 0) {
                this.digits[destIndex] = this.digits[index];
                destIndex++;
                index++;
                digitCount--;
            }
            this.digits[destIndex] = '\0';
        }

        private Number(uint value)
        {
            this.precision = INT32_PRECISION;
            this.negative = false;
            int index = INT32_PRECISION;
            Int32ToDecChars(this.digits, ref index, value, 0);
            int digitCount = INT32_PRECISION - index;
            int destIndex = 0;
            this.scale = digitCount;
            while (digitCount > 0) {
                this.digits[destIndex] = this.digits[index];
                destIndex++;
                index++;
                digitCount--;
            }
            this.digits[destIndex] = '\0';
        }

/*
        private Number(long value) {
            this.precision = INT64_PRECISION;
            if (value >= 0) {
                this.negative = false;
            }
            else {
                this.negative = true;
                value = -value;
            }
            int index = INT64_PRECISION;
            Int64ToDecChars(this.digits, ref index, unchecked((ulong) value), 0);
            int digitCount = INT64_PRECISION - index;
            int destIndex = 0;
            this.scale = digitCount;
            while (digitCount > 0) {
                this.digits[destIndex] = this.digits[index];
                destIndex++;
                index++;
                digitCount--;
            }
            this.digits[destIndex] = '\0';
        }

        private Number(ulong value) {
            this.precision = INT64_PRECISION;
            this.negative = false;
            int index = INT64_PRECISION;
            Int64ToDecChars(this.digits, ref index, value, 0);
            int digitCount = INT64_PRECISION - index;
            int destIndex = 0;
            this.scale = digitCount;
            while (digitCount > 0) {
                this.digits[destIndex] = this.digits[index];
                destIndex++;
                index++;
                digitCount--;
            }
            this.digits[destIndex] = '\0';
        }
*/

        // inline this!!!
        private static bool EndString(String s, int p) {
            return p==s.Length || s[p] == '\0';
        }

        // inline void AddStringRef(wchar** ppBuffer, STRINGREF strRef)
        private static int AddStringRef(char[] ppBuffer, int index,
                                        String strRef) {
            int length = strRef.Length;
            for (int str = 0; str < length; index++, str++) {
                ppBuffer[index] = strRef[str];
            }
            return index;
        }

        // See also Lightning\Src\VM\COMNumber.cpp::
        // wchar* MatchChars(wchar* p, wchar* str)
        // will now return -1 instead of NULL on failure
        private static int MatchChars(String str1, int p, String str) {
            int str_i=0;
            if (EndString(str,str_i)) return -1;
            for (; !EndString(str,str_i); p++, str_i++) {
                if (str1[p] != str[str_i]) //We only hurt the failure case
                {
                    if ((str[str_i] == 0xA0) && (str1[p] == 0x20))
                        // This fix is for French or Kazakh cultures.
                        // Since a user cannot type 0xA0 as a space
                        // character we use 0x20 space character
                        // instead to mean the same.
                        continue;
                    return -1;
                }
            }
            return p;
        }

        // REVIEW: why is this the only thing that is hardcoded
        // anywhere in the system?
        private bool ISWHITE(char ch) {
            return (((ch) == 0x20)||((ch) >= 0x09 && (ch) <= 0x0D));
        }

        private const int STATE_SIGN     = 0x0001;
        private const int STATE_PARENS   = 0x0002;
        private const int STATE_DIGITS   = 0x0004;
        private const int STATE_NONZERO  = 0x0008;
        private const int STATE_DECIMAL  = 0x0010;
        private const int STATE_HEXLEAD  = 0x0020;

        // #defines in Lightning\Src\VM\COMNumber.cpp
        private const int NUMBER_MAXDIGITS = 31;
        private const int INT32_PRECISION = 10;
        private const int UINT32_PRECISION = 10;
        private const int INT64_PRECISION = 20;
        private const int UINT64_PRECISION = 20;
        private const int FLOAT_PRECISION = 7;
        private const int DOUBLE_PRECISION = 15;
        private const int MIN_BUFFER_SIZE = 105;
        private const int SCALE_NAN = unchecked((int)0x80000000);
        private const int SCALE_INF = 0x7FFFFFFF;

        private static String[] posPercentFormats = {
            "# %", "#%", "%#"
        };

        // BUGBUG yslin: have to verify on the negative Percent
        // format for real format.
        private static String[] negPercentFormats = {
            "-# %", "-#%", "-%#"
        };
        private static String[] negNumberFormats = {
            "(#)", "-#", "- #", "#-", "# -"
        };
        private static String posNumberFormat = "#";

        [AccessedByRuntime("defined in Number.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1024)]
        private static extern bool ecvt(double value,
                                        int digits,
                                        char[] buf,
                                        out int decimalpoint,
                                        out bool negative);

        // See also Lightning\Src\VM\COMNumber.cpp::
        //  void DoubleToNumber(double value, int precision, NUMBER* number)
        private Number(double value, int precision) {
            this.precision = precision;
            ecvt(value, precision, digits, out this.scale, out this.negative);
        }

        // code below depends on seeing the null terminator...
        private static char Get(String str, int i) {
            return i<str.Length ? str[i] : '\0';
        }

        // See also Lightning\Src\VM\COMNumber.cpp::
        //  int ParseNumber(wchar** str, int options,
        //                  NUMBER* number, NUMFMTREF numfmt)
        // clr behavior: return nonzero on failure and update *str
        // new behavior: return false iff broken (error or *str != \0 at end)
        private bool ParseNumber(String str, NumberStyles style) {
            this.scale = 0;
            this.negative = false;
            String decSep = NumberFormatInfo.numberDecimalSeparator;
            String groupSep = NumberFormatInfo.numberGroupSeparator;

            int state = 0;
            bool signflag = false; // Cache the results of
            // "style & NumberStyles.AllowLeadingSign &&
            // !(state & STATE_SIGN)"
            // to avoid doing this twice
            int p = 0;
            int next;

            if ((style & NumberStyles.AllowHexSpecifier) != 0 &&
                str.Length >= 2) {
                if (str[0] == '0' && (str[1] == 'x' || str[1] == 'X')) {
                    p = 2;
                }
            }

            char ch = Get(str, p);

            while (true) {
                //Eat whitespace unless we've found a sign.
                if (ISWHITE(ch)
                    && ((style & NumberStyles.AllowLeadingWhite) != 0)
                    && (!((state & STATE_SIGN) != 0) ||
                        (((state & STATE_SIGN) != 0) &&
                         (NumberFormatInfo.numberNegativePattern == 2)))) {
                    // Do nothing here. We will increase p at the end of the loop
                }
                else if ((signflag =
                            (((style & NumberStyles.AllowLeadingSign) != 0) &&
                             !((state & STATE_SIGN) != 0))) &&
                           (next = MatchChars(str, p, NumberFormatInfo.positiveSign)) != -1) {
                    state |= STATE_SIGN;
                    p = next - 1;
                }
                else if (signflag &&
                           (next = MatchChars(str, p, NumberFormatInfo.negativeSign)) != -1){
                    state |= STATE_SIGN;
                    this.negative = true;
                    p = next - 1;
                }
                else if (ch == '(' &&
                           ((style & NumberStyles.AllowParentheses) != 0) &&
                           !((state & STATE_SIGN) != 0)) {
                    state |= STATE_SIGN | STATE_PARENS;
                    this.negative = true;
                }
                else {
                    break;
                }
                ch = Get(str, ++p);
            }
            int digCount = 0;
            int digEnd = 0;
            while (true) {
                if ((ch >= '0' && ch <= '9') ||
                    ( ((style & NumberStyles.AllowHexSpecifier) != 0) &&
                      ((ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')))) {
                    state |= STATE_DIGITS;
                    if (ch != '0' || ((state & STATE_NONZERO) != 0)) {
                        if (digCount < NUMBER_MAXDIGITS) {
                            this.digits[digCount++] = ch;
                            if (ch != '0') digEnd = digCount;
                        }
                        if (!((state & STATE_DECIMAL) != 0)) this.scale++;
                        state |= STATE_NONZERO;
                    }
                    else if ((state & STATE_DECIMAL) != 0) this.scale--;
                }
                else if (((style & NumberStyles.AllowDecimalPoint) != 0) &&
                           !((state & STATE_DECIMAL) != 0) &&
                           ((next = MatchChars(str, p, decSep)) != -1)) {
                    state |= STATE_DECIMAL;
                    p = next - 1;
                }
                else if (((style & NumberStyles.AllowThousands) != 0) &&
                           ((state & STATE_DIGITS) != 0) &&
                           !((state & STATE_DECIMAL) != 0) &&
                           ((next = MatchChars(str, p, groupSep)) != -1)) {
                    p = next - 1;
                }
                else {
                    break;
                }
                ch = Get(str, ++p);
            }

            bool negExp = false;
            this.precision = digEnd;
            this.digits[digEnd] = '\0';
            if ((state & STATE_DIGITS) != 0) {
                if ((ch == 'E' || ch == 'e') &&
                    ((style & NumberStyles.AllowExponent) != 0)) {
                    int temp = p;
                    ch = Get(str, ++p);
                    if ((next = MatchChars(str, p, NumberFormatInfo.positiveSign)) != -1) {
                        ch = Get(str, p = next);
                    }
                    else if ((next = MatchChars(str, p, NumberFormatInfo.negativeSign))!= -1) {
                            ch = Get(str, p = next);
                            negExp = true;
                        }
                    if (ch >= '0' && ch <= '9') {
                        int exp = 0;
                        do {
                            exp = exp * 10 + (ch - '0');
                            ch = Get(str, ++p);
                            if (exp > 1000) {
                                exp=9999;
                                while (ch >='0' && ch <='9') {
                                    ch = Get(str, ++p);
                                }
                            }
                        } while (ch >= '0' && ch <= '9');
                        if (negExp) exp = -exp;
                        this.scale += exp;
                    }
                    else {
                        p = temp;
                        ch = Get(str, p);
                    }
                }
                while (true) {
                    if (ISWHITE(ch) &&
                        ((style & NumberStyles.AllowTrailingWhite) != 0)) {
                        // do nothing
                    }
                    else if ((signflag =
                                (((style & NumberStyles.AllowTrailingSign) != 0)
                                 &&
                                 !((state & STATE_SIGN) != 0))) &&
                               (next =
                                MatchChars(str, p, NumberFormatInfo.positiveSign)) != -1) {
                        state |= STATE_SIGN;
                        p = next - 1;
                    }
                    else if (signflag &&
                               (next = MatchChars(str, p,
                                                  NumberFormatInfo.negativeSign)) != -1) {
                        state |= STATE_SIGN;
                        this.negative = true;
                        p = next - 1;
                    }
                    else if (ch == ')' && ((state & STATE_PARENS) != 0)) {
                        state &= ~STATE_PARENS;
                    }
                    else {
                        break;
                    }
                    ch = Get(str, ++p);
                }
                if (!((state & STATE_PARENS) != 0)) {
                    if (!((state & STATE_NONZERO) != 0)) {
                        this.scale = 0;
                        if (!((state & STATE_DECIMAL) != 0)) {
                            this.negative = false;
                        }
                    }
                    // *str = p;
                    // return 1;
                    return EndString(str, p);
                }
            }
            // *str = p;
            // return 0;
            return false;
        }


        // See also Lightning\Src\VM\COMNumber.cpp::
        //void StringToNumber(STRINGREF str, int options,
        //                    NUMBER* number, NUMFMTREF numfmt)
        private Number(String str, NumberStyles style) {
            {
                //THROWSCOMPLUSEXCEPTION();

                if (str == null) {
                    throw new NullReferenceException();
                }

                if (!NumberFormatInfo.validForParseAsNumber) {
                    throw new ArgumentException("Argument_AmbiguousNumberInfo");
                }
                //wchar* p = str->GetBuffer();
                if (!ParseNumber(str, style)) {
                    throw new FormatException("Format_InvalidString");
                }
            }
        }

/*
        public static String FormatDecimal(Decimal value, String format) {
            // See also Lightning\Src\VM\COMNumber.cpp::FormatDecimal
            if (format == null) {
                throw new ArgumentNullException("format");
            }
            Number number = new Number(ref value);
            return FPNumberToString(number, format);
        }
*/

        public static String FormatDouble(double value, String format) {
            // See also Lightning\Src\VM\COMNumber.cpp::FormatDouble

            Number number;
            int digits;
            double dTest;
            char fmt = ParseFormatSpecifier(format, out digits);
            char val = (char) (fmt & 0xFFDF);
            int precision = DOUBLE_PRECISION;
            switch (val) {
              case 'R':
                //In order to give numbers that are both
                //friendly to display and round-trippable, we
                //parse the number using 15 digits and then
                //determine if it round trips to the same value.
                //If it does, we convert that NUMBER to a
                //string, otherwise we reparse using 17 digits
                //and display that.

                number = new Number(value, DOUBLE_PRECISION);

                if (number.scale == SCALE_NAN) {
                    return NumberFormatInfo.nanSymbol;
                }
                if (number.scale == SCALE_INF) {
                    return number.negative ? NumberFormatInfo.negativeInfinitySymbol
                        : NumberFormatInfo.positiveInfinitySymbol;
                }

                NumberToDouble(number, out dTest);

                if (dTest == value) {
                    return number.ToString('G', DOUBLE_PRECISION);
                }

                number = new Number(value, 17);
                return number.ToString('G', 17);

              case 'E':
                // Here we round values less than E14 to 15 digits
                if (digits > 14) {
                    precision = 17;
                }
                break;

              case 'G':
                // Here we round values less than G15 to 15
                // digits, G16 and G17 will not be touched
                if (digits > 15) {
                    precision = 17;
                }
                break;

            }

            number = new Number(value, precision);
            return FPNumberToString(number, format);
        }

        public static String FormatInt32(int value, String format) {
            // See also Lightning\Src\VM\COMNumber.cpp::FormatInt32
            int digits;
            char fmt = ParseFormatSpecifier(format, out digits);
            switch (fmt) {
              case 'g':
              case 'G': {
                  if (digits > 0) break;
                  goto case 'D';
              }
              case 'd':
              case 'D': {
                  return Int32ToDecString(value, digits, NumberFormatInfo.negativeSign);
              }
              case 'x':
              case 'X': {
                  return Int32ToHexString(unchecked((uint) value),
                                          (char) (fmt-('X'-'A'+10)),
                                          digits);
              }
              default: {
                  break;
              }
            }
            Number number = new Number(value);
            if (fmt == 0) {
                return number.ToStringFormat(format);
            }
            else {
                return number.ToString(fmt, digits);
            }
        }

        public static String FormatUInt32(uint value, String format) {
            // See also Lightning\Src\VM\COMNumber.cpp::FormatUInt32
            int digits;
            char fmt = ParseFormatSpecifier(format, out digits);
            switch (fmt) {
              case 'g':
              case 'G': {
                  if (digits > 0) break;
                  goto case 'D';
              }
              case 'd':
              case 'D': {
                  return UInt32ToDecString(value, digits);
              }
              case 'x':
              case 'X': {
                  return Int32ToHexString(value,
                                          (char) (fmt-('X'-'A'+10)),
                                          digits);
              }
              default: {
                  break;
              }
            }
            Number number = new Number(value);
            if (fmt == 0) {
                return number.ToStringFormat(format);
            }
            else {
                return number.ToString(fmt, digits);
            }
        }

        public static String FormatInt64(long value, String format) {
            return Int64ToHexString(unchecked((ulong) value),
                                    (char) ('X'-('X'-'A'+10)),
                                    0);
/*TODO
            int digits;
            char fmt = ParseFormatSpecifier(format, out digits);
            switch (fmt) {
              case 'g':
              case 'G': {
                  if (digits > 0) break;
                  goto case 'D';
              }
              case 'd':
              case 'D': {
                  return Int64ToDecString(value, digits, NumberFormatInfo.negativeSign);
              }
              case 'x':
              case 'X': {
                  return Int64ToHexString(unchecked((ulong) value),
                                          (char) (fmt-('X'-'A'+10)),
                                          digits);
              }
              default: {
                  break;
              }
            }
            Number number = new Number(value);
            if (fmt == 0) {
                return number.ToStringFormat(format);
            }
            else {
                return number.ToString(fmt, digits);
            }
*/
        }

        public static String FormatUInt64(ulong value, String format) {
            return Int64ToHexString(unchecked((ulong) value),
                                    (char) ('X'-('X'-'A'+10)),
                                    0);
/*TODO
            int digits;
            char fmt = ParseFormatSpecifier(format, out digits);
            switch (fmt) {
              case 'g':
              case 'G': {
                  if (digits > 0) break;
                  goto case 'D';
              }
              case 'd':
              case 'D': {
                  return UInt64ToDecString(value, digits);
              }
              case 'x':
              case 'X': {
                  return Int64ToHexString(value, (char) (fmt-('X'-'A'+10)), digits);
              }
              default: {
                  break;
              }
            }
            Number number = new Number(value);
            if (fmt == 0) {
                return number.ToStringFormat(format);
            }
            else {
                return number.ToString(fmt, digits);
            }
*/
        }

        public static String FormatSingle(float value, String format) {
            // See also Lightning\Src\VM\COMNumber.cpp::FormatSingle

            Number number;
            int digits;
            double dTest;
            double argsValue = value;
            char fmt = ParseFormatSpecifier(format, out digits);
            char val = (char) (fmt & 0xFFDF);
            int precision = FLOAT_PRECISION;
            switch (val) {
              case 'R':
                //In order to give numbers that are both
                //friendly to display and round-trippable, we
                //parse the number using 7 digits and then
                //determine if it round trips to the same value.
                //If it does, we convert that NUMBER to a
                //string, otherwise we reparse using 9 digits
                //and display that.

                number = new Number(argsValue, FLOAT_PRECISION);

                if (number.scale == SCALE_NAN) {
                    return NumberFormatInfo.nanSymbol;
                }
                if (number.scale == SCALE_INF) {
                    return number.negative ? NumberFormatInfo.negativeInfinitySymbol
                        : NumberFormatInfo.positiveInfinitySymbol;
                }

                NumberToDouble(number, out dTest);

                // HACK: force restriction to float
                float[] hack = new float[1];
                hack[0] = (float) dTest;
                float fTest = hack[0];

                if (fTest == value) {
                    return number.ToString('G', FLOAT_PRECISION);
                }

                number = new Number(argsValue, 9);
                return number.ToString('G', 9);

              case 'E':
                // Here we round values less than E14 to 15 digits
                if (digits > 6) {
                    precision = 9;
                }
                break;

              case 'G':
                // Here we round values less than G15 to 15
                // digits, G16 and G17 will not be touched
                if (digits > 7) {
                    precision = 9;
                }
                break;
            }

            number = new Number(value, precision);
            return FPNumberToString(number, format);

        }

        public static Decimal ParseDecimal(String s, NumberStyles style) {
            // See also Lightning\Src\VM\COMNumber.cpp::ParseDecimal
            Number number = new Number(s, style);
            Decimal result;
            if (!NumberToDecimal(number, out result)) {
                throw new OverflowException("Overflow_Decimal");
            }
            return result;
        }

        public static double ParseDouble(String s, NumberStyles style) {
            Number number = new Number(s, style);
            double result;
            NumberToDouble(number, out result);
            return result;
        }

        public static int ParseInt32(String s, NumberStyles style) {
            // See also Lightning\Src\VM\COMNumber.cpp::ParseInt32
            Number number = new Number(s, style);
            int result;
            if ((style & NumberStyles.AllowHexSpecifier) != 0) {
                uint temp;
                if (!HexNumberToUInt32(number, out temp)) {
                    throw new OverflowException("Overflow_Int32");
                }
                result = unchecked((int) temp);
            }
            else {
                if (!NumberToInt32(number, out result)) {
                    throw new OverflowException("Overflow_Int32");
                }
            }
            return result;
        }

        public static uint ParseUInt32(String s, NumberStyles style) {
            // See also Lightning\Src\VM\COMNumber.cpp::ParseUInt32
            Number number = new Number(s, style);
            uint result;
            if ((style & NumberStyles.AllowHexSpecifier) != 0) {
                if (!HexNumberToUInt32(number, out result)) {
                    throw new OverflowException("Overflow_UInt32");
                }
            }
            else {
                if (!NumberToUInt32(number, out result)) {
                    throw new OverflowException("Overflow_UInt32");
                }
            }
            return result;
        }

/*
        public static long ParseInt64(String s, NumberStyles style) {
            // See also Lightning\Src\VM\COMNumber.cpp::ParseInt64
            Number number = new Number(s, style);
            long result;
            if ((style & NumberStyles.AllowHexSpecifier) != 0) {
                ulong temp;
                if (!HexNumberToUInt64(number, out temp)) {
                    throw new OverflowException("Overflow_UInt32");
                }
                result = unchecked((long) temp);
            }
            else {
                if (!NumberToInt64(number, out result)) {
                    throw new OverflowException("Overflow_UInt32");
                }
            }
            return result;
        }

        public static ulong ParseUInt64(String s, NumberStyles style) {
            // See also Lightning\Src\VM\COMNumber.cpp::ParseUInt64
            Number number = new Number(s, style);
            ulong result;
            if ((style & NumberStyles.AllowHexSpecifier) != 0) {
                if (!HexNumberToUInt64(number, out result)) {
                    throw new OverflowException("Overflow_UInt32");
                }
            }
            else {
                if (!NumberToUInt64(number, out result)) {
                    throw new OverflowException("Overflow_UInt32");
                }
            }
            return result;
        }
*/

        public static float ParseSingle(String s, NumberStyles style) {
            return (float)ParseDouble(s, style);
        }

        // STRINGREF FPNumberToString(NUMBER* number, STRINGREF str,
        //                            NUMFMTREF numfmt)
        private static String FPNumberToString(Number number, String format) {
            char fmt;
            int digits;
            if (number.scale == SCALE_NAN) {
                return NumberFormatInfo.nanSymbol;
            }
            if (number.scale == SCALE_INF) {
                return number.negative ? NumberFormatInfo.negativeInfinitySymbol
                    : NumberFormatInfo.positiveInfinitySymbol;
            }

            fmt = ParseFormatSpecifier(format, out digits);
            if (fmt != 0) {
                return number.ToString(fmt, digits);
            }
            return number.ToStringFormat(format);
        }

        // STRINGREF NumberToString(NUMBER* number, wchar format,
        //                          int digits, NUMFMTREF numfmt)
        private String ToString(char format, int digits) {
            long newBufferLen = MIN_BUFFER_SIZE;

            //CQuickBytesSpecifySize<LARGE_BUFFER_SIZE * sizeof(WCHAR)> buf;

            char[] buffer = null;
            int dst; // wchar* dst = NULL;
            char ftype = (char) (format & 0xFFDF);
            int digCount = 0;

            switch (ftype) {
              case 'F':
                if (digits < 0) digits = NumberFormatInfo.numberDecimalDigits;

                if (this.scale < 0)
                    digCount = 0;
                else
                    digCount = this.scale + digits;

                newBufferLen += digCount;

                // For number and exponent
                newBufferLen += NumberFormatInfo.negativeSign.Length;

                newBufferLen += NumberFormatInfo.numberDecimalSeparator.Length;

                //newBufferLen = newBufferLen * sizeof(WCHAR);
                //_ASSERTE(newBufferLen >= MIN_BUFFER_SIZE * sizeof(WCHAR));
                buffer = new char[newBufferLen];
                //if (!buffer)
                //    COMPlusThrowOM();
                dst = 0; // buffer;

                RoundNumber(this.scale + digits);
                if (this.negative) {
                    dst = AddStringRef(buffer, dst, NumberFormatInfo.negativeSign);
                }
                dst = FormatFixed(buffer, dst, digits, null,
                                  NumberFormatInfo.numberDecimalSeparator, null);
                break;
              case 'N':
                // Since we are using digits in our calculation
                if (digits < 0) digits = NumberFormatInfo.numberDecimalDigits;

                if (this.scale < 0)
                    digCount = 0;
                else
                    digCount = this.scale + digits;

                newBufferLen += digCount;

                // For number and exponent
                newBufferLen += NumberFormatInfo.negativeSign.Length;

                // For all the grouping sizes
                newBufferLen += NumberFormatInfo.numberGroupSeparator.Length * digCount;
                newBufferLen += NumberFormatInfo.numberDecimalSeparator.Length;

                //newBufferLen = newBufferLen * sizeof(WCHAR);
                //_ASSERTE(newBufferLen >= MIN_BUFFER_SIZE * sizeof(WCHAR));
                buffer = new char[newBufferLen];
                //if (!buffer)
                //    COMPlusThrowOM();
                dst = 0; // buffer;

                RoundNumber(this.scale + digits);
                dst = FormatNumber(buffer, dst, digits);
                break;
              case 'E':
                if (digits < 0) digits = 6;
                digits++;

                newBufferLen += digits;

                // For number and exponent
                newBufferLen += (NumberFormatInfo.negativeSign.Length +
                                 NumberFormatInfo.positiveSign.Length) * 2;
                newBufferLen += NumberFormatInfo.numberDecimalSeparator.Length;

                //newBufferLen = newBufferLen * sizeof(WCHAR);
                //_ASSERTE(newBufferLen >= MIN_BUFFER_SIZE * sizeof(WCHAR));
                buffer = new char[newBufferLen];
                //if (!buffer)
                //    COMPlusThrowOM();
                dst = 0;  // buffer;

                RoundNumber(digits);
                if (this.negative) {
                    dst = AddStringRef(buffer, dst, NumberFormatInfo.negativeSign);
                }
                dst = FormatScientific(buffer, dst, digits, format);
                break;
              case 'G':
                if (digits < 1) digits = this.precision;
                newBufferLen += digits;

                // For number and exponent
                newBufferLen += (NumberFormatInfo.negativeSign.Length +
                                 NumberFormatInfo.positiveSign.Length) *2;
                newBufferLen += NumberFormatInfo.numberDecimalSeparator.Length;

                //newBufferLen = newBufferLen * sizeof(WCHAR);
                //_ASSERTE(newBufferLen >= MIN_BUFFER_SIZE * sizeof(WCHAR));
                buffer = new char[newBufferLen];
                //if (!buffer)
                //    COMPlusThrowOM();
                dst = 0;  // buffer;

                RoundNumber(digits);
                if (this.negative) {
                    dst = AddStringRef(buffer, dst, NumberFormatInfo.negativeSign);
                }
                dst = FormatGeneral(buffer, dst, digits,
                                    (char) (format - ('G' - 'E')));
                break;
              case 'P':
                if (digits < 0) digits = NumberFormatInfo.percentDecimalDigits;
                this.scale += 2;

                if (this.scale < 0)
                    digCount = 0;
                else
                    digCount = this.scale + digits;

                newBufferLen += digCount;

                // For number and exponent
                newBufferLen += NumberFormatInfo.negativeSign.Length;

                // For all the grouping sizes
                newBufferLen += NumberFormatInfo.percentGroupSeparator.Length * digCount;
                newBufferLen += NumberFormatInfo.percentDecimalSeparator.Length;
                newBufferLen += NumberFormatInfo.percentSymbol.Length;

                //newBufferLen = newBufferLen * sizeof(WCHAR);
                //_ASSERTE(newBufferLen >= MIN_BUFFER_SIZE * sizeof(WCHAR));
                buffer = new char[newBufferLen];
                //if (!buffer)
                //    COMPlusThrowOM();
                dst = 0;  // buffer;

                RoundNumber(this.scale + digits);
                dst = FormatPercent(buffer, dst, digits);
                break;
              default:
                  throw new FormatException("Format_BadFormatSpecifier");
                // COMPlusThrow(kFormatException,L"Format_BadFormatSpecifier");
            }
            //_ASSERTE((dst - buffer >= 0) && (dst - buffer) <= newBufferLen);
            return String.StringCTOR(buffer, 0, dst);
        }

        private static bool NumberToDecimal(Number number, out Decimal value) {
            throw new Exception("System.Number.NumberToDecimal not implemented in Bartok!");
        }

        [AccessedByRuntime("defined in Number.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1024)]
        private static extern double atof(byte[] s);

        private static void NumberToDouble(Number number, out double value) {
            if (number.digits[0] != 0) {
                byte[] buffer = new byte[64];
                int index = 0;
                char[] src = number.digits;
                if (number.negative) buffer[index++] = (byte) '-';
                for (int j = 0; j < src.Length; j++) {
                    if (src[j] == '\0') {
                        break;
                    }
                    else {
                        buffer[index++] = (byte) src[j];
                    }
                }
                int i = number.scale - number.precision;
                if (i != 0) {
                    buffer[index++] = (byte) 'e';
                    if (i < 0) {
                        buffer[index++] = (byte) '-';
                        i = -i;
                    }
                    if (i >= 100) {
                        if (i > 999) i = 999;
                        buffer[index++] = (byte) (i / 100 + (int) '0');
                        i %= 100;
                    }
                    buffer[index++] = (byte) (i / 10 + (int) '0');
                    buffer[index++] = (byte) (i % 10 + (int) '0');
                }
                buffer[index] = (byte)'\0';
                value = atof(buffer);
            }
            else {
                value = 0;
            }

        }

        // int NumberToInt32(NUMBER* number, int* value)
        // Returns 1 (true) on success, 0 (false) for fail.
        private static bool NumberToInt32(Number number, out int value) {
            // See also Lightning\Src\VM\COMNumber.cpp::NumberToInt32
            int i = number.scale;
            if (i > INT32_PRECISION || i < number.precision) goto broken;
            char[] c = number.digits;
            int p = 0;
            int n = 0;
            while (--i >= 0) {
                if ((uint)n > (0x7FFFFFFF / 10)) goto broken;
                n *= 10;
                if (c[p] != '\0') n += c[p++] - '0';
            }
            if (number.negative) {
                n = -n;
                if (n > 0) goto broken;
            }
            else {
                if (n < 0) goto broken;
            }
            value = n;
            return true;

          broken:
            value = 0;
            return false;
        }

        private static bool NumberToUInt32(Number number, out uint value) {
            // See also Lightning\Src\VM\COMNumber.cpp::NumberToInt32
            int i = number.scale;
            if (i > UINT32_PRECISION || i < number.precision) goto broken;
            if (number.negative) goto broken;
            char[] c = number.digits;
            int p = 0;
            uint n = 0;
            while (--i >= 0) {
                if ((uint)n > (0xFFFFFFFF / 10)) goto broken;
                n *= 10;
                if (c[p] != '\0') n += (uint)(c[p++] - '0');
            }
            value = n;
            return true;

          broken:
            value = 0;
            return false;
        }

/*
        private static bool NumberToInt64(Number number, out long value) {
            // See also Lightning\Src\VM\COMNumber.cpp::NumberToInt32
            int i = number.scale;
            if (i > UINT64_PRECISION || i < number.precision) goto broken;
            char[] c = number.digits;
            int p = 0;
            long n = 0;
            while (--i >= 0) {
                if ((ulong)n > (0x7FFFFFFFFFFFFFFF / 10)) goto broken;
                n *= 10;
                if (c[p] != '\0') n += c[p++] - '0';
            }
            if (number.negative) {
                n = -n;
                if (n > 0) goto broken;
            }
            else {
                if (n < 0) goto broken;
            }
            value = n;
            return true;

          broken:
            value = 0;
            return false;
        }

        private static bool NumberToUInt64(Number number, out ulong value)
        {
            // See also Lightning\Src\VM\COMNumber.cpp::NumberToInt32
            int i = number.scale;
            if (i > INT64_PRECISION || i < number.precision) goto broken;
            if (number.negative) goto broken;
            char[] c = number.digits;
            int p = 0;
            ulong n = 0;
            while (--i >= 0) {
                if ((ulong)n > (0xFFFFFFFFFFFFFFFF / 10)) goto broken;
                n *= 10;
                if (c[p] != '\0') n += (ulong)(c[p++] - '0');
            }
            value = n;
            return true;

          broken:
            value = 0;
            return false;
        }
*/

        private static bool HexNumberToUInt32(Number number, out uint value)
        {
            // See also Lightning\Src\VM\COMNumber.cpp::HexNumberToInt32
            int i = number.scale;
            if (i > UINT32_PRECISION || i < number.precision) {
                goto broken;
            }
            if (number.negative) {
                goto broken;
            }
            char[] c = number.digits;
            int p = 0;
            uint n = 0;
            while (--i >= 0) {
                if ((uint)n > (0xFFFFFFFF / 16)) {
                    goto broken;
                }
                n *= 16;
                if (c[p] >= '0' && c[p] <= '9') {
                    n += (uint)(c[p++] - '0');
                }
                else if (c[p] >= 'a' && c[p] <= 'f') {
                    n += 10 + (uint)(c[p++] - 'a');
                }
                else if (c[p] >= 'A' && c[p] <= 'F') {
                    n += 10 + (uint)(c[p++] - 'A');
                }
            }
            value = n;
            return true;

          broken:
            value = 0;
            return false;
        }

/*
        private static bool HexNumberToUInt64(Number number, out ulong value) {
            // See also Lightning\Src\VM\COMNumber.cpp::HexNumberToInt32
            int i = number.scale;
            if (i > INT64_PRECISION || i < number.precision) {
                goto broken;
            }
            if (number.negative) {
                goto broken;
            }
            char[] c = number.digits;
            int p = 0;
            ulong n = 0;
            while (--i >= 0) {
                if ((ulong)n > (0xFFFFFFFFFFFFFFFF / 16)) {
                    goto broken;
                }
                n *= 16;
                if (c[p] >= '0' && c[p] <= '9') {
                    n += (uint)(c[p++] - '0');
                }
                else if (c[p] >= 'a' && c[p] <= 'f') {
                    n += 10 + (uint)(c[p++] - 'a');
                }
                else if (c[p] >= 'A' && c[p] <= 'F') {
                    n += 10 + (uint)(c[p++] - 'A');
                }
            }
            value = n;
            return true;

          broken:
            value = 0;
            return false;
        }
*/

        private static char ParseFormatSpecifier(string format, out int digits)
        {
            if (format != null) {
                int index = 0;
                char c = Get(format, index);
                if (c != 0) {
                    if (c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z') {
                        index++;
                        int n = -1;
                        c = Get(format, index);
                        if (c >= '0' && c <= '9') {
                            n = (c - '0');
                            index++;
                            c = Get(format, index);
                            while (c >= '0' && c <= '9') {
                                n = n * 10 + (c - '0');
                                index++;
                                c = Get(format, index);
                                if (n >= 10) break;
                            }
                        }
                        if (c == 0) {
                            digits = n;
                            return Get(format, 0);
                        }
                    }
                    digits = -1;
                    return '\0';
                }
            }
            digits = -1;
            return 'G';
        }

        // See also Lightning\Src\VM\COMNumber.cpp::NumberToStringFormat
        private String ToStringFormat(String format) {
            int thousandCount = 0;
            int section = (this.digits[0] == 0 ? 2 : (this.negative ? 1 : 0));
            int sectionOffset = FindSection(format, section);
            int firstDigit;
            int lastDigit;
            bool scientific;
            int decimalPos;
            int src;
            int percent;
            int permille;
            int thousandSeps;
            char ch;
            while (true) {
                int digitCount = 0;
                decimalPos = -1;
                firstDigit = 0x7FFFFFFF;
                lastDigit = 0;
                scientific = false;
                percent = 0;
                permille = 0;
                int thousandPos = -1;
                thousandSeps = 0;
                int scaleAdjust = 0;
                src = sectionOffset;
                ch = Get(format, src);
                src++;
                while (ch != '\0' && ch != ';') {
                    switch (ch) {
                      case '#':
                        digitCount++;
                        break;
                      case '0':
                        if (firstDigit == 0x7FFFFFFF) {
                            firstDigit = digitCount;
                        }
                        digitCount++;
                        lastDigit = digitCount;
                        break;
                      case '.':
                        if (decimalPos < 0) {
                            decimalPos = digitCount;
                        }
                        break;
                      case ',':
                        if (digitCount > 0 && decimalPos < 0) {
                            if (thousandPos >= 0) {
                                if (thousandPos == digitCount) {
                                    thousandCount++;
                                    break;
                                }
                                thousandSeps = 1;
                            }
                            thousandPos = digitCount;
                            thousandCount = 1;
                        }
                        break;
                      case '%':
                        percent++;
                        scaleAdjust += 2;
                        break;
                      case '\u2030':
                        permille++;
                        scaleAdjust += 3;
                        break;
                      case '\'':
                      case '"':
                        while (Get(format, src) != 0 &&
                               Get(format, src) != ch) {
                            src++;
                        }
                        break;
                      case '\\':
                        if (Get(format, src) != 0) {
                            src++;
                        }
                        break;
                      case 'E':
                        if (Get(format, src) == '0' ||
                            ((Get(format, src) == '+' ||
                              Get(format, src) == '-') &&
                             Get(format, src+1) == '0')) {
                            do {
                                src++;
                            } while (Get(format, src) != 0);
                            scientific = true;
                        }
                        break;
                    }
                    ch = Get(format, src);
                    src++;
                }
                if (decimalPos < 0) {
                    decimalPos = digitCount;
                }
                if (thousandPos >= 0) {
                    if (thousandPos == decimalPos) {
                        scaleAdjust -= thousandCount * 3;
                    }
                    else {
                        thousandSeps = 1;
                    }
                }
                if (this.digits[0] != 0) {
                    this.scale += scaleAdjust;
                    int pos = (scientific ?
                               digitCount :
                               (this.scale + digitCount - decimalPos));
                    this.RoundNumber(pos);
                    if (this.digits[0] == 0) {
                        src = FindSection(format, 2);
                        if (src != sectionOffset) {
                            sectionOffset = src;
                            continue;
                        }
                    }
                }
                else {
                    this.negative = false;
                }
                break;
            }
            firstDigit = (firstDigit < decimalPos) ? decimalPos - firstDigit : 0;
            lastDigit = (lastDigit > decimalPos) ? decimalPos - lastDigit : 0;
            int digPos;
            int adjust;
            if (scientific) {
                digPos = decimalPos;
                adjust = 0;
            }
            else {
                digPos = (this.scale > decimalPos) ? this.scale : decimalPos;
                adjust = this.scale - decimalPos;
            }
            src = sectionOffset;
            ulong maxStrIncLen = unchecked((ulong) (this.negative ?
                                                    NumberFormatInfo.negativeSign.Length :
                                                    NumberFormatInfo.positiveSign.Length));
            maxStrIncLen += (uint) NumberFormatInfo.numberDecimalSeparator.Length;
            if (scientific) {
                int inc1 = NumberFormatInfo.positiveSign.Length;
                int inc2 = NumberFormatInfo.negativeSign.Length;
                maxStrIncLen += (uint) ((inc1 > inc2) ? inc1 : inc2);
            }
            if (percent > 0) {
                maxStrIncLen += (ulong) ((NumberFormatInfo.percentSymbol.Length) * percent);
            }
            if (permille > 0) {
                maxStrIncLen += (ulong) ((NumberFormatInfo.perMilleSymbol.Length) * permille);
            }
            ulong adjustLength = (adjust > 0) ? (uint) adjust : 0U;
            int bufferLength = 125;
            int[] thousandSepPos = null;
            int thousandSepCtr = -1;
            if (thousandSeps != 0) {
                int groupSizeLen = NumberFormatInfo.numberGroupSizes.Length;
                if (groupSizeLen == 0) {
                    thousandSeps = 0;
                }
                else {
                    thousandSepPos = new int[bufferLength];
                    long groupTotalSizeCount = NumberFormatInfo.numberGroupSizes[0];
                    int groupSizeIndex = 0;
                    int groupSize = (int) groupTotalSizeCount;
                    int totalDigits = digPos + ((adjust < 0) ? adjust : 0);
                    int numDigits =
                        (firstDigit > totalDigits) ? firstDigit : totalDigits;
                    while (numDigits > groupTotalSizeCount) {
                        if (groupSize == 0) {
                            break;
                        }
                        thousandSepCtr++;
                        thousandSepPos[thousandSepCtr] = (int) groupTotalSizeCount;
                        if (groupSizeIndex < groupSizeLen - 1) {
                            groupSizeIndex++;
                            groupSize = NumberFormatInfo.numberGroupSizes[groupSizeIndex];
                        }
                        groupTotalSizeCount += groupSize;
                        if (bufferLength - thousandSepCtr < 10) {
                            bufferLength *= 2;
                            int[] oldThousandSepPos = thousandSepPos;
                            thousandSepPos = new int[bufferLength];
                            for (int i = 0; i < thousandSepCtr; i++) {
                                thousandSepPos[i] = oldThousandSepPos[i];
                            }
                        }
                    }
                    adjustLength += (ulong) ((thousandSepCtr + 1) * NumberFormatInfo.numberGroupSeparator.Length);
                }
            }
            maxStrIncLen += adjustLength;
            ulong tempLen = ((ulong) format.Length + maxStrIncLen + 10U);
            if (tempLen > 0x7FFFFFFF) {
                throw new OutOfMemoryException("Cannot create a formatted string that big!");
            }
            uint bufferLen = (uint) tempLen;
            if (bufferLen < 250) {
                bufferLen = 250;
            }
            int bufferIndex = 0;
            char[] buffer = new char[bufferLen];
            int dst = 0;
            if (this.negative && sectionOffset == 0) {
                bufferIndex =
                    AddStringRef(buffer, bufferIndex, NumberFormatInfo.negativeSign);
            }
            ch = Get(format, src);
            src++;
            int digitOffset = 0;
            while (ch != 0 && ch != ';') {
                if (bufferLength - dst < 10) {
                    bufferLen *= 2;
                    char[] oldBuffer = buffer;
                    buffer = new char[bufferLen];
                    for (int i = 0; i < dst; i++) {
                        buffer[i] = oldBuffer[i];
                    }
                }
                switch (ch) {
                  case '#':
                  case '0': {
                      while (adjust > 0) {
                          buffer[dst] = ((this.digits[digitOffset] != 0) ?
                                         this.digits[digitOffset++] :
                                         '0');
                          dst++;
                          if (thousandSeps != 0 &&
                              digPos > 1 &&
                              thousandSepCtr >= 0) {
                              if (digPos == thousandSepPos[thousandSepCtr] + 1) {
                                  dst = AddStringRef(buffer, dst, NumberFormatInfo.numberGroupSeparator);
                                  thousandSepCtr--;
                              }
                          }
                          digPos--;
                          adjust--;
                      }
                      if (adjust < 0) {
                          adjust++;
                          ch = (digPos <= firstDigit) ? '0' : '\0';
                      }
                      else {
                          ch = ((this.digits[digitOffset] != 0) ?
                                this.digits[digitOffset++] :
                                ((digPos > lastDigit) ? '0' : '\0'));
                      }
                      if (ch != 0) {
                          if (digPos == 0) {
                              dst = AddStringRef(buffer, dst, NumberFormatInfo.numberDecimalSeparator);
                          }
                          buffer[dst] = ch;
                          dst++;
                          if (thousandSeps != 0 &&
                              digPos > 1 &&
                              thousandSepCtr >= 0) {
                              if (digPos == thousandSepPos[thousandSepCtr] + 1) {
                                  dst = AddStringRef(buffer, dst, NumberFormatInfo.numberGroupSeparator);
                                  thousandSepCtr--;
                              }
                          }
                      }
                      digPos--;
                      break;
                  }
                  case '.':
                    break;
                  case '\u2030':
                    dst = AddStringRef(buffer, dst, NumberFormatInfo.perMilleSymbol);
                    break;
                  case '%':
                    dst = AddStringRef(buffer, dst, NumberFormatInfo.percentSymbol);
                    break;
                  case ',':
                    break;
                  case '\'':
                  case '"':
                    while (Get(format, src) != 0 && Get(format, src) != ch) {
                        buffer[dst] = Get(format, src);
                        dst++;
                        src++;
                        if (dst == bufferLen - 1) {
                            if ((ulong) (bufferLen - dst) < maxStrIncLen) {
                                bufferLen *= 2;
                                char[] oldBuffer = buffer;
                                buffer = new char[bufferLen];
                                for (int i = 0; i < dst; i++) {
                                    buffer[i] = oldBuffer[i];
                                }
                            }
                        }
                    }
                    if (Get(format, src) != 0) {
                        src++;
                    }
                    break;
                  case '\\':
                    if (Get(format, src) != 0) {
                        buffer[dst] = Get(format, src);
                        dst++;
                        src++;
                    }
                    break;
                  case 'E':
                  case 'e': {
                      String sign = null;
                      int i = 0;
                      if (scientific) {
                          if (Get(format, src) == '0') {
                              i++;
                          }
                          else if (Get(format, src) == '+' &&
                                     Get(format, src+1) == '0') {
                              sign = NumberFormatInfo.positiveSign;
                          }
                          else if (Get(format, src) == '-' &&
                                     Get(format, src+1) == '0') {
                              // Do nothing
                          }
                          else {
                              buffer[dst] = ch;
                              dst++;
                              break;
                          }
                          while (Get(format, ++src) == '0') {
                              i++;
                          }
                          if (i > 10) {
                              i = 10;
                          }
                          int exp = ((this.digits[0] == 0) ?
                                     0 :
                                     (this.scale - decimalPos));
                          dst = FormatExponent(buffer, dst, exp, ch, sign, NumberFormatInfo.negativeSign, i);
                          scientific = false;
                      }
                      else {
                          buffer[dst] = ch;
                          dst++;
                          if (Get(format, src) == '+' || Get(format, src) == '-') {
                              buffer[dst] = Get(format, src);
                              dst++;
                              src++;
                          }
                          while (Get(format, src) != 0) {
                              buffer[dst] = Get(format, src);
                              dst++;
                              src++;
                          }
                      }
                      break;
                  }
                  default:
                    buffer[dst] = ch;
                    dst++;
                    break;
                }
                ch = Get(format, src);
                src++;
            }
            return String.StringCTOR(buffer, 0, dst);
        }

        private static int FindSection(String format, int section) {
            if (section == 0) {
                return 0;
            }
            int src = 0;
            while (true) {
                char ch = Get(format, src);
                src++;
                switch (ch) {
                  case '\'':
                  case '"':
                    while (Get(format, src) != '\0' && Get(format, src) != ch) {
                        src++;
                    }
                    break;
                  case '\\':
                    if (Get(format, src) != 0) {
                        src++;
                    }
                    break;
                  case ';':
                    section--;
                    if (section != 0) {
                        break;
                    }
                    if (Get(format, src) != 0 && Get(format, src) != ';') {
                        return src;
                    }
                    return 0;
                  case '\0':
                    return 0;
                }
            }
        }

        // See also Lightning\Src\VM\COMNumber.cpp::
        // STRINGREF Int32ToDecStr(int value, int digits, STRINGREF sNegative)
        private static String Int32ToDecString(int value, int digits, String sign) {
            //THROWSCOMPLUSEXCEPTION();
            //CQuickBytes buf;

            int bufferLength = 100; // was UINT
            int negLength = 0;
            // wchar* src = NULL;
            if (digits < 1) digits = 1;

            if (value < 0) {
                //src = sNegative->GetBuffer();
                negLength = sign.Length;
                if (negLength > 85) {
                    bufferLength = negLength + 15; //was implicit C++ cast
                }
            }

            char[] buffer = new char[bufferLength];
            //if (!buffer)
            //    COMPlusThrowOM();

            int p = bufferLength;
            Int32ToDecChars(buffer, ref p, (uint)(value >= 0? value: -value), digits);
            if (value < 0) {
                for (int i = negLength - 1; i >= 0; i--) {
                    buffer[--p] = sign[i];
                    // *(--p) = *(src+i);
                }
            }

            // _ASSERTE( buffer + bufferLength - p >=0 && buffer <= p);
            return String.StringCTOR(buffer, p, bufferLength-p);
            // return COMString::NewString(p, buffer + bufferLength - p);
        }

        private static String Int32ToHexString(uint value,
                                               char hexBase,
                                               int digits) {
            char[] buffer = new char[100];
            if (digits < 1) {
                digits = 1;
            }
            int start = Int32ToHexChars(buffer, 100, value, hexBase, digits);
            return String.StringCTOR(buffer, start, 100-start);
        }

        private static int Int32ToHexChars(char[] buffer, int offset, uint value,
                                           char hexBase, int digits) {
            while (digits > 0 || value != 0) {
                digits--;
                uint digit = value & 0xf;
                offset--;
                buffer[offset] = (char) (digit + (digit < 10 ? '0' : hexBase));
                value >>= 4;
            }
            return offset;
        }

        private static String UInt32ToDecString(uint value, int digits) {
            int bufferLength = 100;
            if (digits < 1) digits = 1;
            char[] buffer = new char[bufferLength];
            int p = bufferLength;
            Int32ToDecChars(buffer, ref p, value, digits);
            return String.StringCTOR(buffer, p, bufferLength-p);
        }

        // used to be macros
        private static uint LO32(ulong x) { return (uint)(x); }
        private static uint HI32(ulong x) {
            return (uint)((((ulong)x) & 0xFFFFFFFF00000000L) >> 32);
        }

/*
        // See also Lightning\Src\VM\COMNumber.cpp::
        //STRINGREF Int64ToDecStr(__int64 value, int digits, STRINGREF sNegative)
        private static String Int64ToDecString(long value, int digits, String sign) {
            //THROWSCOMPLUSEXCEPTION();
            //CQuickBytes buf;

            if (digits < 1) digits = 1;
            int signNum = (int)HI32(unchecked((ulong)value));
            int bufferLength = 100; // was UINT

            if (signNum < 0) {
                value = -value;
                int negLength = sign.Length;
                if (negLength > 75) {// Since max is 20 digits
                    bufferLength = negLength + 25;
                }
            }

            char[] buffer = new char[bufferLength];
            //if (!buffer)
            //    COMPlusThrowOM();
            int p = bufferLength;
            while (HI32(unchecked((ulong)value)) != 0) {
                uint rem;
                value = (long) Int64DivMod1E9((ulong)value, out rem);
                Int32ToDecChars(buffer, ref p, rem, 9);
                digits -= 9;
            }
            Int32ToDecChars(buffer, ref p, LO32(unchecked((ulong)value)), digits);
            if (signNum < 0) {
                for (int i = sign.Length - 1; i >= 0; i--) {
                    buffer[--p] = sign[i];
                }
            }
            return String.StringCTOR(buffer, p, bufferLength-p);
        }
*/

        private static int Int64ToHexChars(char[] buffer, int offset, ulong value,
                                           char hexBase, int digits) {
            while (digits > 0 || value != 0) {
                digits--;
                uint digit = ((uint)value) & 0xf;
                offset--;
                buffer[offset] = (char) (digit + (digit < 10 ? '0' : hexBase));
                value >>= 4;
            }
            return offset;
        }

        private static String Int64ToHexString(ulong value,
                                               char hexBase,
                                               int digits) {
            char[] buffer = new char[100];
            if (digits < 1) {
                digits = 1;
            }
            int start = Int64ToHexChars(buffer, 100, value, hexBase, digits);
            return String.StringCTOR(buffer, start, 100-start);
        }

/*
        private static String UInt64ToDecString(ulong value, int digits) {
            int bufferLength = 100;
            char[] buffer = new char[bufferLength];
            if (digits < 1) digits = 1;
            int p = bufferLength;
            while (HI32(value) != 0) {
                uint rem;
                value = Int64DivMod1E9(value, out rem);
                Int32ToDecChars(buffer, ref p, rem, 9);
                digits -= 9;
            }
            Int32ToDecChars(buffer, ref p, LO32(value), digits);
            return String.StringCTOR(buffer, p, bufferLength-p);
        }
*/

        // See also Lightning\Src\VM\COMNumber.cpp::
        // wchar* Int32ToDecChars(wchar* p, unsigned int value, int digits)
        // There's a x86 asm version there too.
        private static void Int32ToDecChars(char[] buffer, ref int bufferIndex,
                                            uint value, int digits) {
            while (--digits >= 0 || value != 0) {
                buffer[--bufferIndex] = (char) (value % 10 + '0');
                value /= 10;
            }
        }

/*
        private static void Int64ToDecChars(char[] buffer, ref int bufferIndex,
                                            ulong value, int digits) {
            while (--digits >= 0 || value != 0) {
                buffer[--bufferIndex] = (char) (value % 10 + '0');
                value /= 10;
            }
        }
*/

        // See also Lightning\Src\VM\COMNumber.cpp::
        // void RoundNumber(NUMBER* number, int pos)
        private void RoundNumber(int pos) {
            int i = 0;
            while (i < pos && this.digits[i] != 0) i++;
            if (i == pos && this.digits[i] >= '5') {
                while (i > 0 && this.digits[i - 1] == '9') i--;
                if (i > 0) {
                    this.digits[i - 1]++;
                }
                else {
                    this.scale++;
                    this.digits[0] = '1';
                    i = 1;
                }
            }
            else {
                while (i > 0 && this.digits[i - 1] == '0') i--;
            }
            if (i == 0) {
                this.scale = 0;
                this.negative = false;
            }
            this.digits[i] = '\0';
        }

        // wchar* FormatExponent(wchar* buffer, int value, wchar expChar,
        //                       STRINGREF posSignStr, STRINGREF negSignStr,
        //                       int minDigits)
        private int FormatExponent(char[] buffer, int bufferIndex, int value,
                                   char expChar, String posSignStr,
                                   String negSignStr, int minDigits) {
            char[] digits = new char[11];
            buffer[bufferIndex++] = expChar;
            if (value < 0) {
                bufferIndex = AddStringRef(buffer, bufferIndex, negSignStr);
                value = -value;
            }
            else {
                if (posSignStr != null) {
                    bufferIndex = AddStringRef(buffer, bufferIndex, posSignStr);
                }
            }
            int p = 10;
            // REVIEW: (int) was implicit in C++ code
            Int32ToDecChars(digits, ref p, checked((uint)value), minDigits);
            int i = 10 - p;
            while (--i >= 0) buffer[bufferIndex++] = digits[p++];
            return bufferIndex;
        }

        //wchar* FormatGeneral(wchar* buffer, NUMBER* number, int digits,
        //                     wchar expChar, NUMFMTREF numfmt)
        private int FormatGeneral(char[] buffer, int bufferIndex,
                                  int digits, char expChar) {
            int digPos = this.scale;
            bool scientific = false;
            if (digPos > digits || digPos < -3) {
                digPos = 1;
                scientific = true;
            }
            int dig = 0; // number->digits;
            if (digPos > 0) {
                do {
                    buffer[bufferIndex++] =
                        this.digits[dig] != 0 ? this.digits[dig++] : '0';
                } while (--digPos > 0);
            }
            else {
                buffer[bufferIndex++] = '0';
            }
            if (this.digits[dig] != 0) {
                bufferIndex = AddStringRef(buffer, bufferIndex,
                                           NumberFormatInfo.numberDecimalSeparator);
                while (digPos < 0) {
                    buffer[bufferIndex++] = '0';
                    digPos++;
                }
                do {
                    buffer[bufferIndex++] = this.digits[dig++];
                } while (this.digits[dig] != 0);
            }
            if (scientific) {
                bufferIndex = FormatExponent(buffer, bufferIndex,
                                             this.scale - 1, expChar,
                                             NumberFormatInfo.positiveSign,
                                             NumberFormatInfo.negativeSign, 2);
            }
            return bufferIndex;
        }

        // wchar* FormatScientific(wchar* buffer, NUMBER* number,
        //                         int digits, wchar expChar, NUMFMTREF numfmt)
        private int FormatScientific(char[] buffer, int bufferIndex, int digits,
                                     char expChar) {
            int dig = 0;  // number->digits;
            buffer[bufferIndex++] =
                this.digits[dig] != 0 ? this.digits[dig++] : '0';
            if (digits != 1) {
                // For E0 we would like to suppress the decimal point
                bufferIndex = AddStringRef(buffer, bufferIndex,
                                           NumberFormatInfo.numberDecimalSeparator);
            }
            while (--digits > 0) {
                buffer[bufferIndex++] =
                    this.digits[dig] != 0 ? this.digits[dig++] : '0';
            }
            int e = this.digits[0] == 0 ? 0 : this.scale - 1;
            bufferIndex = FormatExponent(buffer, bufferIndex, e, expChar,
                                         NumberFormatInfo.positiveSign,
                                         NumberFormatInfo.negativeSign,
                                         3);
            return bufferIndex;
        }

        // REVIEW: call the real wcslen?
        private static int wcslen(char[] c, int i) {
            int j;
            for (j = i; j < c.Length; ++j) {
                if (c[j] == '\0') break;
            }
            return j-i;
        }

        // wchar* FormatFixed(wchar* buffer, NUMBER* number, int digits,
        //                    I4ARRAYREF groupDigitsRef, STRINGREF sDecimal,
        //                    STRINGREF sGroup)
        private int FormatFixed(char[] buffer, int bufferIndex, int digits,
                                int[] groupDigits, String sDecimal,
                                String sGroup) {
            //          int bufferSize = 0;   // the length of the result buffer string.
            int digPos = this.scale;
            int dig = 0; // = number->digits;

            if (digPos > 0) {
                if (groupDigits != null) {
                    // index into the groupDigits array.
                    int groupSizeIndex = 0;
                    // the current total of group size.
                    int groupSizeCount = groupDigits[groupSizeIndex];
                    // the length of groupDigits array.
                    int groupSizeLen   = groupDigits.Length;
                    // the length of the result buffer string.
                    int bufferSize     = digPos;
                    // the length of the group separator string.
                    int groupSeparatorLen = sGroup.Length;
                    // the current group size.
                    int groupSize = 0;

                    //
                    // Find out the size of the string buffer for the result.
                    //
                    if (groupSizeLen != 0) // You can pass in 0 length arrays
                    {
                        while (digPos > groupSizeCount) {
                            groupSize = groupDigits[groupSizeIndex];
                            if (groupSize == 0) {
                                break;
                            }

                            bufferSize += groupSeparatorLen;
                            if (groupSizeIndex < groupSizeLen - 1) {
                                groupSizeIndex++;
                            }
                            groupSizeCount += groupDigits[groupSizeIndex];
                            if (groupSizeCount < 0 || bufferSize < 0) {
                                throw new ArgumentOutOfRangeException();
                                // if we overflow
                                //COMPlusThrow(kArgumentOutOfRangeException);
                            }
                        }
                        // If you passed in an array with one
                        // entry as 0, groupSizeCount == 0
                        if (groupSizeCount == 0)
                            groupSize = 0;
                        else
                            groupSize = groupDigits[0];
                    }

                    groupSizeIndex = 0;
                    int digitCount = 0;
                    int digStart;
                    int digLength = (int)wcslen(this.digits, dig);
                    digStart = (digPos<digLength)?digPos:digLength;
                    int p = bufferIndex + bufferSize - 1;
                    // wchar* p = buffer + bufferSize - 1;

                    for (int i = digPos - 1; i >= 0; i--) {
                        buffer[p--] = (i<digStart) ? this.digits[dig+i] : '0';

                        if (groupSize > 0) {
                            digitCount++;
                            if (digitCount == groupSize && i != 0) {
                                for (int j = groupSeparatorLen - 1; j >= 0; j--) {
                                    buffer[p--] = sGroup[j];
                                }

                                if (groupSizeIndex < groupSizeLen - 1) {
                                    groupSizeIndex++;
                                    groupSize = groupDigits[groupSizeIndex];
                                }
                                digitCount = 0;
                            }
                        }
                    }
                    bufferIndex += bufferSize;
                    dig += digStart;
                }
                else {
                    do {
                        buffer[bufferIndex++] =
                            this.digits[dig] != 0 ? this.digits[dig++] : '0';
                    } while (--digPos > 0);
                }
            }
            else {
                buffer[bufferIndex++] = '0';
            }
            if (digits > 0) {
                bufferIndex = AddStringRef(buffer, bufferIndex, sDecimal);
                while (digPos < 0 && digits > 0) {
                    buffer[bufferIndex++] = '0';
                    digPos++;
                    digits--;
                }
                while (digits > 0) {
                    buffer[bufferIndex++] =
                        this.digits[dig] != 0 ? this.digits[dig++] : '0';
                    digits--;
                }
            }
            return bufferIndex;
        }

        // wchar* FormatNumber(wchar* buffer, NUMBER* number,
        //                     int digits, NUMFMTREF numfmt)
        private int FormatNumber(char[] buffer, int bufferIndex,
                                 int digits) {
            char ch;
            String fmt = this.negative ?
                negNumberFormats[NumberFormatInfo.numberNegativePattern] :
                posNumberFormat;
            int fmtIndex = 0;

            for (; fmtIndex < fmt.Length; fmtIndex++) {
                ch = fmt[fmtIndex];
                switch (ch) {
                  case '#':
                    bufferIndex = FormatFixed(buffer, bufferIndex, digits,
                                              NumberFormatInfo.numberGroupSizes,
                                              NumberFormatInfo.numberDecimalSeparator,
                                              NumberFormatInfo.numberGroupSeparator);
                    break;
                  case '-':
                    bufferIndex = AddStringRef(buffer, bufferIndex,
                                               NumberFormatInfo.negativeSign);
                    break;
                  default:
                    buffer[bufferIndex++] = ch;
                    break;
                }
            }
            return bufferIndex;
        }

        // wchar* FormatPercent(wchar* buffer, NUMBER* number,
        //                      int digits, NUMFMTREF numfmt)
        private int FormatPercent(char[] buffer, int bufferIndex,
                                  int digits) {
            char ch;
            String fmt = this.negative ?
                negPercentFormats[NumberFormatInfo.percentNegativePattern] :
                posPercentFormats[NumberFormatInfo.percentPositivePattern];
            int fmtIndex = 0;

            while ((ch = fmt[fmtIndex++]) != 0) {
                switch (ch) {
                  case '#':
                    bufferIndex = FormatFixed(buffer, bufferIndex, digits,
                                              NumberFormatInfo.percentGroupSizes,
                                              NumberFormatInfo.percentDecimalSeparator,
                                              NumberFormatInfo.percentGroupSeparator);
                    break;
                  case '-':
                    bufferIndex = AddStringRef(buffer, bufferIndex,
                                               NumberFormatInfo.negativeSign);
                    break;
                  case '%':
                    bufferIndex = AddStringRef(buffer, bufferIndex,
                                               NumberFormatInfo.percentSymbol);
                    break;
                  default:
                    buffer[bufferIndex++] = ch;
                    break;
                }
            }
            return bufferIndex;
        }

/*
        private uint D32DivMod1E9(uint hi32, uint lo32, out uint newlo32) {
            ulong n = (((ulong) hi32) << 32) | lo32;
            newlo32 = (uint) (n / 1000000000);
            return (uint) (n % 1000000000);
        }

        private uint DecDivMod1E9(ref Decimal value) {
            uint newhi, newmid, newlo;
            uint result = D32DivMod1E9(D32DivMod1E9(D32DivMod1E9(0,
                                                                 value.hi32,
                                                                 out newhi),
                                                    value.mid32,
                                                    out newmid),
                                       value.lo32,
                                       out newlo);
            value.hi32 = newhi;
            value.mid32 = newmid;
            value.lo32 = newlo;
            return result;
        }

        // See also Lightning\Src\VM\COMNumber.cpp::
        // unsigned int Int64DivMod1E9(unsigned __int64* value)
        // There's a x86 asm version there too.
        // The interface is different because Bartok does not support
        // taking the address of 64 bit values.
        private static ulong Int64DivMod1E9(ulong value, out uint rem) {
            rem = (uint)(value % 1000000000);
            value /= 1000000000;
            return value;
        }
*/

        public static bool TryParseDouble(String s, NumberStyles style,out double result) {
            throw new Exception("System.Number.TryParseDouble not implemented in Bartok!");
        }


        private const int DecimalPrecision = 29;
        private const int NumberMaxDigits = 31;

        private int precision;
        private int scale;
        private bool negative;
        private char[] digits = new char[NumberMaxDigits+1];
    }
}
