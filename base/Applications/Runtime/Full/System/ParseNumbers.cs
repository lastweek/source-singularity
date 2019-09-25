// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  ParseNumbers
//
// Purpose: Methods for Parsing numbers and Strings.
// All methods are implemented in native.
//
//===========================================================  
namespace System
{

    using System;
    using System.Runtime.CompilerServices;
    internal class ParseNumbers {
        internal const int PrintAsI1=0x40;
        internal const int PrintAsI2=0x80;
        internal const int PrintAsI4=0x100;
        internal const int TreatAsUnsigned=0x200;
        internal const int TreatAsI1=0x400;
        internal const int TreatAsI2=0x800;
        internal const int IsTight=0x1000;
        internal static readonly int[] ZeroStart = {0};

        //
        // NATIVE METHODS
        // For comments on these methods please see $\src\vm\COMUtilNative.cpp
        //
        public static long StringToLong(System.String s, int radix, int flags) {
            int [] zeroStart = {0};
            return StringToLong(s,radix,flags,zeroStart);
        }

        public static int StringToInt(System.String s, int radix, int flags) {
            int [] zeroStart = {0};
            return StringToInt(s,radix,flags,zeroStart);
        }

        // From Lightning\Src\VM\COMUtilNative.cpp:: enum FmtFlags
        internal const int LeftAlign = 0x1;
        internal const int CenterAlign = 0x2;
        internal const int RightAlign = 0x4;
        internal const int PrefixSpace = 0x8;
        internal const int PrintSign = 0x10;
        internal const int PrintBase = 0x20;
        //internal const int TreatAsUnsigned = 0x10;
        //internal const int PrintAsI1 = 0x40;
        //internal const int PrintAsI2 = 0x80;
        //internal const int PrintAsI4 = 0x100;
        internal const int PrintRadixBase = 0x200;
        internal const int AlternateForm = 0x400;

        internal const int MinRadix=2;
        internal const int MaxRadix=36;

        static private int EatWhiteSpace(String buffer, int length, int i) {
            for (; i < length && Char.IsWhiteSpace(buffer[i]); i++);
            return i;
        }

        static private uint GrabInts(uint radix, String buffer, int length,
                                     ref int i,bool isUnsigned) {
            uint result=0;
            uint value;
            uint maxVal;
#if DEBUG
            if (!(radix == 2 || radix == 8 || radix == 10 || radix == 16)) {
                VTable.DebugBreak();
            }
#endif
            // Allow all non-decimal numbers to set the sign bit.
            if (radix == 10 && !isUnsigned) {
                maxVal = (0x7FFFFFFF / 10);
                while (i < length && IsDigit(buffer[i], radix, out value)) {
                    // Read all of the digits and convert to a number
                    // Check for overflows - this is sufficient & correct.
                    if (result > maxVal || ((int)result) < 0) {
                        throw new OverflowException("Overflow_Int32");
                    }
                    result = result * radix + value;
                    i++;
                }
                if ((int)result < 0 && result != 0x80000000) {
                    throw new OverflowException("Overflow_Int32");
                }
            }
            else {
                maxVal = UInt32.MaxValue / radix;
                while (i < length && IsDigit(buffer[i], radix, out value)) {
                    // Read all of the digits and convert to a number
                    // Check for overflows - this is sufficient & correct.
                    if (result > maxVal) {
                        throw new OverflowException("Overflow_UInt32");
                    }
                    result = result * radix + value;
                    i++;
                }
            }
            return result;
        }

        static private ulong GrabLongs(uint radix, String buffer, int length,
                                       ref int i, bool isUnsigned) {
            ulong result = 0;
            uint value;
            ulong maxVal;
            // Allow all non-decimal numbers to set the sign bit.
            if (radix == 10 && !isUnsigned) {
                maxVal = (0x7FFFFFFFFFFFFFFF / 10);
                while (i < length && IsDigit(buffer[i], radix, out value)) {
                    // Read all of the digits and convert to a number
                    // Check for overflows - this is sufficient & correct.
                    if (result > maxVal || ((long) result) < 0) {
                        throw new OverflowException("Overflow_Int64");
                    }
                    result = result * radix + value;
                    i++;
                }
                if ((long) result < 0 && result != 0x8000000000000000) {
                    throw new OverflowException("Overflow_Int64");
                }
            }
            else {
                maxVal = unchecked((ulong) -1L) / radix;
                while (i < length && IsDigit(buffer[i], radix, out value)) {
                    // Read all of the digits and convert to a number
                    // Check for overflows - this is sufficient & correct.
                    if (result > maxVal) {
                        throw new OverflowException("Overflow_Int64");
                    }
                    result = result * radix + value;
                    i++;
                }
            }
            return result;
        }

        static bool IsDigit(char c, uint radix, out uint result) {
            if (c >='0' && c <='9') {
                result = (uint) (c-'0');
            }
            else {
                char d = Char.ToLower(c);
                if (d >='a' && d <='z') {
                    //+10 is necessary because a is actually 10, etc.
                    result = (uint) (d-'a'+10);
                }
                else {
                    result = 0;
                    return false;
                }
            }
            return (result < radix);
        }

        public static int StringToInt(String s, int radix, int flags,
                                      int[] currPos)
        {
            if (s == null) {
                return 0;
            }
            int i = currPos[0];
            //Do some radix checking.
            //A radix of -1 says to use whatever base is spec'd on the number.
            //Parse in Base10 until we figure out what the base actually is.
            uint r = (-1==radix)?10U:(uint)radix;
            if (r != 2 && r != 10 && r != 8 && r != 16) {
                throw new ArgumentException("Arg_InvalidBase");
            }
            int length = s.Length;
            if (i < 0 || i >= length) {
                throw new ArgumentOutOfRangeException("startIndex(currPos[0])");
            }
            // Get rid of the whitespace and then check that we've still got
            // some digits to parse.
            if ((flags & IsTight) != 0) {
                i = EatWhiteSpace(s,length,i);
                if (i == length) {
                    throw new FormatException("Format_EmptyInputString");
                }
            }
            int sign = 1;
            bool isUnsigned = ((flags & TreatAsUnsigned) != 0);
            if (s[i] =='-') { // Check for a sign
                if (r != 10) {
                    throw new ArgumentException("ArgCannotHaveNegativeValue");
                }
                if (isUnsigned) {
                    throw new OverflowException("Overflow_NegativeUnsigned");
                }
                sign = -1;
                i++;
            }
            else if (s[i] =='+') {
                i++;
            }
            //Consume the 0x if we're in an unknown base or in base 16.
            if ((radix ==- 1 || radix == 16) && (i + 1 < length) && s[i] =='0') {
                if (s[i + 1] =='x' || s[i + 1] =='X') {
                    r=16;
                    i+=2;
                }
            }
            int grabNumbersStart=i;
            uint result = GrabInts(r,s,length,ref i, isUnsigned);
            if (i == grabNumbersStart) {
                throw new FormatException("Format_NoParsibleDigits");
            }
            if ((flags & IsTight) != 0) {
                //   i = EatWhiteSpace(s,length,i);
                //If we've got effluvia left at the end of the string, complain.
                if (i <(length)) {
                    throw new FormatException("Format_ExtraJunkAtEnd");
                }
            }
            //Put the current index back into the correct place.
            currPos[0]=i;
            //Return the value properly signed.
            if ((flags & TreatAsI1) != 0) {
                if (result > 0xFF) {
                    throw new OverflowException("Overflow_SByte");
                }
                // _ASSERTE(sign==1 || r==10);  // result looks positive when parsed as an I4
                if (result >= 0x80) {
                    sign = -1;
                }
            }
            else if ((flags & TreatAsI2) != 0) {
                if (result > 0xFFFF) {
                    throw new OverflowException("Overflow_Int16");
                }
                // _ASSERTE(sign==1 || r==10);  // result looks positive when parsed as an I4
                if (result >= 0x8000) {
                    sign = -1;
                }
            }
            else if (result == 0x80000000 && sign == 1 && r == 10) {
                throw new OverflowException("Overflow_Int32");
            }
            if (r == 10) {
                return unchecked((int)result) * sign;
            }
            else {
                return unchecked((int) result);
            }
        }

        public static long StringToLong(String s, int radix, int flags, int[] currPos) {
            if (s == null) {
                return 0L;
            }
            int i = currPos[0];
            //Do some radix checking.
            //A radix of -1 says to use whatever base is spec'd on the number.
            //Parse in Base10 until we figure out what the base actually is.
            uint r = (-1==radix)?10U:(uint)radix;
            if (r != 2 && r != 10 && r != 8 && r != 16) {
                throw new ArgumentException("Arg_InvalidBase");
            }
            int length = s.Length;
            if (i < 0 || i >= length) {
                throw new ArgumentOutOfRangeException("startIndex(currPos[0])");
            }
            // Get rid of the whitespace and then check that we've still
            // got some digits to parse.
            if ((flags & IsTight) != 0) {
                i = EatWhiteSpace(s,length,i);
                if (i == length) {
                    throw new FormatException("EmptyInputString");
                }
            }
            int sign = 1;
            bool isUnsigned = ((flags & TreatAsUnsigned) != 0);
            if (s[i] == '-') {
                if (r != 10) {
                    throw new ArgumentException("Negative non-base-10 number");
                }
                if (isUnsigned) {
                    throw new OverflowException("Negative unsigned number");
                }
                sign = -1;
                i++;
            }
            else if (s[i] == '+') {
                i++;
            }
            //Consume the 0x if we're in an unknown base or in base 16.
            if ((radix ==- 1 || radix == 16) && (i + 1 < length) && s[i] =='0') {
                if (s[i + 1] =='x' || s[i + 1] =='X') {
                    r=16;
                    i+=2;
                }
            }
            int grabNumbersStart = i;
            ulong result = GrabLongs(r,s,length,ref i,isUnsigned);
            if (i == grabNumbersStart) {
                throw new FormatException("No parsable digits");
            }
            if ((flags & IsTight) != 0) {
                if (i < length) {
                    throw new FormatException("Extra junk at end");
                }
            }
            //Put the current index back into the correct place.
            currPos[0]=i;
            //Return the value properly signed.
            if (result == 0x8000000000000000 && sign == 1 && r == 10) {
                throw new OverflowException("Overflow_Int64");
            }
            if (r == 10) {
                return unchecked((long) result) * sign;
            }
            else {
                return unchecked((long) result);
            }
        }

        public static String IntToDecimalString(int i) {
            // See also Lightning\Src\VM\COMUtilNative.cpp::IntToDecimalString
            int count;
            char[] buffer = IntToDecimalChars(i, out count);
            return String.StringCTOR(buffer, 0, count);
        }

        internal static char[] IntToDecimalChars(int value, out int count) {
            char[] result = new char[66];
            bool isNegative;
            uint uValue;
            if (value == 0) {
                result[0] = '0';
                count = 1;
                return result;
            }
            if (value < 0) {
                isNegative = true;
                uValue = (uint) -value;
            }
            else {
                isNegative = false;
                uValue =  (uint) value;
            }
            int index = 0;
            do {
                result[index] = (char) ((uValue % 10) + '0');
                index++;
                uValue = uValue / 10;
            } while (uValue != 0);
            if (isNegative) {
                result[index] = '-';
                index++;
            }
            // Reverse the characters in the buffer
            int limit = index / 2;
            count = limit;
            int i = 0;
            index--;
            while (i < index) {
                char t = result[i];
                result[i] = result[index];
                result[index] = t;
                i++;
                index--;
            }
            return result;
        }

        //FCIMPL5(LPVOID, ParseNumbers::IntToString, INT32 n, INT32 radix,
        //        INT32 width, WCHAR paddingChar, INT32 flags);
        public static String IntToString(int n, int radix, int width,
                                         char paddingChar, int flags) {
            // See also Lightning\Src\VM\COMUtilNative.cpp::IntToString

            // changed to fill the char[] backwards to call a normal
            // stringCTOR and not have an additional copy

            bool isNegative = false;
            int charVal;
            int buffLength;
            uint l;

            // Longest possible string length for an integer in
            // binary notation with prefix
            int bufSize = 66;
            char[] buffer = new char[bufSize];
            int index=bufSize;

            if (radix < MinRadix || radix > MaxRadix) {
                throw new ArgumentException("Argument_InvalidBase");
                //COMPlusThrowArgumentException(L"radix", L"Arg_InvalidBase");
            }

            //If the number is negative, make it positive and remember the sign.
            //If the number is MIN_VALUE, this will still be negative,
            //so we'll have to special case this later.
            if (n < 0) {
                isNegative=true;
                // For base 10, write out -num, but other bases write out the
                // 2's complement bit pattern
                if (10 == radix)
                    l = (uint)(-n);
                else
                    l = (uint)n; // REVIEW: comment suggests ~n wanted
            }
            else {
                l=(uint)n;
            }

            //The conversion to a UINT will sign extend the number.  In order to
            //ensure that we only get as many bits as we expect, we chop the
            //number.
            if ((flags & PrintAsI1) != 0) {
                l = l&0xFF;
            }
            else if ((flags & PrintAsI2) != 0) {
                l = l&0xFFFF;
            }
            else if ((flags & PrintAsI4) != 0) {
                l=l&0xFFFFFFFF;
            }

            if (0 == l) { //Special case the 0.
                buffer[--index]='0';
            }
            else {
                do {
                    charVal = (int) (l%(uint)radix);
                    l=l/(uint)radix;
                    if (charVal < 10) {
                        buffer[--index] = (char)(charVal + '0');
                    }
                    else {
                        buffer[--index] = (char)(charVal + 'a' - 10);
                    }
                } while (l != 0);
            }
            //If they want the base, append that to the string (in reverse order)
            if (radix != 10 && ((flags & PrintBase) != 0)) {
                if (16 == radix) {
                    buffer[--index]='x';
                    buffer[--index]='0';
                }
                else if (8 == radix) {
                    buffer[--index]='0';
                }
            }

            if (10 == radix) {
                if (isNegative) {
                    //If it was negative, append the sign.
                    buffer[--index]='-';
                }
                else if ((flags & PrintSign) != 0) {
                    //else if they requested, add the '+';
                    buffer[--index]='+';
                }
                else if ((flags & PrefixSpace) != 0) {
                    //If they requested a leading space, put it on.
                    buffer[--index]=' ';
                }
            }

            //Figure out the size of our string.
            if (width <= bufSize - index) {
                buffLength=bufSize-index;
            }
            else {
                buffLength=width;
            }

            String local = String.StringCTOR(buffer, index, bufSize-index);

            // Pad if necessary, open up access to String if you
            //don't want to make a new string here
            if ((flags & LeftAlign) != 0) {
                local = local.PadRight(buffLength,paddingChar);
            }
            else {
                local = local.PadLeft(buffLength,paddingChar);
            }

            return local;
        }

        //FCIMPL5(LPVOID, ParseNumbers::LongToString, INT32 radix, INT32 width,
        //        INT64 n, WCHAR paddingChar, INT32 flags)
        public static String LongToString(long n, int radix, int width,
                                          char paddingChar, int flags) {
            // See also Lightning\Src\VM\COMUtilNative.cpp::LongToString,
            bool isNegative = false;
            int charVal;
            ulong l;
            int buffLength=0;

            //Longest possible string length for an integer in
            //binary notation with prefix
            int bufSize = 67;
            char[] buffer = new char[67];
            int index=bufSize;

            if (radix < MinRadix || radix > MaxRadix) {
                throw new ArgumentException("Argument_InvalidBase");
                //COMPlusThrowArgumentException(L"radix", L"Arg_InvalidBase");
            }

            //If the number is negative, make it positive and remember the sign.
            if (n < 0) {
                isNegative=true;
                // For base 10, write out -num, but other bases write out the
                // 2's complement bit pattern
                if (10 == radix)
                    l = (ulong)(-n);
                else
                    l = (ulong)n; // REVIEW: comment suggests ~n wanted
            }
            else {
                l=(ulong)n;
            }

            if ((flags & PrintAsI1) != 0) {
                l = l&0xFF;
            }
            else if ((flags & PrintAsI2) != 0) {
                l = l&0xFFFF;
            }
            else if ((flags & PrintAsI4) != 0) {
                l=l&0xFFFFFFFF;
            }

            //Special case the 0.
            if (0 == l) {
                buffer[--index]='0';
            }
            else {
                //Pull apart the number and put the digits (in
                //reverse order) into the buffer.
                for (; l > 0; l = l/(ulong)radix) {
                    if ((charVal =(int)(l%(ulong)radix)) < 10) {
                        buffer[--index] = (char)(charVal + '0');
                    }
                    else {
                        buffer[--index] = (char)(charVal + 'a' - 10);
                    }
                }
            }

            //If they want the base, append that to the string (in reverse order)
            if (radix != 10 && ((flags & PrintBase) != 0)) {
                if (16 == radix) {
                    buffer[--index]='x';
                    buffer[--index]='0';
                }
                else if (8 == radix) {
                    buffer[--index]='0';
                }
                else if ((flags & PrintRadixBase) != 0) {
                    buffer[--index]='#';
                    buffer[--index]=(char)((radix%10)+'0');
                    buffer[--index]=(char)((radix/10)+'0');
                }
            }

            if (10 == radix) {
                if (isNegative) {
                    //If it was negative, append the sign.
                    buffer[--index]='-';
                }
                else if ((flags & PrintSign) != 0) {
                    //else if they requested, add the '+';
                    buffer[--index]='+';
                }
                else if ((flags & PrefixSpace) != 0) {
                    //If they requested a leading space, put it on.
                    buffer[--index]=' ';
                }
            }

            //Figure out the size of our string.
            if (width <= bufSize - index) {
                buffLength=bufSize-index;
            }
            else {
                buffLength=width;
            }

            String local = String.StringCTOR(buffer, index, bufSize-index);

            //Pad if necessary, open up access to String if you
            //don't want to make a new string here
            if ((flags & LeftAlign) != 0) {
                local = local.PadRight(buffLength,paddingChar);
            }
            else {
                local = local.PadLeft(buffLength,paddingChar);
            }

            return local;
        }

        private static String LongToString(int radix, int width, long l, char paddingChar, int flags) {
            // Just in case the C# compiler gets smart enough to inline the
            // original version of the above method (which calls the original
            // version of this method to avoid a problem with fastcall not
            // liking int64 as a first argument).
            return LongToString(l, radix, width, paddingChar, flags);
        }
    }
}
