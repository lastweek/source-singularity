// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Char
//
// Purpose: This is the value class representing a Unicode character
// Char methods until we create this functionality.
//
//===========================================================  
namespace System
{

    using System;
    using System.Globalization;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="Char"]/*' />
    [StructLayout(LayoutKind.Sequential, CharSet=CharSet.Unicode)]
    public struct Char : IComparable {
        //
        // Member Variables
        //
        internal char m_value;

        //
        // Public Constants
        //
        // The maximum character value.
        //| <include path='docs/doc[@for="Char.MaxValue"]/*' />
        public const char MaxValue =  (char) 0xFFFF;
        // The minimum character value.
        //| <include path='docs/doc[@for="Char.MinValue"]/*' />
        public const char MinValue =  (char) 0x00;

        //
        // Private Constants
        //

        //
        // Overridden Instance Methods
        //

        // Calculate a hashcode for a 2 byte Unicode character.
        //| <include path='docs/doc[@for="Char.GetHashCode"]/*' />
        public override int GetHashCode() {
            return (int)m_value | ((int)m_value << 16);
        }

        // Used for comparing two boxed Char objects.
        //
        //| <include path='docs/doc[@for="Char.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (!(obj is Char)) {
                return false;
            }
            return (m_value==((Char)obj).m_value);
        }

        // Compares this object to another object, returning an integer that
        // indicates the relationship.
        // Returns a value less than zero if this  object
        // null is considered to be less than any instance.
        // If object is not of type Char, this method throws an ArgumentException.
        //
        //| <include path='docs/doc[@for="Char.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }
            if (!(value is Char)) {
                throw new ArgumentException ("Arg_MustBeChar");
            }

            return (m_value-((Char)value).m_value);
        }

        // Overrides System.Object.ToString.
        //| <include path='docs/doc[@for="Char.ToString"]/*' />
        public override String ToString() {
            return Char.ToString(m_value);
        }

        //
        // Formatting Methods
        //

        //===================================ToString===================================
        //This static methods takes a character and returns the String representation of it.
        //==============================================================================  
        // Provides a string representation of a character.
        //| <include path='docs/doc[@for="Char.ToString1"]/*' />
        public static String ToString(char c) {
            return new String(new char[] {c});
        }

        //| <include path='docs/doc[@for="Char.Parse"]/*' />
        public static char Parse(String s) {
            if (s == null) {
                throw new ArgumentNullException("s");
            }
            if (s.Length != 1) {
                throw new FormatException("Format_NeedSingleChar");
            }
            return s[0];
        }

        //
        // Static Methods
        //
        //=================================ISDIGIT======================================
        //A wrapper for Char.  Returns a boolean indicating whether    **
        //character c is considered to be a digit.                                    **
        //==============================================================================  
        // Determines whether a character is a digit.
        //| <include path='docs/doc[@for="Char.IsDigit"]/*' />
        public static bool IsDigit(char c) {
            return CharacterInfo.IsDigit(c);
        }

        //=================================ISLETTER=====================================
        //A wrapper for Char.  Returns a boolean indicating whether    **
        //character c is considered to be a letter.                                   **
        //==============================================================================  
        // Determines whether a character is a letter.
        //| <include path='docs/doc[@for="Char.IsLetter"]/*' />
        public static bool IsLetter(char c) {
            return CharacterInfo.IsLetter(c);
        }

        //===============================ISWHITESPACE===================================
        //A wrapper for Char.  Returns a boolean indicating whether    **
        //character c is considered to be a whitespace character.                     **
        //==============================================================================  
        // Determines whether a character is whitespace.
        //| <include path='docs/doc[@for="Char.IsWhiteSpace"]/*' />
        public static bool IsWhiteSpace(char c) {
            return CharacterInfo.IsWhiteSpace(c);
        }


        //===================================IsUpper====================================
        //Arguments: c -- the character to be checked.
        //Returns:  True if c is an uppercase character.
        //==============================================================================  
        // Determines whether a character is upper-case.
        //| <include path='docs/doc[@for="Char.IsUpper"]/*' />
        public static bool IsUpper(char c) {
            return CharacterInfo.IsUpper(c);
        }

        //===================================IsLower====================================
        //Arguments: c -- the character to be checked.
        //Returns:  True if c is an lowercase character.
        //==============================================================================  
        // Determines whether a character is lower-case.
        //| <include path='docs/doc[@for="Char.IsLower"]/*' />
        public static bool IsLower(char c) {
            return CharacterInfo.IsLower(c);
        }

        //================================IsPunctuation=================================
        //Arguments: c -- the character to be checked.
        //Returns:  True if c is an punctuation mark
        //==============================================================================  
        // Determines whether a character is a punctuation mark.
        //| <include path='docs/doc[@for="Char.IsPunctuation"]/*' />
        public static bool IsPunctuation(char c){
            return CharacterInfo.IsPunctuation(c);
        }

        // Determines whether a character is a letter or a digit.
        //| <include path='docs/doc[@for="Char.IsLetterOrDigit"]/*' />
        public static bool IsLetterOrDigit(char c) {
            UnicodeCategory uc = CharacterInfo.GetUnicodeCategory(c);
            return (uc == UnicodeCategory.UppercaseLetter
                    || uc == UnicodeCategory.LowercaseLetter
                    || uc == UnicodeCategory.TitlecaseLetter
                    || uc == UnicodeCategory.ModifierLetter
                    || uc == UnicodeCategory.OtherLetter
                    || uc == UnicodeCategory.DecimalDigitNumber);
        }

        //=================================TOUPPER======================================
        //A wrapper for Char.toUpperCase.  Converts character c to its **
        //uppercase equivalent.  If c is already an uppercase character or is not an  **
        //alphabetic, nothing happens.                                                **
        //==============================================================================  
        // Converts a character to upper-case for the default culture.
        //
        //| <include path='docs/doc[@for="Char.ToUpper1"]/*' />
        public static char ToUpper(char c) {
            return TextInfo.ToUpper(c);
        }


        //=================================TOLOWER======================================
        //A wrapper for Char.toLowerCase.  Converts character c to its **
        //lowercase equivalent.  If c is already a lowercase character or is not an   **
        //alphabetic, nothing happens.                                                **
        //==============================================================================  
        // Converts a character to lower-case for the default culture.
        //| <include path='docs/doc[@for="Char.ToLower1"]/*' />
        public static char ToLower(char c) {
            return TextInfo.ToLower(c);
        }

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="Char.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode() {
            return TypeCode.Char;
        }

        //| <include path='docs/doc[@for="Char.IsControl1"]/*' />
        public static bool IsControl(char c)
        {
            return CharacterInfo.IsControl(c);
        }

        //| <include path='docs/doc[@for="Char.IsControl"]/*' />
        public static bool IsControl(String s, int index) {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsControl(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsDigit1"]/*' />
        public static bool IsDigit(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsDigit(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsLetter1"]/*' />
        public static bool IsLetter(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsLetter(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsLetterOrDigit1"]/*' />
        public static bool IsLetterOrDigit(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsLetterOrDigit(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsLower1"]/*' />
        public static bool IsLower(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsLower(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsNumber"]/*' />
        public static bool IsNumber(char c)
        {
            return CharacterInfo.IsNumber(c);
        }

        //| <include path='docs/doc[@for="Char.IsNumber1"]/*' />
        public static bool IsNumber(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsNumber(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsPunctuation1"]/*' />
        public static bool IsPunctuation (String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsPunctuation(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsSeparator"]/*' />
        public static bool IsSeparator(char c)
        {
            return CharacterInfo.IsSeparator(c);
        }

        //| <include path='docs/doc[@for="Char.IsSeparator1"]/*' />
        public static bool IsSeparator(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsSeparator(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsSurrogate"]/*' />
        public static bool IsSurrogate(char c)
        {
            return CharacterInfo.IsSurrogate(c);
        }

        //| <include path='docs/doc[@for="Char.IsSurrogate1"]/*' />
        public static bool IsSurrogate(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsSurrogate(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsSymbol"]/*' />
        public static bool IsSymbol(char c)
        {
            return CharacterInfo.IsSymbol(c);
        }

        //| <include path='docs/doc[@for="Char.IsSymbol1"]/*' />
        public static bool IsSymbol(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsSymbol(s[index]);
        }


        //| <include path='docs/doc[@for="Char.IsUpper1"]/*' />
        public static bool IsUpper(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsUpper(s[index]);
        }

        //| <include path='docs/doc[@for="Char.IsWhiteSpace1"]/*' />
        public static bool IsWhiteSpace(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return IsWhiteSpace(s[index]);
        }

        //| <include path='docs/doc[@for="Char.GetUnicodeCategory"]/*' />
        public static UnicodeCategory GetUnicodeCategory(char c)
        {
            return CharacterInfo.GetUnicodeCategory(c);
        }

        //| <include path='docs/doc[@for="Char.GetUnicodeCategory1"]/*' />
        public static UnicodeCategory GetUnicodeCategory(String s, int index)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            if (((uint)index)>=((uint)s.Length)) {
                throw new ArgumentOutOfRangeException("index");
            }
            return GetUnicodeCategory(s[index]);
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
