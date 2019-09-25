// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  String
//
// Purpose: Contains headers for the String class.  Actual implementations
// are in String.cpp
//
//===========================================================  
namespace System
{
    using System.Text;
    using System;
    using System.Diagnostics;
    using System.Globalization;
    using System.Threading;
    using System.Collections;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using Microsoft.Bartok.Runtime;

    //
    // For Information on these methods, please see COMString.cpp
    //
    // The String class represents a static string of characters.  Many of
    // the String methods perform some type of transformation on the current
    // instance and return the result as a new String. All comparison methods are
    // implemented as a part of String.  As with arrays, character positions
    // (indices) are zero-based.
    //
    //| <include path='docs/doc[@for="String"]/*' />
    public sealed partial class String : IComparable, ICloneable, IEnumerable {
        //
        //Native Static Methods
        //

        // Joins an array of strings together as one string with a separator between each original string.
        //
        //| <include path='docs/doc[@for="String.Join"]/*' />
        public static String Join(String separator, String[] value) {
            if (value == null) {
                throw new ArgumentNullException("value");
            }
            return Join(separator, value, 0, value.Length);
        }

        ///
        // Joins an array of strings together as one string with a separator
        // between each original string.
        //
        // @param separator the string used as a separator.
        // @param value the array of strings to be joined.
        // @param startIndex the position within the array to start using
        //  strings.
        // @param count the number of strings to take from the array.
        //
        // @return a string consisting of the strings contained in <i>value</i>
        //  from <EM>startIndex</EM> to <EM>startIndex</EM> + <EM>count</EM>
        //  joined together to form a single string, with each of the original
        //  strings separated by <i>separator</i>.
        // 
        //| <include path='docs/doc[@for="String.Join1"]/*' />
        public static String Join(String separator, String[] value,
                                  int startIndex, int count)
        {
            // See also Lightning\Src\VM\COMString.cpp::JoinArray
            if (separator == null) {
                separator = String.Empty;
            }
            if (value == null) {
                throw new ArgumentNullException("value array is null");
            }
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (count < 0) {
                throw new ArgumentOutOfRangeException("count is negative");
            }
            if (startIndex + count > value.Length) {
                throw new ArgumentOutOfRangeException("startIndex+count>value.Length");
            }
            // Special case the empty list of strings
            if (count == 0) {
                return String.Empty;
            }
            // Compute the length of the new string
            int newLength = 0;
            int limit = startIndex + count;
            for (int i = startIndex; i < limit; i++) {
                String s = value[i];
                if (s != null) {
                    newLength += s.m_stringLength;
                }
            }
            newLength += (count - 1) * separator.m_stringLength;
            // Create a new String
            String result = FastAllocateString(newLength);
            if (newLength == 0) {
                return result;
            }
            // Fill in the string
            int dstIndex = 0;
            String firstString = value[startIndex];
            if (firstString != null) {
                FillString(result, 0, firstString);
                dstIndex = firstString.m_stringLength;
            }
            for (int i = startIndex + 1; i < limit; i++) {
                FillString(result, dstIndex, separator);
                dstIndex += separator.m_stringLength;
                String elementString = value[i];
                if (elementString != null) {
                    FillString(result, dstIndex, elementString);
                    dstIndex += elementString.m_stringLength;
                }
            }
            return result;
        }

        private unsafe static bool CaseInsensitiveCompHelper(char * strAChars,
                                                             char * strBChars,
                                                             int aLength,
                                                             int bLength,
                                                             out int result) {
            char charA;
            char charB;
            char *strAStart;

            strAStart = strAChars;

            result = 0;

            // setup the pointers so that we can always increment them.
            // We never access these pointers at the negative offset.
            strAChars--;
            strBChars--;

            do {
                strAChars++; strBChars++;

                charA = *strAChars;
                charB = *strBChars;

                //Case-insensitive comparison on chars greater than 0x80 requires
                //a locale-aware casing operation and we're not going there.
                if (charA >= 0x80 || charB >= 0x80) {
                    // TODO: We should be able to fix this.
                    return false;
                }

                // Do the right thing if they differ in case only.
                // We depend on the fact that the uppercase and lowercase letters
                // in the range which we care about (A-Z,a-z) differ only by the
                // 0x20 bit.
                // The check below takes the xor of the two characters and
                // determines if this bit is only set on one of them.
                // If they're different cases, we know that we need to execute
                // only one of the conditions within block.
                if (((charA^charB) & 0x20) != 0) {
                    if (charA >='A' && charA <='Z') {
                        charA |= (char)0x20;
                    }
                    else if (charB >='A' && charB <='Z') {
                        charB |= (char)0x20;
                    }
                }
            } while (charA == charB && charA != 0);

            // Return the (case-insensitive) difference between them.
            if (charA != charB) {
                result = (int)(charA-charB);
                return true;
            }

            // The length of b was unknown because it was just a pointer to a
            // null-terminated string.
            // If we get here, we know that both A and B are pointing at a null.
            // However, A can have an embedded null.  Check the number of
            // characters that we've walked in A against the expected length.
            if (bLength == -1) {
                if ((strAChars - strAStart) != aLength) {
                    result = 1;
                    return true;
                }
                result=0;
                return true;
            }

            result = (aLength - bLength);
            return true;
        }

        internal unsafe static int nativeCompareOrdinal(String strA, String strB,
                                                        bool bIgnoreCase)
        {
            // See also Lightning\Src\VM\COMString.cpp::FCCompareOrdinal
            int strALength = strA.Length;
            int strBLength = strB.Length;
            fixed(char * strAChars = &strA.m_firstChar) {
                fixed(char * strBCharsStart = &strB.m_firstChar) {

                    // Need copy because fixed vars are readonly
                    char * strBChars = strBCharsStart;

                    // Handle the comparison where we wish to ignore case.
                    if (bIgnoreCase) {
                        int result;
                        if (CaseInsensitiveCompHelper(strAChars, strBChars,
                                                      strALength, strBLength,
                                                      out result)) {
                            return result;
                        }
                        else {
                            // This will happen if we have characters greater
                            // than 0x7F.
                            throw new ArgumentException();
                        }
                    }

                    // If the strings are the same length, compare exactly the
                    // right # of chars.  If they are different, compare the
                    // shortest # + 1 (the '\0').
                    int count = strALength;
                    if (count > strBLength)
                        count = strBLength;

                    long diff = (byte*)strAChars - (byte*)strBChars;

                    // Loop comparing a DWORD at a time.
                    while ((count -= 2) >= 0) {
                        if (((*(int*)((byte*)strBChars + diff))
                            - *(int*)strBChars) != 0) {
                            char * ptr1 = (char*)((byte*)strBChars + diff);
                            char * ptr2 = strBChars;
                            if (*ptr1 != *ptr2) {
                                return ((int)*ptr1 - (int)*ptr2);
                            }
                            return ((int)*(ptr1+1) - (int)*(ptr2+1));
                        }

                        // differs from COMString.cpp because they have DWORD*
                        // and we use char*
                        strBChars += 2;
                    }

                    // Handle an extra WORD.
                    int c;
                    if (count == -1) {
                        c = *((char*)((byte*)strBChars+diff)) - *strBChars;
                        if (c != 0) {
                            return c;
                        }
                    }
                    return strALength - strBLength;
                }
            }
        }

        internal static int nativeCompareOrdinalEx(String strA, int indexA,
                                                   String strB, int indexB,
                                                   int count)
        {
            // See also Lightning\Src\VM\COMString.cpp::CompareOrdinalEx
            throw new Exception("System.String.nativeCompareOrdinalEx not implemented in Bartok!");
        }

        //
        // This is a helper method for the security team.  They need to uppercase some strings (guaranteed to be less
        // than 0x80) before security is fully initialized.  Without security initialized, we can't grab resources (the nlp's)
        // from the assembly.  This provides a workaround for that problem and should NOT be used anywhere else.
        //
        internal static String SmallCharToUpper(String strA)
        {
            String newString = FastAllocateString(strA.Length);
            nativeSmallCharToUpper(strA, newString);
            return newString;
        }

        private static void nativeSmallCharToUpper(String strIn, String strOut)
        {
            // See also Lightning\Src\VM\COMString.cpp::SmallCharToUpper
            throw new Exception("System.String.nativeSmallCharToUpper not implemented in Bartok!");
        }

        // This is a helper method for the security team.  They need to construct strings from a char[]
        // within their homebrewed XML parser.  They guarantee that the char[] they pass in isn't null and
        // that the provided indices are valid so we just stuff real fast.
        internal static String CreateFromCharArray(char[] array, int start, int count)
        {
            String newString = FastAllocateString(count);
            FillStringArray(newString, 0, array, start, count);
            return newString;
        }

        //
        //
        // NATIVE INSTANCE METHODS
        //
        //

        //
        // Search/Query methods
        //

        // Determines whether two strings match.
        //| <include path='docs/doc[@for="String.Equals"]/*' />
        public override bool Equals(Object obj) {
            if (obj is String) {
                return this.Equals((String) obj);
            }
            else {
                return false;
            }
        }

        // Determines whether two strings match.
        //| <include path='docs/doc[@for="String.Equals1"]/*' />
        public unsafe bool Equals(String value) {
            if (value == null) {
                return false;
            }
            if (this.m_stringLength != value.m_stringLength) {
                return false;
            }
            fixed (char *thisCharPtr = &this.m_firstChar) {
                fixed (char *valueCharPtr = &value.m_firstChar) {
                    char *thisCursor = thisCharPtr;
                    char *valueCursor = valueCharPtr;
                    for (int i = this.m_stringLength; i > 0; i--) {
                        if (*thisCursor != *valueCursor) {
                            return false;
                        }
                        thisCursor++;
                        valueCursor++;
                    }
                }
            }
            return true;
        }

        // Determines whether two Strings match.
        //| <include path='docs/doc[@for="String.Equals2"]/*' />
        public static bool Equals(String a, String b) {
            if ((Object)a ==(Object)b) {
                return true;
            }

            if ((Object)a == null || (Object)b == null) {
                return false;
            }

            return a.Equals(b);
        }

        //| <include path='docs/doc[@for="String.operatorEQ"]/*' />
        public static bool operator == (String a, String b)
        {
            return String.Equals(a, b);
        }

        //| <include path='docs/doc[@for="String.operatorNE"]/*' />
        public static bool operator != (String a, String b)
        {
            return !String.Equals(a, b);
        }

        internal unsafe char InternalGetChar(int index)
        {
            // See also Lightning\Src\VM\COMString.cpp::GetCharAt
            if ((uint) index >= (uint) this.m_stringLength) {
                throw new IndexOutOfRangeException();
            }
            fixed (char *charPtr = &this.m_firstChar) {
                return charPtr[index];
            }
        }

        // Gets the character at a specified position.
        //
        //| <include path='docs/doc[@for="String.this"]/*' />
        public char this[int index] {
            get { return InternalGetChar(index); }
        }

        internal unsafe int InternalGetChars(char *output, int maxput)
        {
            fixed (char *charPtr = &this.m_firstChar) {
                int i;
                for (i = 0; i < m_stringLength && i < maxput; i++) {
                    output[i] = charPtr[i];
                }
                return i;
            }
        }

        // Converts a substring of this string to an array of characters.  Copies the
        // characters of this string beginning at position startIndex and ending at
        // startIndex + length - 1 to the character array buffer, beginning
        // at bufferStartIndex.
        //
        //| <include path='docs/doc[@for="String.CopyTo"]/*' />
        public void CopyTo(int sourceIndex, char[] destination, int destinationIndex, int count)
        {
            if (destination == null)
                throw new ArgumentNullException("destination");
            if (count < 0)
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_NegativeCount");
            if (sourceIndex < 0)
                throw new ArgumentOutOfRangeException("sourceIndex", "ArgumentOutOfRange_Index");
            if (count > Length - sourceIndex)
                throw new ArgumentOutOfRangeException("sourceIndex", "ArgumentOutOfRange_IndexCount");
            if (destinationIndex > destination.Length - count || destinationIndex < 0)
                throw new ArgumentOutOfRangeException("destinationIndex", "ArgumentOutOfRange_IndexCount");
            InternalCopyTo(sourceIndex, destination, destinationIndex, count);
        }

        internal unsafe void InternalCopyTo(int sourceIndex, char[] destination,
                                            int destinationIndex, int count) {
            // See also Lightning\Src\VM\COMString.cpp::GetPreallocatedCharArray
            if (sourceIndex + count > this.m_stringLength) {
                throw new ArgumentOutOfRangeException();
            }
            if (count > 0) {
                // Necessary test as &destination[0] is illegal for empty array
                fixed (char *srcPtrFixed = &this.m_firstChar) {
                    fixed (char *dstPtrFixed = destination) {
                        char *srcPtr = srcPtrFixed + sourceIndex;
                        char *dstPtr = dstPtrFixed + destinationIndex;
                        Buffer.MoveMemory((byte *)dstPtr, (byte *)srcPtr,
                                          count * sizeof(char));
                    }
                }
            }
        }

        internal unsafe void CopyToByteArray(int sourceIndex, byte[] destination,
                                      int destinationIndex, int charCount)
        {
            // See also Lightning\Src\VM\COMString.cpp::InternalCopyToByteArray
            // Called by System.Text.UnicodeEncoding.GetBytes() for little-endian Unicode.

            if (destination == null)
                throw new ArgumentNullException("destination");
            if (charCount < 0)
                throw new ArgumentOutOfRangeException("charCount");
            if (destinationIndex < 0)
                throw new ArgumentOutOfRangeException("destinationIndex");
            if (sourceIndex < 0)
                throw new ArgumentOutOfRangeException("sourceIndex");
            if (sourceIndex + charCount > this.m_stringLength)
                throw new ArgumentOutOfRangeException("charCount");

            int byteCount = charCount * 2;
            if (destinationIndex + byteCount > destination.Length)
                throw new ArgumentOutOfRangeException("destinationLength");

            if (charCount > 0) {
                fixed (byte* dest = &destination[destinationIndex])
                fixed (char* src_char0 = &this.m_firstChar) {
                    byte* src_bytes = (byte*)(&src_char0[sourceIndex]);
                    Buffer.MoveMemory(dest, src_bytes, byteCount);
                }
            }
        }

        // Returns the entire string as an array of characters.
        //| <include path='docs/doc[@for="String.ToCharArray"]/*' />
        public char[] ToCharArray() {
            return ToCharArray(0,Length);
        }

        // Returns a substring of this string as an array of characters.
        //
        //| <include path='docs/doc[@for="String.ToCharArray1"]/*' />
        public char[] ToCharArray(int startIndex, int length)
        {
            // Range check everything.
            if (startIndex < 0 || startIndex > Length || startIndex > Length - length)
                throw new ArgumentOutOfRangeException("startIndex", "ArgumentOutOfRange_Index");
            if (length < 0)
                throw new ArgumentOutOfRangeException("length", "ArgumentOutOfRange_Index");

            char[] chars = new char[length];
            InternalCopyTo(startIndex, chars, 0, length);
            return chars;
        }

        // Gets a hash code for this string.  If strings A and B are such that A.Equals(B), then
        // they will return the same hash code.
        //| <include path='docs/doc[@for="String.GetHashCode"]/*' />
        public unsafe override int GetHashCode() {
            // See also Lightning\Src\VM\COMString.cpp::GetHashCode
            fixed (char *charPtrFixed = &this.m_firstChar) {
                char *charPtr = charPtrFixed;
                if (charPtr[this.m_stringLength] != 0) {
                    throw new Exception("Bartok string is not null terminated");
                }
                // See also Lightning\Src\UtilCode.h::HashString
                uint hash = 5381;
                char c = *charPtr;
                while (c != 0) {
                    hash = ((hash << 5) + hash) ^ c;
                    charPtr++;
                    c = *charPtr;
                }
                return (int) hash;
            }
        }

        // Gets the length of this string
        //| <include path='docs/doc[@for="String.Length"]/*' />
        public int Length {
            [NoHeapAllocation]
            get { return InternalLength(); }
        }

        ///<internalonly/>
        internal int ArrayLength {
            [NoHeapAllocation]
            get { return (m_arrayLength); }
        }

        // Used by StringBuilder
        internal int Capacity {
            [NoHeapAllocation]
            get { return (m_arrayLength - 1); }
        }

        // Creates an array of strings by splitting this string at each
        // occurrence of a separator.  The separator is searched for, and if found,
        // the substring preceding the occurrence is stored as the first element in
        // the array of strings.  We then continue in this manner by searching
        // the substring that follows the occurrence.  On the other hand, if the separator
        // is not found, the array of strings will contain this instance as its only element.
        // If the separator is null
        // whitespace (i.e., Character.IsWhitespace) is used as the separator.
        //
        //| <include path='docs/doc[@for="String.Split"]/*' />
        public String [] Split(params char [] separator) {
            return Split(separator, Int32.MaxValue);
        }

        //==============================MakeSeparatorList========================
        //Args: baseString -- the string to parse for the given list of
        //                    separator chars.
        //      Separator  -- A string containing all of the split characters.
        //      list       -- a pointer to a caller-allocated array of ints for
        //                    split char indices.
        //      listLength -- the number of slots allocated in list.
        //Returns: A list of all of the places within baseString where instances
        //         of characters in Separator occur.
        //Exceptions: None.
        //N.B.:  This just returns silently if the caller hasn't allocated
        //       enough space for the int list.
        //=======================================================================  

        // WCHAR * -> char *
        // int * -> int[]

        // CHARARRAYREF --> char[]
        // c->GetNumComponents --> c.Length

        // STRINGREF --> String
        // s->GetStringLength --> s.Length
        // s->GetBuffer --> fixed(&s.m_firstChar)

        // COMNlsInfo::nativeIsWhiteSpace --> Char.IsWhiteSpace
        // ArrayContains(char,char* start,char* end)
        //   --> ArrayContains(char, char[] buf)
        private unsafe static int MakeSeparatorList(String baseString, char[] Separator, int[] list, int listLength) {
            // From Lightning\Src\VM\COMString.cpp::MakeSeparatorList
            int i;
            int foundCount=0;
            fixed (char *thisChars = &baseString.m_firstChar) {
                int thisLength = baseString.Length;

                if (Separator == null || Separator.Length == 0) {
                    //If they passed null or an empty string,
                    //look for whitespace.
                    for (i = 0; i < thisLength && foundCount < listLength; i++) {
                        // was nativeIsWhiteSpace()
                        if (Char.IsWhiteSpace(thisChars[i])) {
                            list[foundCount++]=i;
                        }
                    }
                }
                else {
                    //WCHAR *searchChars = (WCHAR *)Separator->GetDataPtr();

                    int searchLength = Separator.Length;
                    //If they passed in a string of chars,
                    //actually look for those chars.
                    for (i = 0; i < thisLength && foundCount < listLength; i++) {
                        if (ArrayContains(thisChars[i],Separator) >= 0) {
                            list[foundCount++]=i;
                        }
                    }
                }
                return foundCount;
            }
        }

        // Creates an array of strings by splitting this string at each
        // occurrence of a separator.  The separator is searched for, and if found,
        // the substring preceding the occurrence is stored as the first element in
        // the array of strings.  We then continue in this manner by searching
        // the substring that follows the occurrence.  On the other hand, if the separator
        // is not found, the array of strings will contain this instance as its only element.
        // If the separator is the empty string (i.e., String.Empty), then
        // whitespace (i.e., Character.IsWhitespace) is used as the separator.
        // If there are more than count different strings, the last n-(count-1)
        // elements are concatenated and added as the last String.
        //
        //| <include path='docs/doc[@for="String.Split1"]/*' />
        //| <include path='docs/doc[@for="String.Split1"]/*' />

        // STRINGREF --> String
        // PTRARRAYREF --> String[]
        // p->SetAt(0, v) --> p[0] = v
        //
        // LPVOID --> gone
        // CQuickBytes --> gone

        // AllocateObjectArray(x,g_pStringClass) --> new String[x]
        // NewString(&ref, index, size) --> ref.Substring(index, size)

        public String[] Split(char[] separator, int count) {
            // See also Lightning\Src\VM\COMString.cpp::Split
            // This implementation based on COMString

            int numReplaces;
            int numActualReplaces;
            int[] sepList;
            int currIndex=0;
            int arrIndex=0;
            //char *thisChars;
            int thisLength;
            int i;
            String[] splitStrings;
            String temp;

            if (count < 0) {
                throw new ArgumentOutOfRangeException
                    ("count", "ArgumentOutOfRange_Negative");
            }

            //Allocate space and fill an array of ints with a list of everyplace
            //within our String that a separator character occurs.
            sepList = new int[this.Length];
            numReplaces = MakeSeparatorList(this, separator, sepList, this.Length);
            //Handle the special case of no replaces.
            if (0 == numReplaces) {
                splitStrings = new String[1];
                splitStrings[0] = this;
                return splitStrings;
            }
            thisLength = Length;

            count--;
            numActualReplaces = (numReplaces<count) ? numReplaces : count;

            //Allocate space for the new array.
            //+1 for the string from the end of the last replace to the end
            //of the String.
            splitStrings = new String[numActualReplaces+1];

            for (i = 0; i < numActualReplaces && currIndex < thisLength; i++) {
                temp = this.Substring(currIndex, sepList[i]-currIndex);

                splitStrings[arrIndex++] = temp;
                currIndex=sepList[i]+1;
            }

            //Handle the last string at the end of the array if there is one.

            if (currIndex < thisLength) {
                temp = this.Substring(currIndex, thisLength-currIndex);
                splitStrings[arrIndex] = temp;
            }
            else if (arrIndex == numActualReplaces) {
                //We had a separator character at the end of a string.  Rather than just allowing
                //a null character, we'll replace the last element in the array with an empty string.
                temp = Empty;
                splitStrings[arrIndex] = temp;
            }

            return splitStrings;
        }

        // Returns a substring of this string.
        //
        //| <include path='docs/doc[@for="String.Substring"]/*' />
        public String Substring(int startIndex) {
            return this.Substring (startIndex, Length-startIndex);
        }

        // Returns a substring of this string.
        //
        //| <include path='docs/doc[@for="String.Substring1"]/*' />
        public String Substring(int startIndex, int length) {

            int thisLength = Length;

            //Bounds Checking.
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex", "ArgumentOutOfRange_StartIndex");
            }

            if (length < 0) {
                throw new ArgumentOutOfRangeException("length", "ArgumentOutOfRange_NegativeLength");
            }

            if (startIndex > thisLength - length) {
                throw new ArgumentOutOfRangeException("length", "ArgumentOutOfRange_IndexLength");
            }

            String s = FastAllocateString(length);
            FillSubstring(s, 0, this, startIndex, length);

            return s;
        }

        internal String TrimHelper(char[] trimChars, int trimType)
        {
            // See also Lighting\Src\VM\COMString.cpp::TrimHelper
            int stringLength = this.m_stringLength;
            int iLeft = 0;
            int iRight = stringLength - 1;
            this.TrimHelper(trimChars, trimType, ref iLeft, ref iRight);
            int newLength = iRight - iLeft + 1;
            if (newLength == stringLength) {
                return this;
            }
            else if (newLength == 0) {
                return String.Empty;
            }
            else {
                String result = FastAllocateString(newLength);
                FillSubstring(result, 0, this, iLeft, newLength);
                return result;
            }
        }

        private unsafe void TrimHelper(char[] trimChars, int trimType,
                                       ref int iLeft, ref int iRight)
        {
            fixed (char *charPtr = &this.m_firstChar) {
                if (trimType == String.TrimHead ||
                    trimType == String.TrimBoth) {
                    while (iLeft <= iRight &&
                           ArrayContains(charPtr[iLeft], trimChars) >= 0) {
                        iLeft++;
                    }
                }
                if (trimType == String.TrimTail ||
                    trimType == String.TrimBoth) {
                    while (iRight >= iLeft &&
                           ArrayContains(charPtr[iRight], trimChars) >= 0) {
                        iRight--;
                    }
                }
            }
        }

        private static int ArrayContains(char c, char[] charArray) {
            int limit = charArray.Length;
            for (int i = 0; i < limit; i++) {
                if (charArray[i] == c) {
                    return i;
                }
            }
            return -1;
        }

        ///
        // Creates a new string from the characters in a subarray.  The new
        // string will be created from the characters in <i>value</i> between
        // <i>startIndex</i> and <i>startIndex</i> + <i>length</i> - 1.
        //
        // @param value an array of characters.
        // @param startIndex the index at which the subarray begins.
        // @param length the length of the subarray.
        //
        // @exception ArgumentException if value is <b>null</b>.
        // @exception ArgumentException if <i>startIndex</i> or
        //  <i>startIndex</i>+<i>length</i>-1 are not valid indices of
        //  <i>value</i>.
        // 
        //| <include path='docs/doc[@for="String.String7"]/*' />

        public static String StringCTOR(char[] value, int startIndex,
                                        int length) {
            // See also Lightning\Src\VM\COMString.cpp::StringInitCharArray
            if (value == null) {
                throw new ArgumentNullException("array value is null");
            }
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (length < 0) {
                throw new ArgumentOutOfRangeException("length is negative");
            }
            if (length == 0) {
                return String.Empty;
            }
            else {
                String result = FastAllocateString(length);
                FillStringArray(result, 0, value, startIndex, length);
                return result;
            }
        }

        ///
        // Creates a new string from the characters in a subarray.  The new
        // string will be created from the characters in <i>value</i>.
        //
        // @param value an array of characters.
        //
        // @exception ArgumentException if value is <b>null</b>.
        // 
        //| <include path='docs/doc[@for="String.String5"]/*' />
        public static String StringCTOR(char[] value) {
            // See also Lightning\Src\VM\COMString.cpp::StringInitChars
            if (value == null) {
                return String.Empty;
            }
            int length = value.Length;
            if (length == 0) {
                return String.Empty;
            }
            String result = FastAllocateString(length);
            FillStringArray(result, 0, value, 0, length);
            return result;
        }

        internal static String NewString(String curr,int start,int copyLen,
                                         int capacity) {
            String result = FastAllocateString(capacity);
            FillSubstring(result, 0, curr, start, copyLen);
            return result;
        }

        //| <include path='docs/doc[@for="String.String6"]/*' />
        public static String StringCTOR(char c, int count) {
            // See also Lightning\Src\VM\COMString.cpp::StringInitCharCount
            if (count < 0) {
                throw new ArgumentOutOfRangeException("count is negative");
            }
            if (count == 0) {
                return String.Empty;
            }
            else {
                String result = FastAllocateString(count);
                FillStringChar(result, 0, c, count);
                return result;
            }
        }

        // Removes a string of characters from the ends of this string.
        //| <include path='docs/doc[@for="String.Trim"]/*' />
        public String Trim(params char[] trimChars) {
            if (null == trimChars || trimChars.Length == 0) {
                trimChars=CharacterInfo.WhitespaceChars;
            }
            return TrimHelper(trimChars,TrimBoth);
        }

        // Removes a string of characters from the beginning of this string.
        //| <include path='docs/doc[@for="String.TrimStart"]/*' />
        public String TrimStart(params char[] trimChars) {
            if (null == trimChars || trimChars.Length == 0) {
                trimChars=CharacterInfo.WhitespaceChars;
            }
            return TrimHelper(trimChars,TrimHead);
        }


        // Removes a string of characters from the end of this string.
        //| <include path='docs/doc[@for="String.TrimEnd"]/*' />
        public String TrimEnd(params char[] trimChars) {
            if (null == trimChars || trimChars.Length == 0) {
                trimChars=CharacterInfo.WhitespaceChars;
            }
            return TrimHelper(trimChars,TrimTail);
        }
        
        unsafe static private String CreateString(sbyte *value, int startIndex, int length, Encoding enc) {
            if (enc == null)
                return new String(value, startIndex, length); // default to ANSI
            if (length < 0)
                throw new ArgumentOutOfRangeException("length","ArgumentOutOfRange_NeedNonNegNum");
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex","ArgumentOutOfRange_StartIndex");
            }
            if ((value + startIndex) < value) {
                // overflow check
                throw new ArgumentOutOfRangeException("startIndex","ArgumentOutOfRange_PartialWCHAR");
            }
            byte [] b = new byte[length];
            if (length > 0) {
                fixed(byte* pDest = b) {
                    Buffer.MoveMemory(pDest, ((byte*)value)+startIndex, length);
                }
            }
            return enc.GetString(b);
        }

        // For ASCIIEncoding::GetString()
        unsafe static internal String CreateStringFromASCII(byte[] bytes, int startIndex, int length) {
            Debug.Assert(bytes != null, "need a byte[].");
            Debug.Assert(startIndex >= 0 && (startIndex < bytes.Length || bytes.Length == 0), "startIndex >= 0 && startIndex < bytes.Length");
            Debug.Assert(length >= 0 && length <= bytes.Length - startIndex, "length >= 0 && length <= bytes.Length - startIndex");
            if (length == 0)
                return String.Empty;
            String s = FastAllocateString(length);
            fixed(char* pChars = &s.m_firstChar) {
                for (int i = 0; i < length; i++)
                    pChars[i] = (char) (bytes[i+startIndex] & 0x7f);
            }
            return s;
        }

        // For Latin1Encoding::GetString()
        unsafe static internal String CreateStringFromLatin1(byte[] bytes, int startIndex, int length) {
            Debug.Assert(bytes != null, "need a byte[].");
            Debug.Assert(startIndex >= 0 && (startIndex < bytes.Length || bytes.Length == 0), "startIndex >= 0 && startIndex < bytes.Length");
            Debug.Assert(length >= 0 && length <= bytes.Length - startIndex, "length >= 0 && length <= bytes.Length - startIndex");
            if (length == 0)
                return String.Empty;
            String s = FastAllocateString(length);
            fixed(char* pChars = &s.m_firstChar) {
                for (int i = 0; i < length; i++)
                    pChars[i] = (char) (bytes[i+startIndex]);
            }
            return s;
        }

        private static String FastAllocateString(int stringLength) {
            return GC.AllocateString(stringLength);
        }

        [Inline]
        internal void InitializeStringLength(int stringLength) {
            this.m_arrayLength = stringLength+1;
            this.m_stringLength = stringLength;
        }

        private unsafe static void FillString(String dest, int destPos,
                                              String src) {
            fixed (char *srcPtr = &src.m_firstChar) {
                FillStringCharPtr(dest, destPos, srcPtr, src.m_stringLength);
            }
        }

        private unsafe static void FillStringChecked(String dest, int destPos,
                                                     String src) {
            if (!(src.Length <= dest.ArrayLength - destPos)) {
                throw new IndexOutOfRangeException(); // REVIEW: param?
            }
            fixed (char *srcPtr = &src.m_firstChar) {
                FillStringCharPtr(dest, destPos, srcPtr, src.m_stringLength);
            }
        }

        private unsafe static void FillStringEx(String dest, int destPos,
                                                String src,int srcLength) {
            // ASSERT(srcLength <= dest.ArrayLength - destPos);
            fixed (char *srcPtr = &src.m_firstChar) {
                FillStringCharPtr(dest, destPos, srcPtr, srcLength);
            }
        }

        private unsafe static void FillStringChar(String dest, int destPos,
                                                  char c, int count) {
            fixed (char *destPtr = &dest.m_firstChar) {
                char *charPtr = destPtr + destPos;
                // Set the odd leader char if necessary
                if (destPos % 2 == 1) {
                    *charPtr = c;
                    charPtr++;
                    count--;
                }
                // Set the buffer 2 chars at a time
                int c2 = (c << 16) | c;
                int *intPtr = (int *) charPtr;
                count--;              // Prevent overruns from odd lengths
                while (count > 0) {
                    *intPtr = c2;
                    intPtr++;
                    count -= 2;
                }
                // Set the odd trailer char if necessary
                if (count == 0) {
                    *((char *) intPtr) = c;
                }
            }
        }

        private unsafe static void FillStringCharPtr(String dest, int destPos,
                                                     char *srcPtr, int count) {
            fixed (char *charPtr = &dest.m_firstChar) {
                char *destPtr = charPtr + destPos;
                Buffer.MoveMemory((byte *)destPtr, (byte *)srcPtr, count * sizeof(char));
            }
        }

        private unsafe static void FillStringBytePtr(String dest, int destPos,
                                                     byte *srcPtr, int count) {
            fixed (char *charPtr = &dest.m_firstChar) {
                char *destPtr = charPtr + destPos;
                for (int i = 0; i < count; i++) {
                    *destPtr++ = (char)*srcPtr++;
                }
            }
        }

        private unsafe static void FillStringArray(String dest, int stringStart,
                                                   char[] array, int charStart,
                                                   int count) {
            fixed (char *destPtr = &array[charStart]) {
                FillStringCharPtr(dest, stringStart, destPtr, count);
            }
        }

        private unsafe static void FillSubstring(String dest, int destPos,
                                                 String src, int startPos,
                                                 int count) {
            fixed (char *srcPtr = &src.m_firstChar) {
                FillStringCharPtr(dest, destPos, srcPtr + startPos, count);
            }
        }

        //
        //
        // INSTANCE METHODS
        //
        //

        // Provides a culture-correct string comparison. StrA is compared to StrB
        // to determine whether it is lexicographically less, equal, or greater, and then returns
        // either a negative integer, 0, or a positive integer; respectively.
        //
        //| <include path='docs/doc[@for="String.Compare"]/*' />
        public static int Compare(String strA, String strB) {
            return CompareInfo.Compare(strA, strB, CompareOptions.None);
        }

        // Provides a culture-correct string comparison. strA is compared to strB
        // to determine whether it is lexicographically less, equal, or greater, and then a
        // negative integer, 0, or a positive integer is returned; respectively.
        // The case-sensitive option is set by ignoreCase
        //
        //| <include path='docs/doc[@for="String.Compare1"]/*' />
        public static int Compare(String strA, String strB, bool ignoreCase) {
            if (ignoreCase) {
                return CompareInfo.Compare(strA, strB, CompareOptions.IgnoreCase);
            }
            return CompareInfo.Compare(strA, strB, CompareOptions.None);
        }

        // [Bartok]:
        public static int Compare(String strA, String strB, bool ignoreCase,
                                  CultureInfo info)
        {
            return Compare(strA, strB, ignoreCase);
        }

        // Determines whether two string regions match.  The substring of strA beginning
        // at indexA of length count is compared with the substring of strB
        // beginning at indexB of the same length.
        //
        //| <include path='docs/doc[@for="String.Compare3"]/*' />
        public static int Compare(String strA, int indexA, String strB, int indexB, int length) {
            int lengthA = length;
            int lengthB = length;

            if (strA != null) {
                if (strA.Length - indexA < lengthA) {
                    lengthA = (strA.Length - indexA);
                }
            }

            if (strB != null) {
                if (strB.Length - indexB < lengthB) {
                    lengthB = (strB.Length - indexB);
                }
            }
            return CompareInfo.Compare(strA, indexA, lengthA, strB, indexB, lengthB, CompareOptions.None);
        }


        // Determines whether two string regions match.  The substring of strA beginning
        // at indexA of length count is compared with the substring of strB
        // beginning at indexB of the same length.  Case sensitivity is determined by the ignoreCase boolean.
        //
        //| <include path='docs/doc[@for="String.Compare4"]/*' />
        public static int Compare(String strA, int indexA, String strB, int indexB, int length, bool ignoreCase) {
            int lengthA = length;
            int lengthB = length;

            if (strA != null) {
                if (strA.Length - indexA < lengthA) {
                    lengthA = (strA.Length - indexA);
                }
            }

            if (strB != null) {
                if (strB.Length - indexB < lengthB) {
                    lengthB = (strB.Length - indexB);
                }
            }

            if (ignoreCase) {
                return CompareInfo.Compare(strA, indexA, lengthA, strB, indexB, lengthB, CompareOptions.IgnoreCase);
            }
            return CompareInfo.Compare(strA, indexA, lengthA, strB, indexB, lengthB, CompareOptions.None);
        }

        // Compares this object to another object, returning an integer that
        // indicates the relationship. This method returns a value less than 0 if this is less than value, 0
        // if this is equal to value, or a value greater than 0
        // if this is greater than value.  Strings are considered to be
        // greater than all non-String objects.  Note that this means sorted
        // arrays would contain nulls, other objects, then Strings in that order.
        //
        //| <include path='docs/doc[@for="String.CompareTo"]/*' />
        public int CompareTo(Object value) {
            if (value == null) {
                return 1;
            }

            if (!(value is String)) {
                throw new ArgumentException("Arg_MustBeString");
            }

            return String.Compare(this,(String)value);
        }

        // Determines the sorting relation of StrB to the current instance.
        //
        //| <include path='docs/doc[@for="String.CompareTo1"]/*' />
        public int CompareTo(String strB) {
            if (strB == null) {
                return 1;
            }
            return CompareInfo.Compare(this, strB, 0);
        }

        // Compares strA and strB using an ordinal (code-point) comparison.
        //
        //| <include path='docs/doc[@for="String.CompareOrdinal"]/*' />
        public static int CompareOrdinal(String strA, String strB) {
            if (strA == null || strB == null) {
                if ((Object)strA ==(Object)strB) { //they're both null;
                    return 0;
                }
                return (strA==null)? -1 : 1; //-1 if A is null, 1 if B is null.
            }

            return nativeCompareOrdinal(strA, strB, false);
        }

        // Compares strA and strB using an ordinal (code-point) comparison.
        //
        //| <include path='docs/doc[@for="String.CompareOrdinal"]/*' />
        public static int CompareOrdinal(String strA, String strB, bool ignoreCase) {
            if (strA == null || strB == null) {
                if ((Object)strA ==(Object)strB) { //they're both null;
                    return 0;
                }
                return (strA==null)? -1 : 1; //-1 if A is null, 1 if B is null.
            }

            return nativeCompareOrdinal(strA, strB, ignoreCase);
        }

        // Compares strA and strB using an ordinal (code-point) comparison.
        //
        //| <include path='docs/doc[@for="String.CompareOrdinal1"]/*' />
        public static int CompareOrdinal(String strA, int indexA, String strB, int indexB, int length) {
            if (strA == null || strB == null) {
                if ((Object)strA ==(Object)strB) { //they're both null;
                    return 0;
                }

                return (strA==null)? -1 : 1; //-1 if A is null, 1 if B is null.
            }

            return nativeCompareOrdinalEx(strA, indexA, strB, indexB, length);
        }


        // Determines whether a specified string is a suffix of the the current instance.
        //
        // The case-sensitive and culture-sensitive option is set by options,
        // and the default culture is used.
        //
        //| <include path='docs/doc[@for="String.EndsWith"]/*' />
        public bool EndsWith(String value) {
            if (null == value) {
                throw new ArgumentNullException("value");
            }
            int valueLen = value.Length;
            int thisLen = this.Length;
            if (valueLen > thisLen) {
                return false;
            }
            return (0==Compare(this, thisLen-valueLen, value, 0, valueLen));
        }

        public bool EndsWith(char value) {
            int thisLen = this.Length;
            if (thisLen != 0) {
                if (this[thisLen - 1] == value)
                    return true;
            }
            return false;
        }


        // Returns the index of the first occurrence of value in the current instance.
        // The search starts at startIndex and runs thorough the next count characters.
        //
        //| <include path='docs/doc[@for="String.IndexOf"]/*' />
        public int IndexOf(char value) {
            return IndexOf(value, 0, this.Length);
        }

        //| <include path='docs/doc[@for="String.IndexOf1"]/*' />
        public int IndexOf(char value, int startIndex) {
            return IndexOf(value, startIndex, this.Length - startIndex);
        }

        //| <include path='docs/doc[@for="String.IndexOf2"]/*' />
        public unsafe int IndexOf(char value, int startIndex, int count) {
            // See also Lightning\Src\VM\COMString.cpp::IndexOfChar
            if (startIndex < 0 || startIndex > this.m_stringLength) {
                throw new ArgumentOutOfRangeException("startIndex out of range");
            }
            if (count < 0 || startIndex + count > this.m_stringLength) {
                throw new ArgumentOutOfRangeException("count out of range");
            }
            fixed (char *charPtr = &this.m_firstChar) {
                char *cursor = charPtr + startIndex;
                for (int i = count; i > 0; i--) {
                    if (*cursor == value) {
                        return (startIndex + (count - i));
                    }
                    cursor++;
                }
            }
            return -1;
        }

        // Returns the index of the first occurrence of any character in value in the current instance.
        // The search starts at startIndex and runs to endIndex-1. [startIndex,endIndex).
        //

        //| <include path='docs/doc[@for="String.IndexOfAny1"]/*' />
        public int IndexOfAny(char [] anyOf) {
            return IndexOfAny(anyOf,0, this.Length);
        }

        //| <include path='docs/doc[@for="String.IndexOfAny2"]/*' />
        public int IndexOfAny(char [] anyOf, int startIndex) {
            return IndexOfAny(anyOf, startIndex, this.Length - startIndex);
        }

        //| <include path='docs/doc[@for="String.IndexOfAny3"]/*' />
        public unsafe int IndexOfAny(char [] anyOf, int startIndex, int count) {
            // See also Lightning\Src\VM\COMString.cpp::IndexOfCharArray
            if (anyOf == null) {
                throw new ArgumentNullException("anyOf array is null");
            }
            if (startIndex < 0 || startIndex > this.m_stringLength) {
                throw new ArgumentOutOfRangeException("startIndex out of range");
            }
            if (count < 0 || startIndex + count > this.m_stringLength) {
                throw new ArgumentOutOfRangeException("count out of range");
            }
            fixed (char *charPtr = &this.m_firstChar) {
                char *cursor = charPtr + startIndex;
                for (int i = count; i > 0; i--) {
                    if (ArrayContains(*cursor, anyOf) >= 0) {
                        return (startIndex + (count - i));
                    }
                    cursor++;
                }
            }
            return -1;
        }

        // Determines the position within this string of the first occurrence of the specified
        // string, according to the specified search criteria.  The search begins at
        // the first character of this string, it is case-sensitive and culture-sensitive,
        // and the default culture is used.
        //
        //| <include path='docs/doc[@for="String.IndexOf6"]/*' />
        public int IndexOf(String value) {
            return CompareInfo.IndexOf(this,value);
        }

        // Determines the position within this string of the first occurrence of the specified
        // string, according to the specified search criteria.  The search begins at
        // startIndex, it is case-sensitive and culture-sensitve, and the default culture is used.
        //
        //| <include path='docs/doc[@for="String.IndexOf7"]/*' />
        public int IndexOf(String value, int startIndex){
            return CompareInfo.IndexOf(this,value,startIndex);
        }

        // Determines the position within this string of the first occurrence of the specified
        // string, according to the specified search criteria.  The search begins at
        // startIndex, ends at endIndex and the default culture is used.
        //
        //| <include path='docs/doc[@for="String.IndexOf8"]/*' />
        public int IndexOf(String value, int startIndex, int count){
            if (startIndex + count > this.Length) {
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_Index");
            }
            return CompareInfo.IndexOf(this, value, startIndex, count, CompareOptions.None);
        }


        // Returns the index of the last occurrence of value in the current instance.
        // The search starts at startIndex and runs to endIndex. [startIndex,endIndex].
        // The character at position startIndex is included in the search.  startIndex is the larger
        // index within the string.
        //
        //| <include path='docs/doc[@for="String.LastIndexOf"]/*' />
        public int LastIndexOf(char value) {
            return LastIndexOf(value, this.Length-1, this.Length);
        }

        //| <include path='docs/doc[@for="String.LastIndexOf1"]/*' />
        public int LastIndexOf(char value, int startIndex){
            return LastIndexOf(value,startIndex,startIndex + 1);
        }

        //| <include path='docs/doc[@for="String.LastIndexOf2"]/*' />
        public unsafe int LastIndexOf(char value, int startIndex, int count) {
            // See also Lightning\Src\VM\COMString.cpp::LastIndexOfChar
            if (this.m_stringLength == 0) {
                return -1;
            }
            if (startIndex < 0 || startIndex >= this.m_stringLength) {
                throw new ArgumentOutOfRangeException("startIndex out of range");
            }
            if (count < 0 || count - 1 > startIndex) {
                throw new ArgumentOutOfRangeException("count out of range");
            }
            fixed (char *charPtr = &this.m_firstChar) {
                char *cursor = charPtr + startIndex;
                for (int i = count; i > 0; i--) {
                    if (*cursor == value) {
                        return (startIndex - (count - i));
                    }
                    cursor--;
                }
            }
            return -1;
        }

        // Returns the index of the last occurrence of any character in value in the current instance.
        // The search starts at startIndex and runs to endIndex. [startIndex,endIndex].
        // The character at position startIndex is included in the search.  startIndex is the larger
        // index within the string.
        //

        //| <include path='docs/doc[@for="String.LastIndexOfAny1"]/*' />
        public int LastIndexOfAny(char [] anyOf) {
            return LastIndexOfAny(anyOf,this.Length-1,this.Length);
        }

        //| <include path='docs/doc[@for="String.LastIndexOfAny2"]/*' />
        public int LastIndexOfAny(char [] anyOf, int startIndex) {
            return LastIndexOfAny(anyOf,startIndex,startIndex + 1);
        }

        //| <include path='docs/doc[@for="String.LastIndexOfAny3"]/*' />
        public unsafe int LastIndexOfAny(char [] anyOf, int startIndex,
                                         int count) {
            // See also Lightning\Src\VM\COMString.cpp::LastIndexOfCharArray
            if (anyOf == null) {
                throw new ArgumentNullException("anyOf array is null");
            }
            if (this.m_stringLength == 0) {
                return -1;
            }
            if (startIndex < 0 || startIndex >= this.m_stringLength) {
                throw new ArgumentOutOfRangeException("startIndex out of range");
            }
            if (count < 0 || count - 1 > startIndex) {
                throw new ArgumentOutOfRangeException("count out of range");
            }
            fixed (char *charPtr = &this.m_firstChar) {
                char *cursor = charPtr + startIndex;
                for (int i = count; i > 0; i--) {
                    if (ArrayContains(*cursor, anyOf) >= 0) {
                        return (startIndex - (count - 1));
                    }
                    cursor--;
                }
            }
            return -1;
        }

        // Returns the index of the last occurrence of any character in value in the current instance.
        // The search starts at startIndex and runs to endIndex. [startIndex,endIndex].
        // The character at position startIndex is included in the search.  startIndex is the larger
        // index within the string.
        //
        //| <include path='docs/doc[@for="String.LastIndexOf6"]/*' />
        public int LastIndexOf(String value) {
            return LastIndexOf(value, this.Length-1,this.Length);
        }

        //| <include path='docs/doc[@for="String.LastIndexOf7"]/*' />
        public int LastIndexOf(String value, int startIndex) {
            return LastIndexOf(value, startIndex, startIndex + 1);
        }

        //| <include path='docs/doc[@for="String.LastIndexOf8"]/*' />
        public int LastIndexOf(String value, int startIndex, int count) {
            if (count < 0) {
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_Count");
            }
            return CompareInfo.LastIndexOf(this, value, startIndex, count, CompareOptions.None);
        }


        //
        //
        //| <include path='docs/doc[@for="String.PadLeft"]/*' />
        public String PadLeft(int totalWidth) {
            return PadHelper(totalWidth, ' ', false);
        }

        //| <include path='docs/doc[@for="String.PadLeft1"]/*' />
        public String PadLeft(int totalWidth, char paddingChar) {
            return PadHelper(totalWidth, paddingChar, false);
        }

        //| <include path='docs/doc[@for="String.PadRight"]/*' />
        public String PadRight(int totalWidth) {
            return PadHelper(totalWidth, ' ', true);
        }

        //| <include path='docs/doc[@for="String.PadRight1"]/*' />
        public String PadRight(int totalWidth, char paddingChar) {
            return PadHelper(totalWidth, paddingChar, true);
        }

        private String PadHelper(int totalWidth, char paddingChar,
                                 bool isRightPadded) {
            // See also Lightning\Src\VM\COMString.cpp::PadHelper
            if (totalWidth < 0) {
                throw new ArgumentOutOfRangeException("totalWidth is negative");
            }
            if (totalWidth <= this.m_stringLength) {
                return this;
            }
            int padCount = totalWidth - this.m_stringLength;
            String result = FastAllocateString(totalWidth);
            if (isRightPadded) {
                FillString(result, 0, this);
                FillStringChar(result, this.m_stringLength,
                               paddingChar, padCount);
            }
            else {

                FillStringChar(result, 0, paddingChar, padCount);
                FillString(result, padCount, this);
            }
            return result;
        }

        // Determines whether a specified string is a prefix of the current instance
        //
        //| <include path='docs/doc[@for="String.StartsWith"]/*' />
        public bool StartsWith(String value) {
            if (null == value) {
                throw new ArgumentNullException("value");
            }
            if (this.Length < value.Length) {
                return false;
            }
            return (0==Compare(this,0, value,0, value.Length));
        }

        // Creates a copy of this string in lower case.
        //| <include path='docs/doc[@for="String.ToLower"]/*' />
        public String ToLower() {
            return TextInfo.ToLower(this);
        }

        // Creates a copy of this string in upper case.
        //| <include path='docs/doc[@for="String.ToUpper"]/*' />
        public String ToUpper() {
            return TextInfo.ToUpper(this);
        }

        // Returns this string.
        //| <include path='docs/doc[@for="String.ToString"]/*' />
        public override String ToString() {
            return this;
        }

        // Method required for the ICloneable interface.
        // There's no point in cloning a string since they're immutable, so we simply return this.
        //| <include path='docs/doc[@for="String.Clone"]/*' />
        public Object Clone() {
            return this;
        }


        // Trims the whitespace from both ends of the string.  Whitespace is defined by
        // CharacterInfo.WhitespaceChars.
        //
        //| <include path='docs/doc[@for="String.Trim1"]/*' />
        public String Trim() {
            return this.Trim(CharacterInfo.WhitespaceChars);
        }

        //
        //
        //| <include path='docs/doc[@for="String.Insert"]/*' />
        public String Insert(int startIndex, String value) {
            // See also Lightning\Src\VM\COMString.cpp::Insert
            if (startIndex < 0 || startIndex > this.m_stringLength) {
                throw new ArgumentOutOfRangeException("startIndex out of range");
            }
            if (value == null) {
                throw new ArgumentNullException("value string is null");
            }
            int newLength = this.m_stringLength + value.m_stringLength;
            String result = FastAllocateString(newLength);
            FillSubstring(result, 0, this, 0, startIndex);
            FillSubstring(result, startIndex, value, 0, value.m_stringLength);
            FillSubstring(result, startIndex + value.m_stringLength,
                          this, startIndex, this.m_stringLength - startIndex);
            return result;
        }

        internal unsafe void InsertHoleInString(int startIndex, int holeSize) {
            int tail = this.m_stringLength - startIndex;
            this.m_stringLength += holeSize;
            if (tail > 0) {
                fixed (char *charPtr = &this.m_firstChar) {
                    char *srcPtr = charPtr + startIndex;
                    char *dstPtr = charPtr + holeSize;
                    Buffer.MoveMemory((byte *)dstPtr, (byte *)srcPtr,
                                      tail * sizeof(char));
                }
            }
        }

        internal unsafe void InsertStringOverwrite(String value, int startIndex, int valueLength) {
            fixed (char *charPtr = &this.m_firstChar) {
                char *dstPtr = charPtr + startIndex;
                fixed (char *srcPtr = &value.m_firstChar) {
                    Buffer.MoveMemory((byte *)dstPtr, (byte *)srcPtr,
                                      valueLength * sizeof(char));
                }
            }
        }

        // Replaces all instances of oldChar with newChar.
        //
        //| <include path='docs/doc[@for="String.Replace"]/*' />
        public String Replace(char oldChar, char newChar) {
            // See also Lightning\Src\VM\COMString.cpp::Replace
            String result = FastAllocateString(this.m_stringLength);
            this.Replace(oldChar, newChar, result);
            return result;
        }

        private unsafe void Replace(char oldChar, char newChar, String newString) {
            fixed (char *srcPtr = &this.m_firstChar) {
                fixed (char *destPtr = &newString.m_firstChar) {
                    char *srcCursor = srcPtr;
                    char *destCursor = destPtr;
                    for (int i = this.m_stringLength; i > 0; i--) {
                        char c = *srcCursor;
                        *destCursor = (c == oldChar) ? newChar : c;
                        srcCursor++;
                        destCursor++;
                    }
                }
            }
        }

        // This method contains the same functionality as StringBuilder Replace. The only difference is that
        // a new String has to be allocated since Strings are immutable
        //| <include path='docs/doc[@for="String.Replace1"]/*' />
        public String Replace(String oldValue, String newValue) {
            // See also Lightning\Src\VM\COMString.cpp::ReplaceString
            if (oldValue == null) {
                throw new ArgumentNullException("oldString is null");
            }
            if (newValue == null) {
                newValue = String.Empty;
            }
            if (oldValue.m_stringLength == 0) {
                throw new ArgumentException("oldString is empty string");
            }
            int matchIndex = LocalIndexOfString(oldValue, 0);
            if (matchIndex < 0) {
                return this;
            }
            // Compute a table of where to insert newValue
            int replaceCount = 0;
            int[] replacementTable = new int[(this.m_stringLength - matchIndex) / oldValue.m_stringLength + 1];
            do {
                replacementTable[replaceCount] = matchIndex;
                replaceCount++;
                matchIndex = LocalIndexOfString(oldValue, matchIndex+oldValue.m_stringLength);
            } while (matchIndex >= 0);
            int newLength = this.m_stringLength + replaceCount * (newValue.m_stringLength - oldValue.m_stringLength);
            String result = FastAllocateString(newLength);
            int srcIndex = 0;
            int destIndex = 0;
            for (int replIndex = 0; replIndex < replaceCount; replIndex++) {
                int count = replacementTable[replIndex] - srcIndex;
                FillSubstring(result, destIndex, this, srcIndex, count);
                srcIndex += count + oldValue.m_stringLength;
                destIndex += count;
                FillString(result, destIndex, newValue);
                destIndex += newValue.m_stringLength;
            }
            FillSubstring(result, destIndex, this, srcIndex,
                          this.m_stringLength - srcIndex);
            return result;
        }

        private unsafe int LocalIndexOfString(String pattern, int startPos) {
            fixed (char *stringPtr = &this.m_firstChar) {
                fixed (char *patternPtr = &pattern.m_firstChar) {
                    char *stringCharPtr = stringPtr + startPos;
                    int count = this.m_stringLength - pattern.m_stringLength -
                        startPos + 1;
                    for (int index = 0; index < count; index++) {
                        char *stringCursor = stringCharPtr + index;
                        char *patternCursor = patternPtr;
                        int i = pattern.m_stringLength;
                        while (i > 0 && *stringCursor == *patternCursor) {
                            i--;
                            stringCursor++;
                            patternCursor++;
                        }
                        if (i == 0) {
                            return (startPos + index);
                        }
                    }
                }
            }
            return -1;
        }

        //| <include path='docs/doc[@for="String.Remove"]/*' />
        public String Remove(int startIndex, int count) {
            if (count < 0) {
                throw new ArgumentOutOfRangeException("count is negative");
            }
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (startIndex + count > this.m_stringLength) {
                throw new ArgumentOutOfRangeException("startIndex+count>Length");
            }
            int newLength = this.m_stringLength - count;
            String result = FastAllocateString(newLength);
            FillSubstring(result, 0, this, 0, startIndex);
            FillSubstring(result, startIndex, this, startIndex + count,
                          newLength - startIndex);
            return result;
        }

        internal unsafe void RemoveRange(int startIndex, int count) {
            int tail = this.m_stringLength - startIndex;
            this.m_stringLength -= count;
            if (tail > 0) {
                fixed (char *charPtr = &this.m_firstChar) {
                    char *dstPtr = charPtr + startIndex;
                    char *srcPtr = dstPtr + count;
                    Buffer.MoveMemory((byte *)dstPtr, (byte *)srcPtr,
                                      tail * sizeof(char));
                }
            }
        }

        //| <include path='docs/doc[@for="String.Format"]/*' />
        public static String Format(String format, Object arg0) {
            return Format(format, new Object[] {arg0});
        }

        //| <include path='docs/doc[@for="String.Format1"]/*' />
        public static String Format(String format, Object arg0, Object arg1) {
            return Format(format, new Object[] {arg0, arg1});
        }

        //| <include path='docs/doc[@for="String.Format2"]/*' />
        public static String Format(String format, Object arg0, Object arg1, Object arg2) {
            return Format(format, new Object[] {arg0, arg1, arg2});
        }

        //| <include path='docs/doc[@for="String.Format3"]/*' />
        public static String Format(String format, params Object[] args) {
            if (format == null || args == null)
                throw new ArgumentNullException((format==null)?"format":"args");
            StringBuilder sb = new StringBuilder(format.Length + args.Length * 8);
            sb.AppendFormat(format,args);
            return sb.ToString();
        }

        //| <include path='docs/doc[@for="String.Copy"]/*' />
        public static String Copy (String str) {
            if (str == null) {
                throw new ArgumentNullException("str");
            }

            int length = str.Length;

            String result = FastAllocateString(length);
            FillString(result, 0, str);
            return result;
        }

        // Used by StringBuilder to avoid data corruption
        internal static String InternalCopy (String str) {
            int length = str.Length;
            String result = FastAllocateString(length);
            FillStringEx(result, 0, str, length); // The underlying's String can changed length is StringBuilder
            return result;
        }

        //| <include path='docs/doc[@for="String.Concat"]/*' />
        public static String Concat(Object arg0) {
            if (arg0 == null) {
                return String.Empty;
            }
            return arg0.ToString();
        }

        //| <include path='docs/doc[@for="String.Concat1"]/*' />
        public static String Concat(Object arg0, Object arg1) {
            if (arg0 == null) {
                arg0 = String.Empty;
            }

            if (arg1 == null) {
                arg1 = String.Empty;
            }
            return Concat(arg0.ToString(), arg1.ToString());
        }

        //| <include path='docs/doc[@for="String.Concat2"]/*' />
        public static String Concat(Object arg0, Object arg1, Object arg2) {
            if (arg0 == null) {
                arg0 = String.Empty;
            }

            if (arg1 == null) {
                arg1 = String.Empty;
            }

            if (arg2 == null) {
                arg2 = String.Empty;
            }

            return Concat(arg0.ToString(), arg1.ToString(), arg2.ToString());
        }

        //| <include path='docs/doc[@for="String.Concat4"]/*' />
        public static String Concat(params Object[] args) {
            if (args == null) {
                throw new ArgumentNullException("args");
            }

            String[] sArgs = new String[args.Length];
            int totalLength=0;

            for (int i = 0; i < args.Length; i++) {
                object value = args[i];
                sArgs[i] = ((value==null)?(String.Empty):(value.ToString()));
                totalLength += sArgs[i].Length;
                // check for overflow
                if (totalLength < 0) {
                    throw new OutOfMemoryException();
                }
            }
            return ConcatArray(sArgs, totalLength);
        }


        //| <include path='docs/doc[@for="String.Concat5"]/*' />
        public static String Concat(String str0, String str1) {
            if (str0 == null) {
                if (str1 == null) {
                    return String.Empty;
                }
                return str1;
            }

            if (str1 == null) {
                return str0;
            }

            int str0Length = str0.Length;

            String result = FastAllocateString(str0Length + str1.Length);

            FillStringChecked(result, 0,        str0);
            FillStringChecked(result, str0Length, str1);

            return result;
        }

        //| <include path='docs/doc[@for="String.Concat6"]/*' />
        public static String Concat(String str0, String str1, String str2) {
            if (str0 == null && str1 == null && str2 == null) {
                return String.Empty;
            }

            if (str0 == null) {
                str0 = String.Empty;
            }

            if (str1 == null) {
                str1 = String.Empty;
            }

            if (str2 == null) {
                str2 = String.Empty;
            }

            int totalLength = str0.Length + str1.Length + str2.Length;

            String result = FastAllocateString(totalLength);
            FillStringChecked(result, 0, str0);
            FillStringChecked(result, str0.Length, str1);
            FillStringChecked(result, str0.Length + str1.Length, str2);

            return result;
        }

        //| <include path='docs/doc[@for="String.Concat7"]/*' />
        public static String Concat(String str0, String str1, String str2, String str3) {
            if (str0 == null && str1 == null && str2 == null && str3 == null) {
                return String.Empty;
            }

            if (str0 == null) {
                str0 = String.Empty;
            }

            if (str1 == null) {
                str1 = String.Empty;
            }

            if (str2 == null) {
                str2 = String.Empty;
            }

            if (str3 == null) {
                str3 = String.Empty;
            }

            int totalLength = str0.Length + str1.Length + str2.Length + str3.Length;

            String result = FastAllocateString(totalLength);
            FillStringChecked(result, 0, str0);
            FillStringChecked(result, str0.Length, str1);
            FillStringChecked(result, str0.Length + str1.Length, str2);
            FillStringChecked(result, str0.Length + str1.Length + str2.Length, str3);

            return result;
        }

        private static String ConcatArray(String[] values, int totalLength) {
            String result =  FastAllocateString(totalLength);
            int currPos=0;

            for (int i = 0; i < values.Length; i++) {
                Debug.Assert((currPos + values[i].Length <= totalLength),
                                "[String.ConcatArray](currPos + values[i].Length <= totalLength)");

                FillStringChecked(result, currPos, values[i]);
                currPos+=values[i].Length;
            }

            return result;
        }

        // poor man's varargs for String.Concat: 8 strings
        public static String Concat(object obj0, object obj1, object obj2,
                                    object obj3, string obj4, string obj5,
                                    string obj6, string obj7) {
            String[] strs = new String[8];
            strs[0] = obj0.ToString();
            strs[1] = obj1.ToString();
            strs[2] = obj2.ToString();
            strs[3] = obj3.ToString();
            strs[4] = obj4.ToString();
            strs[5] = obj5.ToString();
            strs[6] = obj6.ToString();
            strs[7] = obj7.ToString();
            return Join(null,strs,0,8);
        }

        private static String[] CopyArrayOnNull(String[] values, out int totalLength) {
            totalLength = 0;

            String[] outValues = new String[values.Length];

            for (int i = 0; i < values.Length; i++) {
                outValues[i] = ((values[i]==null)?String.Empty:values[i]);
                totalLength += outValues[i].Length;
            }
            return outValues;
        }

        //| <include path='docs/doc[@for="String.Concat8"]/*' />
        public static String Concat(params String[] values) {
            int totalLength=0;

            if (values == null) {
                throw new ArgumentNullException("values");
            }

            // Always make a copy to prevent changing the array on another thread.
            String[] internalValues = new String[values.Length];

            for (int i = 0; i < values.Length; i++) {
                string value = values[i];
                internalValues[i] = ((value==null)?(String.Empty):(value));
                totalLength += internalValues[i].Length;
                // check for overflow
                if (totalLength < 0) {
                    throw new OutOfMemoryException();
                }
            }

            return ConcatArray(internalValues, totalLength);
        }

        //| <include path='docs/doc[@for="String.Intern"]/*' />
        public static String Intern(String str) {
            str.CheckHighChars();
            if (str == null) {
                throw new ArgumentNullException("str");
            }
            if (internedStringVector == null) {
                InitializeInternedTable();
            }
            int code = str.GetHashCode();
            lock (internedStringVector) {
                int[] codeTable= internedStringHashCodes;
                String[] stringTable = internedStringVector;
                int tableSize = codeTable.Length;
                int indexMask = tableSize - 1;
                int hx = code & indexMask;
                //Scan up from our initial hash index guess
                while (true) {   // It is guaranteed there are holes in table
                    int tableCode = codeTable[hx];
                    if (tableCode == code) {
                        String s = stringTable[hx];
                        if (str.Equals(s)) {
                            return s;
                        }
                    }
                    else if (tableCode == 0 && stringTable[hx] == null) {
                        // We need to insert the string here!
                        int stringLength = str.Length;
                        if (str.m_arrayLength > stringLength + 1) {
                            str = NewString(str, 0, stringLength, stringLength);
                        }
                        internedStringCount++;
                        stringTable[hx] = str; // Set string entry first
                        codeTable[hx] = code; // then set code!
                        if (internedStringCount >= internedStringBound) {
                            RehashInternedStrings();
                        }
                        return str;
                    }
                    hx++;
                    hx &= indexMask;
                }
            }
        }

        //| <include path='docs/doc[@for="String.IsInterned"]/*' />
        public static String IsInterned(String str) {
            if (str == null) {
                throw new ArgumentNullException("str");
            }
            if (internedStringVector == null) {
                InitializeInternedTable();
            }
            int code = str.GetHashCode();
            int[] codeTable;
            String[] stringTable;
            do {
                codeTable = internedStringHashCodes;
                stringTable = internedStringVector;
            } while (codeTable.Length != stringTable.Length);
            int tableSize = codeTable.Length;
            int indexMask = tableSize - 1;
            int hx = code & indexMask;
            // Scan up from our initial hash index guess
            while (true) {       // It is guaranteed there are holes in table
                int tableCode = codeTable[hx];
                if (tableCode == code) {
                    String s = stringTable[hx];
                    if (str.Equals(s)) {
                        return s;
                    }
                }
                else if (tableCode == 0 && stringTable[hx] == null) {
                    return null;
                }
                hx++;
                hx &= indexMask;
            }
        }

        private static void InitializeInternedTable() {
            lock (typeof(String)) {
                if (internedStringVector != null) {
                    return;
                }
                int tableSize = 128;
                int constantCount = internedStringConstants.Length;
                while (tableSize <= constantCount) {
                    tableSize <<= 1;
                }
                int indexMask = tableSize - 1;
                String[] stringTable = new String[tableSize];
                int[] codeTable = new int[tableSize];
                for (int i = 0; i < constantCount; i++) {
                    String s = internedStringConstants[i];
                    int code = s.GetHashCode();
                    int hx = code & indexMask;
                    while (true) {
                        int tableCode = codeTable[hx];
                        VTable.Assert(tableCode != code ||
                                      !s.Equals(stringTable[hx]),
                                      "Duplicate interned strings!");
                        if (tableCode == 0 && stringTable[hx] == null) {
                            internedStringCount++;
                            stringTable[hx] = s;
                            codeTable[hx] = code;
                            break;
                        }
                        hx++;
                        hx &= indexMask;
                    }
                }
                internedStringBound = tableSize >> 1;
                internedStringHashCodes = codeTable;
                internedStringVector = stringTable;
            }
        }

        private static void RehashInternedStrings() {
            int[] oldCodeTable = internedStringHashCodes;
            String[] oldStringTable = internedStringVector;
            int oldSize = oldCodeTable.Length;
            int oldIndexMask = oldSize - 1;
            int newSize = oldSize << 1;
            int newIndexMask = newSize -1;
            int[] newCodeTable = new int[newSize];
            String[] newStringTable = new String[newSize];
            for (int i = 0; i < oldSize; i++) {
                String s = oldStringTable[i];
                if (s != null) {
                    int code = oldCodeTable[i];
                    int hx = code & newIndexMask;
                    while (true) {
                        if (newCodeTable[hx] == 0 &&
                            newStringTable[hx] == null) {
                            newStringTable[hx] = s;
                            newCodeTable[hx] = code;
                            break;
                        }
                        hx++;
                        hx &= newIndexMask;
                    }
                }
            }
            internedStringBound = newSize >> 1;
            internedStringHashCodes = newCodeTable;
            internedStringVector = newStringTable;
        }

        private static int internedStringCount;
        private static int internedStringBound;
        private static int[] internedStringHashCodes;
        private static String[] internedStringVector;
        private static String[] internedStringConstants;

        private static readonly bool [] HighCharTable = {
            false, // 0x00, 0x0
            true,  // 0x01, .
            true,  // 0x02, .
            true,  // 0x03, .
            true,  // 0x04, .
            true,  // 0x05, .
            true,  // 0x06, .
            true,  // 0x07, .
            true,  // 0x08, .
            false, // 0x09,
            false, // 0x0A,
            false, // 0x0B, .
            false, // 0x0C, .
            false, // 0x0D,
            true,  // 0x0E, .
            true,  // 0x0F, .
            true,  // 0x10, .
            true,  // 0x11, .
            true,  // 0x12, .
            true,  // 0x13, .
            true,  // 0x14, .
            true,  // 0x15, .
            true,  // 0x16, .
            true,  // 0x17, .
            true,  // 0x18, .
            true,  // 0x19, .
            true,  // 0x1A,
            true,  // 0x1B, .
            true,  // 0x1C, .
            true,  // 0x1D, .
            true,  // 0x1E, .
            true,  // 0x1F, .
            false, // 0x20,
            false, // 0x21, !
            false, // 0x22, "
            false, // 0x23, #
            false, // 0x24, $
            false, // 0x25, %
            false, // 0x26, &
            true,  // 0x27, '
            false, // 0x28, (
            false, // 0x29, )
            false, // 0x2A  *
            false, // 0x2B, +
            false, // 0x2C, ,
            true,  // 0x2D, -
            false, // 0x2E, .
            false, // 0x2F, /
            false, // 0x30, 0
            false, // 0x31, 1
            false, // 0x32, 2
            false, // 0x33, 3
            false, // 0x34, 4
            false, // 0x35, 5
            false, // 0x36, 6
            false, // 0x37, 7
            false, // 0x38, 8
            false, // 0x39, 9
            false, // 0x3A, :
            false, // 0x3B, ;
            false, // 0x3C, <
            false, // 0x3D, =
            false, // 0x3E, >
            false, // 0x3F, ?
            false, // 0x40, @
            false, // 0x41, A
            false, // 0x42, B
            false, // 0x43, C
            false, // 0x44, D
            false, // 0x45, E
            false, // 0x46, F
            false, // 0x47, G
            false, // 0x48, H
            false, // 0x49, I
            false, // 0x4A, J
            false, // 0x4B, K
            false, // 0x4C, L
            false, // 0x4D, M
            false, // 0x4E, N
            false, // 0x4F, O
            false, // 0x50, P
            false, // 0x51, Q
            false, // 0x52, R
            false, // 0x53, S
            false, // 0x54, T
            false, // 0x55, U
            false, // 0x56, V
            false, // 0x57, W
            false, // 0x58, X
            false, // 0x59, Y
            false, // 0x5A, Z
            false, // 0x5B, [
            false, // 0x5C, \
            false, // 0x5D, ]
            false, // 0x5E, ^
            false, // 0x5F, _
            false, // 0x60, `
            false, // 0x61, a
            false, // 0x62, b
            false, // 0x63, c
            false, // 0x64, d
            false, // 0x65, e
            false, // 0x66, f
            false, // 0x67, g
            false, // 0x68, h
            false, // 0x69, i
            false, // 0x6A, j
            false, // 0x6B, k
            false, // 0x6C, l
            false, // 0x6D, m
            false, // 0x6E, n
            false, // 0x6F, o
            false, // 0x70, p
            false, // 0x71, q
            false, // 0x72, r
            false, // 0x73, s
            false, // 0x74, t
            false, // 0x75, u
            false, // 0x76, v
            false, // 0x77, w
            false, // 0x78, x
            false, // 0x79, y
            false, // 0x7A, z
            false, // 0x7B, {
            false, // 0x7C, |
            false, // 0x7D, }
            false, // 0x7E, ~
            true,  // 0x7F, 
        };

        //
        // IValue implementation
        //

        //| <include path='docs/doc[@for="String.GetTypeCode"]/*' />
        [NoHeapAllocation]
        public override TypeCode GetTypeCode() {
            return TypeCode.String;
        }

        // Is this a string that can be compared quickly (that is it has only characters > 0x80
        // and not a - or '
        internal bool IsFastSort() {
            return ((StringState & StringState.SpecialSort) != 0);
        }

        internal bool IsSlowSort() {
            return !IsFastSort();
        }

        internal bool IsFastOpsExceptSort() {
            return ((StringState & StringState.SpecialSort) != 0 ||
                    (StringState & StringState.FastOps) != 0);
        }

        internal bool IsFastCasing() {
            return ((StringState & StringState.SpecialSort) != 0 ||
                    (StringState & StringState.FastOps) != 0);
        }

        internal bool IsFastIndex() {
            return ((StringState & StringState.SpecialSort) != 0 ||
                    (StringState & StringState.FastOps) != 0);
        }

        internal bool IsStringStateUndetermined() {
            return (StringState == StringState.Undetermined);
        }

        internal bool HasHighChars() {
            return (StringState == StringState.HighChars);
        }


        /// <summary>
        /// Get or set the string state for this string.
        /// </summary>
        internal unsafe StringState StringState {
            [NoLoggingForUndo]
                get {
                StringState result = MultiUseWord.GetStringState(this);
                return (StringState)result;
            }
            [NoLoggingForUndo]
                set {
                MultiUseWord.SetStringState(this, value);
            }
        }

        internal unsafe StringState CheckHighChars() {
            char c;
            StringState ss = StringState.FastOps;
            int length = m_stringLength;
            fixed(char *charPtr = &this.m_firstChar) {
                for (int i = 0; i < length; i++) {
                    c = charPtr[i];
                    if (c >= 0x80) {
                        StringState = StringState.HighChars;
                        return StringState;
                    }
                    else if (HighCharTable[(int)c]) {
                        ss = StringState.SpecialSort;
                    }
                }
            }

            StringState = ss;
            return StringState;
        }

        ///<internalonly/>
        unsafe internal void SetChar(int index, char value)
        {
#if _DEBUG
            Debug.Assert(ValidModifiableString(), "Modifiable string must not have highChars flags set");
#endif

            //Bounds check and then set the actual bit.
            if ((UInt32)index >= (UInt32)Length)
                throw new ArgumentOutOfRangeException("index", "ArgumentOutOfRange_Index");

            fixed (char *p = &this.m_firstChar) {
                // Set the character.
                p[index] = value;
            }
        }

#if _DEBUG
        // Only used in debug build. Insure that the HighChar state information for a string is not set as known
        [MethodImpl(MethodImplOptions.InternalCall)]
        private bool ValidModifiableString() {
            throw new Exception("System.String.ValidModifiableString not implemented in Bartok!");
        }
#endif

        ///<internalonly/>
        unsafe internal void AppendInPlace(char value,int currentLength)
        {
            Debug.Assert(currentLength < m_arrayLength, "[String.AppendInPlace(char)currentLength < m_arrayLength");
#if _DEBUG
            Debug.Assert(ValidModifiableString(), "Modifiable string must not have highChars flags set");
#endif

            fixed (char *p = &this.m_firstChar)
            {
                // Append the character.
                p[currentLength] = value;
                p[++currentLength] = '\0';
                m_stringLength = currentLength;
            }
        }


        ///<internalonly/>
        unsafe internal void AppendInPlace(char value, int repeatCount, int currentLength)
        {
            Debug.Assert(currentLength+repeatCount < m_arrayLength, "[String.AppendInPlace]currentLength+repeatCount < m_arrayLength");
#if _DEBUG
            Debug.Assert(ValidModifiableString(), "Modifiable string must not have highChars flags set");
#endif

            int newLength = currentLength + repeatCount;


            fixed (char *p = &this.m_firstChar)
            {
                int i;
                for (i = currentLength; i < newLength; i++) {
                    p[i] = value;
                }
                p[i] = '\0';
            }
            this.m_stringLength = newLength;
        }

        ///<internalonly/>
        internal unsafe void AppendInPlace(String value, int currentLength) {
            Debug.Assert(value!=null, "[String.AppendInPlace]value!=null");
            Debug.Assert(value.Length + currentLength < this.m_arrayLength, "[String.AppendInPlace]Length is wrong.");
#if _DEBUG
            Debug.Assert(ValidModifiableString(), "Modifiable string must not have highChars flags set");
#endif

            FillString(this, currentLength, value);
            SetLength(currentLength + value.Length);
            NullTerminate();
        }

        internal void AppendInPlace(String value, int startIndex, int count, int currentLength) {
            Debug.Assert(value!=null, "[String.AppendInPlace]value!=null");
            Debug.Assert(count + currentLength < this.m_arrayLength, "[String.AppendInPlace]count + currentLength < this.m_arrayLength");
            Debug.Assert(count>=0, "[String.AppendInPlace]count>=0");
            Debug.Assert(startIndex>=0, "[String.AppendInPlace]startIndex>=0");
            Debug.Assert(startIndex <= (value.Length - count), "[String.AppendInPlace]startIndex <= (value.Length - count)");
#if _DEBUG
            Debug.Assert(ValidModifiableString(), "Modifiable string must not have highChars flags set");
#endif

            FillSubstring(this, currentLength, value, startIndex, count);
            SetLength(currentLength + count);
            NullTerminate();
        }

        internal unsafe void AppendInPlace(char *value, int count,int currentLength) {
            Debug.Assert(value!=null, "[String.AppendInPlace]value!=null");
            Debug.Assert(count + currentLength < this.m_arrayLength, "[String.AppendInPlace]count + currentLength < this.m_arrayLength");
            Debug.Assert(count>=0, "[String.AppendInPlace]count>=0");
#if _DEBUG
            Debug.Assert(ValidModifiableString(), "Modifiable string must not have highChars flags set");
#endif
            fixed(char *p = &this.m_firstChar) {
                int i;
                for (i = 0; i < count; i++) {
                    p[currentLength+i] = value[i];
                }
            }
            SetLength(currentLength + count);
            NullTerminate();
        }


        ///<internalonly/>
        internal unsafe void AppendInPlace(char[] value, int start, int count, int currentLength) {
            Debug.Assert(value!=null, "[String.AppendInPlace]value!=null");
            Debug.Assert(count + currentLength < this.m_arrayLength, "[String.AppendInPlace]Length is wrong.");
            Debug.Assert(value.Length-count>=start, "[String.AppendInPlace]value.Length-count>=start");
#if _DEBUG
            Debug.Assert(ValidModifiableString(), "Modifiable string must not have highChars flags set");
#endif

            FillStringArray(this, currentLength, value, start, count);
            this.m_stringLength = (currentLength + count);
            this.NullTerminate();
        }


        ///<internalonly/>
        unsafe internal void ReplaceCharInPlace(char oldChar, char newChar, int startIndex, int count,int currentLength) {
            Debug.Assert(startIndex>=0, "[String.ReplaceCharInPlace]startIndex>0");
            Debug.Assert(startIndex<=currentLength, "[String.ReplaceCharInPlace]startIndex>=Length");
            Debug.Assert((startIndex<=currentLength-count), "[String.ReplaceCharInPlace]count>0 && startIndex<=currentLength-count");
#if _DEBUG
            Debug.Assert(ValidModifiableString(), "Modifiable string must not have highChars flags set");
#endif

            int endIndex = startIndex+count;

            fixed (char *p = &this.m_firstChar) {
                for (int i = startIndex; i < endIndex; i++) {
                    if (p[i] == oldChar) {
                        p[i]=newChar;
                    }
                }
            }
        }


        ///<internalonly/>
        internal static String GetStringForStringBuilder(String value, int capacity) {
            Debug.Assert(value!=null, "[String.GetStringForStringBuilder]value!=null");
            Debug.Assert(capacity>=value.Length,  "[String.GetStringForStringBuilder]capacity>=value.Length");

            String newStr = FastAllocateString(capacity);
            if (value.Length == 0) {
                newStr.m_stringLength=0;
                newStr.m_firstChar='\0';
                return newStr;
            }
            FillString(newStr, 0, value);
            newStr.m_stringLength = value.m_stringLength;
            return newStr;
        }

        ///<internalonly/>
        private unsafe void NullTerminate() {
            fixed(char *p = &this.m_firstChar) {
                p[m_stringLength] = '\0';
            }
        }

        ///<internalonly/>
        unsafe internal void ClearPostNullChar() {
            int newLength = Length+1;
            if (newLength < m_arrayLength) {
                fixed(char *p = &this.m_firstChar) {
                    p[newLength] = '\0';
                }
            }
        }

        ///<internalonly/>
        internal void SetLength(int newLength) {
            Debug.Assert(newLength <= m_arrayLength, "newLength<=m_arrayLength");
            m_stringLength = newLength;
        }



        //| <include path='docs/doc[@for="String.GetEnumerator"]/*' />
        public CharEnumerator GetEnumerator() {
            return new CharEnumerator(this);
        }

        //| <include path='docs/doc[@for="String.IEnumerable.GetEnumerator"]/*' />
        /// <internalonly/>
        IEnumerator IEnumerable.GetEnumerator() {
            return new CharEnumerator(this);
        }

        //
        // This is just designed to prevent compiler warnings.
        // This field is used from native, but we need to prevent the compiler warnings.
        //
#if _DEBUG
        private void DontTouchThis() {
            m_arrayLength = 0;
            m_stringLength = 0;
            m_firstChar = m_firstChar;
        }
#endif

        internal unsafe void InternalSetCharNoBoundsCheck(int index, char value) {
            fixed (char *p = &this.m_firstChar) {
                p[index] = value;
            }
        }


#if false // Unused

        // NOTE: len is not the length in characters, but the length in bytes

        // Copies the source String (byte buffer) to the destination IntPtr memory allocated with len bytes.
        internal unsafe static void InternalCopy(String src, IntPtr dest,int len)
        {
            if (len == 0)
                return;
            fixed(char* charPtr = &src.m_firstChar) {
                byte* srcPtr = (byte*) charPtr;
                byte* dstPtr = (byte*) dest.ToPointer();
                Buffer.MoveMemory(dstPtr, srcPtr, len);
            }
        }

        // memcopies characters inside a String.
        internal unsafe static void InternalMemCpy(String src, int srcOffset, String dst, int destOffset, int len)
        {
            if (len == 0)
                return;
            fixed(char* srcPtr = &src.m_firstChar) {
                fixed(char* dstPtr = &dst.m_firstChar) {
                    Buffer.MoveMemory((byte*)(dstPtr + destOffset),
                                      (byte*)(srcPtr + srcOffset),
                                      len);
                }
            }
        }
#endif

        // Copies the source String to the destination byte[]
        internal unsafe static void InternalCopy(String src, byte[] dest, int stringLength)
        {
            if (stringLength == 0)
                return;
            int len = stringLength * sizeof(char);

            Debug.Assert(dest.Length >= len);

            fixed(char* charPtr = &src.m_firstChar) {
                fixed(byte* destPtr = &dest[0]) {
                    byte* srcPtr = (byte*) charPtr;
                    Buffer.MoveMemory(destPtr, srcPtr, len);
                }
            }
        }

        internal unsafe void InsertInPlace(int index, String value, int repeatCount, int currentLength, int requiredLength) {
            Debug.Assert(requiredLength  < m_arrayLength, "[String.InsertString] requiredLength  < m_arrayLength");
            Debug.Assert(index + value.Length * repeatCount < m_arrayLength, "[String.InsertString] index + value.Length * repeatCount < m_arrayLength");
#if _DEBUG
            Debug.Assert(ValidModifiableString(), "Modifiable string must not have highChars flags set");
#endif
            //Copy the old characters over to make room and then insert the new characters.
            fixed(char* srcPtr = &this.m_firstChar) {
                fixed(char* valuePtr = &value.m_firstChar) {
                    Buffer.MoveMemory((byte*)(srcPtr + index + value.Length * repeatCount),
                                   (byte*)(srcPtr + index),
                                   (currentLength - index) * sizeof(char));
                    for (int i = 0; i < repeatCount; i++) {
                        Buffer.MoveMemory((byte*)(srcPtr + index + i * value.Length),
                                       (byte*)valuePtr,
                                       value.Length * sizeof(char));
                    }
                }
                srcPtr[requiredLength] = '\0';
            }
            this.m_stringLength = requiredLength;
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public unsafe int LimitedFormatTo(char *buffer, int length)
        {
            unchecked {
                fixed (char *fmtBeg = &m_firstChar) {
                    char *fmtPtr = fmtBeg;
                    char *fmtEnd = fmtBeg + m_stringLength;

                    char *outPtr = buffer;
                    char *outEnd = buffer + length;

                    while (fmtPtr < fmtEnd && outPtr < outEnd) {
                        *outPtr++ = *fmtPtr++;
                    }
                    return (int)(outPtr - buffer);
                }
            }
        }

        [CLSCompliant(false)]
        [NoHeapAllocation]
        public static unsafe int LimitedFormatTo(String format,
                                                 ArgIterator args,
                                                 char *buffer,
                                                 int length)
        {
            unchecked {

            fixed (char *fmtBeg = &format.m_firstChar) {
                char *fmtPtr = fmtBeg;
                char *fmtEnd = fmtBeg + format.m_stringLength;

                char *outPtr = buffer;
                char *outEnd = buffer + length;

                while (fmtPtr < fmtEnd && outPtr < outEnd) {
                    if (*fmtPtr == '{') {
                        char * fmtPos = fmtPtr;
                        bool bad = false;
                        fmtPtr++;

                        int ndx = 0;
                        int aln = 0;
                        int wid = 0;
                        char fmt = 'd';

                        if (*fmtPtr == '{') {
                            *outPtr++ = *fmtPtr++;
                        }
                        else if (*fmtPtr >= '0' && *fmtPtr <= '9') {

                            // {index,alignment:type width}
                            // Get Index
                            while (*fmtPtr >= '0' && *fmtPtr <= '9') {
                                ndx = ndx * 10 + (*fmtPtr++ - '0');
                            }

                            // Get Alignment
                            if (*fmtPtr == ',') {
                                fmtPtr++;
                                if (*fmtPtr == '-') {
                                    // We just ignore left alignment for now.
                                    fmtPtr++;
                                }
                                while (*fmtPtr >= '0' && *fmtPtr <= '9') {
                                    aln = aln * 10 + (*fmtPtr++ - '0');
                                }
                            }

                            // Get FormatString
                            if (*fmtPtr == ':') {
                                fmtPtr++;
                                if (*fmtPtr >= 'a' && *fmtPtr <= 'z') {
                                    fmt = *fmtPtr++;
                                }
                                else if (*fmtPtr >= 'A' && *fmtPtr <= 'Z') {
                                    fmt = (char)(*fmtPtr++ - ('A' + 'a'));
                                }
                                while (*fmtPtr >= '0' && *fmtPtr <= '9') {
                                    wid = wid * 10 + (*fmtPtr++ - '0');
                                }
                            }

                            // Get closing brace.
                            if (*fmtPtr == '}') {
                                fmtPtr++;
                            }
                            else {
                                bad = true;
                            }

                            if (ndx >= args.Length) {
                                bad = true;
                            }

                            if (bad) {
                                for (; fmtPos < fmtPtr; fmtPos++) {
                                    if (outPtr < outEnd) {
                                        *outPtr++ = *fmtPos;
                                    }
                                }
                            }
                            else {
                                // Get the value
                                char cvalue = '\0';
                                long ivalue = 0;
                                string svalue = null;
                                ulong value = 0;
                                IntPtr pvalue;
                                RuntimeType type;

                                type = args.GetArg(ndx, out pvalue);

                                switch (type.classVtable.structuralView) {
                                    case StructuralType.Bool:
                                        svalue =*(bool *)pvalue ? "true" : "false";
                                        break;
                                    case StructuralType.Char:
                                        cvalue = *(char *)pvalue;
                                        break;
                                    case StructuralType.Int8:
                                        ivalue = *(sbyte *)pvalue;
                                        break;
                                    case StructuralType.Int16:
                                        ivalue = *(short *)pvalue;
                                        break;
                                    case StructuralType.Int32:
                                        ivalue = *(int *)pvalue;
                                        break;
                                    case StructuralType.Int64:
                                        ivalue = *(long *)pvalue;
                                        break;
                                    case StructuralType.UInt8:
                                        value = *(byte *)pvalue;
                                        break;
                                    case StructuralType.UInt16:
                                        value = *(ushort *)pvalue;
                                        break;
                                    case StructuralType.UInt32:
                                        value = *(uint *)pvalue;
                                        break;
                                    case StructuralType.UInt64:
                                        value = *(ulong *)pvalue;
                                        break;
                                    case StructuralType.IntPtr:
                                        value = (ulong)*(IntPtr *)pvalue;
                                        break;
                                    case StructuralType.UIntPtr:
                                        value = (ulong)*(UIntPtr *)pvalue;
                                        break;
                                    case StructuralType.Reference:
                                        if (type == typeof(String)) {
                                            svalue = Magic.toString(
                                                Magic.fromAddress(*(UIntPtr *)pvalue));
                                        }
                                        else {
                                            svalue = type.Name;
                                        }
                                        break;
                                    default:
                                        svalue = "???";
                                        break;
                                }

                                if (cvalue != '\0') {
                                    outPtr = AddChar(outPtr, outEnd, *(char *)pvalue, aln);
                                }
                                else if (svalue != null) {
                                    outPtr = AddString(outPtr, outEnd, svalue, aln);
                                }
                                else {
                                    if (aln < wid) {
                                        aln = wid;
                                    }

                                    if (fmt == 'x') {
                                        if (ivalue != 0) {
                                            value = (ulong)ivalue;
                                        }
                                        outPtr = AddNumber(outPtr, outEnd, value, aln, 16, '0', '\0');
                                    }
                                    else {
                                        char sign = '\0';
                                        if (ivalue < 0) {
                                            sign = '-';
                                            value = unchecked((ulong)-ivalue);
                                        }
                                        else if (ivalue > 0) {
                                            value = unchecked((ulong)ivalue);
                                        }
                                        outPtr = AddNumber(outPtr, outEnd, value, aln, 10, ' ', sign);
                                    }
                                }
                            }
                        }
                    }
                    else if (*fmtPtr == '}') {
                        if (outPtr < outEnd) {
                            *outPtr++ = *fmtPtr;
                        }
                        fmtPtr++;
                    }
                    else {
                        if (outPtr < outEnd) {
                            *outPtr++ = *fmtPtr;
                        }
                        fmtPtr++;
                    }
                }
                return (int)(outPtr - buffer);
            }
            }
        }

        [NoHeapAllocation]
        private static int CountDigits(ulong value, uint valueBase)
        {
            int used = 0;
            do {
                value /= valueBase;
                used++;
            } while (value != 0);

            return used;
        }

        [NoHeapAllocation]
        private static unsafe char * AddNumber(char *output, char *limit,
                                               ulong value, int width, uint valueBase,
                                               char fill, char sign)
        {
            // Make sure we won't overfill the buffer.
            if (output >= limit) {
                return output;
            }

            // Figure out how wide the string will be.
            int used = CountDigits(value, valueBase);

            // Check for overflow.
            if (output + used + ((sign != '\0') ? 1 : 0) > limit) {
                while (width > 0) {
                    *output++ = '#';
                    width--;
                }
                return output;
            }

            // Handle sign and space fill.
            if (sign != '\0' && used < width) {
                if (fill == ' ') {
                    while (width > used + 1) {
                        *output++ = fill;
                        width--;
                    }
                    fill = '\0';
                }
                *output++ = sign;
            }

            // Handle other non-zero fills.
            if (fill != '\0') {
                while (width > used) {
                    *output++ = fill;
                    width--;
                }
            }

            // Write the characters into the buffer.
            char *outp = output + used;
            do {
                uint digit = (uint)(value % valueBase);
                value /= valueBase;

                if (digit >= 0 && digit <= 9) {
                    *--outp = (char)('0' + digit);
                }
                else {
                    *--outp = (char)('a' + (digit - 10));
                }
            } while (value != 0);

            return output + used;
        }

        [NoHeapAllocation]
        private static unsafe char * AddString(char *output, char *limit,
                                               string value, int width)
        {
            fixed (char *pwString = &value.m_firstChar) {
                return AddString(output, limit, pwString, value.m_stringLength, width);
            }
        }

        [NoHeapAllocation]
        private static unsafe char * AddString(char *output, char *limit,
                                               char *pwString, int cwString,
                                               int width)
        {
            // width < 0: left justified at -width.
            // width = 0: no specified width.
            // width > 0: right justified at width.
            if (width == 0) {
                width = cwString;
            }
            else if (width < 0) {
                width = -width;
                for (; width > cwString; width--) {
                    if (output < limit) {
                        *output++ = ' ';
                    }
                }
            }

            while (cwString > 0 && width > 0) {
                if (output < limit) {
                    *output++ = (char)*pwString++;
                }
                width--;
                cwString--;
            }

            for (; width > 0; width--) {
                if (output < limit) {
                    *output++ = ' ';
                }
            }
            return output;
        }

        [NoHeapAllocation]
        private static unsafe char * AddChar(char *output, char *limit, char value, int width)
        {
            // width < 0: left justified at -width.
            // width = 0: no specified width.
            // width > 0: right justified at width.
            if (width == 0) {
                width = 1;
            }
            else if (width < 0) {
                width = -width;
                for (; width > 1; width--) {
                    if (output < limit) {
                        *output++ = ' ';
                    }
                }
            }

            if (width > 0) {
                if (output < limit) {
                    *output++ = (char)value;
                }
                width--;
            }

            for (; width > 0; width--) {
                if (output < limit) {
                    *output++ = ' ';
                }
            }
            return output;
        }
    }
}
