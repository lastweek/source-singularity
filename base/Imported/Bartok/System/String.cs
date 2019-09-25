// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*============================================================
**
** Class:  String
**
** Purpose: Contains headers for the String class.  Actual implementations
** are in String.cpp
**
===========================================================*/
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
    // The String class represents a static string of characters.
    //
    //| <include path='docs/doc[@for="String"]/*' />
    [CCtorIsRunDuringStartup]
    [AccessedByRuntime("referenced from c++")]
    public sealed partial class String : IComparable, IEnumerable {

        //
        //NOTE NOTE NOTE NOTE
        //These fields map directly onto the fields in an EE StringObject.  See object.h for the layout.
        //Be careful changing these fields or adding any new fields.
        //
        [RequiredByBartok]
        private int  m_arrayLength;
        [AccessedByRuntime("referenced from c++")]
        private int  m_stringLength;
        [AccessedByRuntime("referenced from c++")]
        private char m_firstChar;

        //private static readonly char FmtMsgMarkerChar='%';
        //private static readonly char FmtMsgFmtCodeChar='!';
        //These are defined in Com99/src/vm/COMStringCommon.h and must be kept in sync.
        private const int TrimHead = 0;
        private const int TrimTail = 1;
        private const int TrimBoth = 2;

        // The Empty constant holds the empty string value.
        //We need to call the String constructor so that the compiler doesn't mark this as a literal.
        //Marking this as a literal would mean that it doesn't show up as a field which we can access
        //from native.
        //| <include path='docs/doc[@for="String.Empty"]/*' />
        public static readonly String Empty = "";

        //
        // Constructors
        //

        // Creates a new string with the characters copied in from ptr. If
        // ptr is null, a string initialized to ";<;No Object>;"; (i.e.,
        // String.NullString) is created.
        //
        // Issue: This method is only accessible from VC.
        //| <include path='docs/doc[@for="String.String"]/*' />
        [CLSCompliant(false), MethodImpl(MethodImplOptions.InternalCall)]
        unsafe public extern String(char *value);
        //| <include path='docs/doc[@for="String.String1"]/*' />
        [CLSCompliant(false), MethodImpl(MethodImplOptions.InternalCall)]
        unsafe public extern String(char *value, int startIndex, int length);

        //| <include path='docs/doc[@for="String.String2"]/*' />
        [CLSCompliant(false), MethodImpl(MethodImplOptions.InternalCall)]
        unsafe public extern String(sbyte *value);
        //| <include path='docs/doc[@for="String.String3"]/*' />
        [CLSCompliant(false), MethodImpl(MethodImplOptions.InternalCall)]
        unsafe public extern String(sbyte *value, int startIndex, int length);

        // Creates a new string from the characters in a subarray.  The new string will
        // be created from the characters in value between startIndex and
        // startIndex + length - 1.
        //
        //| <include path='docs/doc[@for="String.String7"]/*' />
        [MethodImpl(MethodImplOptions.InternalCall)]
        public extern String(char [] value, int startIndex, int length);

        // Creates a new string from the characters in a subarray.  The new string will be
        // created from the characters in value.
        //
        //| <include path='docs/doc[@for="String.String5"]/*' />
        [MethodImpl(MethodImplOptions.InternalCall)]
        public extern String(char [] value);

        //| <include path='docs/doc[@for="String.String6"]/*' />
        [MethodImpl(MethodImplOptions.InternalCall)]
        public extern String(char c, int count);

        /**
         * Creates a new string with the characters copied in from <i>ptr</i>. If
         * <i>ptr</i> is null, a string initialized to
         * &quot;&lt;No Object&gt;&quot; (i.e., <code>String.NullString</code>)
         * is created.
         *
         * Issue: This method is only accessible from VC.
         * @issue The verifier needs to recognize that this is not necessarily
         *  secure.
         *
         * @param ptr this is a WCHAR *.
         *
         */
        //| <include path='docs/doc[@for="String.String"]/*' />
        [CLSCompliant(false)]
        public unsafe static String StringCTOR(char *valuePtr) {
            // See also Lightning\Src\VM\COMString.cpp::StringInitWCHARPtr
            if (valuePtr == null) {
                return String.Empty;
            }
            // First figure out how many characters the string has
            int count = 0;
            char *cursor = valuePtr;
            int c = *cursor;
            while (c != 0) {
                count++;
                cursor++;
                c = *cursor;
            }
            // Allocate and fill in the string object
            if (count == 0) {
                return String.Empty;
            }
            else {
                String result = FastAllocateString(count);
                FillStringCharPtr(result, 0, valuePtr, count);
                return result;
            }
        }

        //| <include path='docs/doc[@for="String.String1"]/*' />
        [CLSCompliant(false)]
        public unsafe static String StringCTOR(char *valuePtr, int startIndex,
                                               int length) {
            // See also Lightning\Src\VM\COMString.cpp::StringInitWCHARPtrPartial
            if (valuePtr == null) {
                return String.Empty;
            }
            if (length < 0) {
                throw new ArgumentOutOfRangeException("length is negative");
            }
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (length == 0) {
                return String.Empty;
            }
            else {
                String result = FastAllocateString(length);
                FillStringCharPtr(result, 0, valuePtr + startIndex, length);
                return result;
            }
        }

        //| <include path='docs/doc[@for="String.String1"]/*' />
        [CLSCompliant(false)]
        public unsafe static String StringCTOR(byte *valuePtr, int startIndex,
                                               int length) {
            // See also Lightning\Src\VM\COMString.cpp::StringInitWCHARPtrPartial
            if (valuePtr == null) {
                return String.Empty;
            }
            if (length < 0) {
                throw new ArgumentOutOfRangeException("length is negative");
            }
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (length == 0) {
                return String.Empty;
            }
            else {
                String result = FastAllocateString(length);
                FillStringBytePtr(result, 0, valuePtr + startIndex, length);
                return result;
            }
        }

        //| <include path='docs/doc[@for="String.String2"]/*' />
        [CLSCompliant(false)]
        public unsafe static String StringCTOR(sbyte *valuePtr) {
            // See also Lightning\Src\VM\COMString.cpp::StringInitCharPtr
            return StringInitCharHelper(valuePtr, -1);
        }

        //| <include path='docs/doc[@for="String.String3"]/*' />
        [CLSCompliant(false)]
        public unsafe static String StringCTOR(sbyte *valuePtr, int startIndex,
                                               int length) {
            // See also Lightning\Src\VM\COMString.cpp::StringInitCharPtrPartial
            if (startIndex < 0) {
                throw new ArgumentOutOfRangeException("startIndex is negative");
            }
            if (length < 0) {
                throw new ArgumentOutOfRangeException("length is negative");
            }
            return StringInitCharHelper(valuePtr + startIndex, length);
        }

        private unsafe static String StringInitCharHelper(sbyte *valuePtr,
                                                          int length) {
            // See also Lightning\Src\VM\COMString.cpp::StringInitCharHelper
            throw new Exception("StringInitCharHelper is not implemented in Bartok!");
        }

        //
        // Other special methods
        //

        /// This is an EE implemented function so that the JIT can recognise it and
        /// treat it specially by eliminating checks on character fetches.
        [NoHeapAllocation]
        private int InternalLength() {
            // See also Lightning\Src\VM\COMString.cpp::Length
            // See also Lightning\Src\VM\object.h::GetStringLength
            return this.m_stringLength;
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

    }
}
