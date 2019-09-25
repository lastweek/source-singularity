//------------------------------------------------------------------------------
// <copyright file="httpserverutility.cs" company="Microsoft">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//------------------------------------------------------------------------------

namespace System.Web
{
    using System.Text;
    using System.Threading;
    using System.IO;
    using System.Collections;
    using System.Globalization;
    using System.Web.Hosting;
    using System.Diagnostics;

    //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility"]/*' />
    /// <devdoc>
    /// </devdoc>
    public sealed class HttpUtility {

        //
        // NOTE: Various entire chunks of functionality are not included in
        // this port. In fact, only URL encoding/decoding is available.
        //

        //////////////////////////////////////////////////////////////////////////
        //
        //  URL decoding / encoding
        //
        //////////////////////////////////////////////////////////////////////////

        //
        //  Public static methods
        //

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncode"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static string UrlEncode(string str) {
            if (str == null)
                return null;
            return UrlEncode(str, Encoding.UTF8);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlPathEncode"]/*' />
        /// <devdoc>
        ///    <para>
        ///       URL encodes a path portion of a URL string and returns the encoded string.
        ///    </para>
        /// </devdoc>
        public static string UrlPathEncode(string str) {
            if (str == null)
                return null;

            // recurse in case there is a query string
            int i = str.IndexOf('?');
            if (i >= 0)
                return UrlPathEncode(str.Substring(0, i)) + str.Substring(i);

            // encode DBCS characters and spaces only
            return UrlEncodeSpaces(UrlEncodeNonAscii(str, Encoding.UTF8));
        }

        internal static string AspCompatUrlEncode(string s) {
            s = UrlEncode(s);
            s = s.Replace("!", "%21");
            s = s.Replace("*", "%2A");
            s = s.Replace("(", "%28");
            s = s.Replace(")", "%29");
            s = s.Replace("-", "%2D");
            s = s.Replace(".", "%2E");
            s = s.Replace("_", "%5F");
            s = s.Replace("\\", "%5C");
            return s;
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncode1"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static string UrlEncode(string str, Encoding e) {
            if (str == null)
                return null;
            return Encoding.ASCII.GetString(UrlEncodeToBytes(str, e));
        }

        //  Helper to encode the non-ASCII url characters only
        internal static String UrlEncodeNonAscii(string str, Encoding e) {
            if (str == null || str.Length == 0)
                return str;
            if (e == null)
                e = Encoding.UTF8;
            byte[] bytes = e.GetBytes(str);
            bytes = UrlEncodeBytesToBytesInternalNonAscii(bytes, 0, bytes.Length, false);
            return Encoding.ASCII.GetString(bytes);
        }

        //  Helper to encode spaces only
        internal static String UrlEncodeSpaces(string str) {
            if (str != null && str.IndexOf(' ') >= 0)
                str = str.Replace(" ", "%20");
            return str;
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncode2"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static string UrlEncode(byte[] bytes) {
            if (bytes == null)
                return null;
            return Encoding.ASCII.GetString(UrlEncodeToBytes(bytes));
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncode3"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static string UrlEncode(byte[] bytes, int offset, int count) {
            if (bytes == null)
                return null;
            return Encoding.ASCII.GetString(UrlEncodeToBytes(bytes, offset, count));
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncodeToBytes"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static byte[] UrlEncodeToBytes(string str) {
            if (str == null)
                return null;
            return UrlEncodeToBytes(str, Encoding.UTF8);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncodeToBytes1"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static byte[] UrlEncodeToBytes(string str, Encoding e) {
            if (str == null)
                return null;
            byte[] bytes = e.GetBytes(str);
            return UrlEncodeBytesToBytesInternal(bytes, 0, bytes.Length, false);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncodeToBytes2"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static byte[] UrlEncodeToBytes(byte[] bytes) {
            if (bytes == null)
                return null;
            return UrlEncodeToBytes(bytes, 0, bytes.Length);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncodeToBytes3"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static byte[] UrlEncodeToBytes(byte[] bytes, int offset, int count) {
            if (bytes == null && count == 0)
                return null;
            if (bytes == null) {
                throw new ArgumentNullException("bytes");
            }
            if (offset < 0 || offset > bytes.Length) {
                throw new ArgumentOutOfRangeException("offset");
            }
            if (count < 0 || offset + count > bytes.Length) {
                throw new ArgumentOutOfRangeException("count");
            }
            return UrlEncodeBytesToBytesInternal(bytes, offset, count, true);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncodeUnicode"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static string UrlEncodeUnicode(string str) {
            if (str == null)
                return null;
            return UrlEncodeUnicodeStringToStringInternal(str, false);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlEncodeUnicodeToBytes"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static byte[] UrlEncodeUnicodeToBytes(string str) {
            if (str == null)
                return null;
            return Encoding.ASCII.GetBytes(UrlEncodeUnicode(str));
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlDecode"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static string UrlDecode(string str) {
            if (str == null)
                return null;
            return UrlDecode(str, Encoding.UTF8);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlDecode1"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static string UrlDecode(string str, Encoding e) {
            if (str == null)
                return null;
            return UrlDecodeStringFromStringInternal(str, e);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlDecode2"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static string UrlDecode(byte[] bytes, Encoding e) {
            if (bytes == null)
                return null;
            return UrlDecode(bytes, 0, bytes.Length, e);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlDecode3"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static string UrlDecode(byte[] bytes, int offset, int count, Encoding e) {
            if (bytes == null && count == 0)
                return null;
            if (bytes == null) {
                throw new ArgumentNullException("bytes");
            }
            if (offset < 0 || offset > bytes.Length) {
                throw new ArgumentOutOfRangeException("offset");
            }
            if (count < 0 || offset + count > bytes.Length) {
                throw new ArgumentOutOfRangeException("count");
            }
            return UrlDecodeStringFromBytesInternal(bytes, offset, count, e);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlDecodeToBytes"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static byte[] UrlDecodeToBytes(string str) {
            if (str == null)
                return null;
            return UrlDecodeToBytes(str, Encoding.UTF8);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlDecodeToBytes1"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static byte[] UrlDecodeToBytes(string str, Encoding e) {
            if (str == null)
                return null;
            return UrlDecodeToBytes(e.GetBytes(str));
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlDecodeToBytes2"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static byte[] UrlDecodeToBytes(byte[] bytes) {
            if (bytes == null)
                return null;
            return UrlDecodeToBytes(bytes, 0, (bytes != null) ? bytes.Length : 0);
        }

        //| <include file='doc\httpserverutility.uex' path='docs/doc[@for="HttpUtility.UrlDecodeToBytes3"]/*' />
        /// <devdoc>
        ///    <para>[To be supplied.]</para>
        /// </devdoc>
        public static byte[] UrlDecodeToBytes(byte[] bytes, int offset, int count) {
            if (bytes == null && count == 0)
                return null;
            if (bytes == null) {
                throw new ArgumentNullException("bytes");
            }
            if (offset < 0 || offset > bytes.Length) {
                throw new ArgumentOutOfRangeException("offset");
            }
            if (count < 0 || offset + count > bytes.Length) {
                throw new ArgumentOutOfRangeException("count");
            }
            return UrlDecodeBytesFromBytesInternal(bytes, offset, count);
        }

        //
        //  Implementation for encoding
        //

        private static byte[] UrlEncodeBytesToBytesInternal(byte[] bytes, int offset, int count, bool alwaysCreateReturnValue) {
            int cSpaces = 0;
            int cUnsafe = 0;

            // count them first
            for (int i = 0; i < count; i++) {
                char ch = (char)bytes[offset+i];

                if (ch == ' ')
                    cSpaces++;
                else if (!IsSafe(ch))
                    cUnsafe++;
            }

            // nothing to expand?
            if (!alwaysCreateReturnValue && cSpaces == 0 && cUnsafe == 0)
                return bytes;

            // expand not 'safe' characters into %XX, spaces to +s
            byte[] expandedBytes = new byte[count + cUnsafe*2];
            int pos = 0;

            for (int i = 0; i < count; i++) {
                byte b = bytes[offset+i];
                char ch = (char)b;

                if (IsSafe(ch)) {
                    expandedBytes[pos++] = b;
                }
                else if (ch == ' ') {
                    expandedBytes[pos++] = (byte)'+';
                }
                else {
                    expandedBytes[pos++] = (byte)'%';
                    expandedBytes[pos++] = (byte)IntToHex((b >> 4) & 0xf);
                    expandedBytes[pos++] = (byte)IntToHex(b & 0x0f);
                }
            }

            return expandedBytes;
        }

        private static byte[] UrlEncodeBytesToBytesInternalNonAscii(byte[] bytes, int offset, int count, bool alwaysCreateReturnValue) {
            int cNonAscii = 0;

            // count them first
            for (int i = 0; i < count; i++) {
                if ((bytes[offset + i] & 0x80) != 0)
                    cNonAscii++;
            }

            // nothing to expand?
            if (!alwaysCreateReturnValue && cNonAscii == 0)
                return bytes;

            // expand not 'safe' characters into %XX, spaces to +s
            byte[] expandedBytes = new byte[count + cNonAscii*2];
            int pos = 0;

            for (int i = 0; i < count; i++) {
                byte b = bytes[offset+i];

                if ((bytes[offset + i] & 0x80) == 0) {
                    expandedBytes[pos++] = b;
                }
                else {
                    expandedBytes[pos++] = (byte)'%';
                    expandedBytes[pos++] = (byte)IntToHex((b >> 4) & 0xf);
                    expandedBytes[pos++] = (byte)IntToHex(b & 0x0f);
                }
            }

            return expandedBytes;
        }


        private static string UrlEncodeUnicodeStringToStringInternal(string s, bool ignoreAscii) {
            int l = s.Length;
            StringBuilder sb = new StringBuilder(l);

            for (int i = 0; i < l; i++) {
                char ch = s[i];

                if ((ch & 0xff80) == 0) { // 7 bit?
                    if (ignoreAscii || IsSafe(ch)) {
                        sb.Append(ch);
                    }
                    else if (ch == ' ') {
                        sb.Append('+');
                    }
                    else {
                        sb.Append('%');
                        sb.Append(IntToHex((ch >>  4) & 0xf));
                        sb.Append(IntToHex((ch      ) & 0xf));
                    }
                }
                else { // arbitrary Unicode?
                    sb.Append("%u");
                    sb.Append(IntToHex((ch >> 12) & 0xf));
                    sb.Append(IntToHex((ch >>  8) & 0xf));
                    sb.Append(IntToHex((ch >>  4) & 0xf));
                    sb.Append(IntToHex((ch      ) & 0xf));
                }
            }

            return sb.ToString();
        }

        //
        //  Implementation for decoding
        //

        // Internal class to facilitate URL decoding -- keeps char buffer and byte buffer, allows appending of either chars or bytes
        private class UrlDecoder {
            private int _bufferSize;

            // Accumulate characters in a special array
            private int _numChars;
            private char[] _charBuffer;

            // Accumulate bytes for decoding into characters in a special array
            private int _numBytes;
            private byte[] _byteBuffer;

            // Encoding to convert chars to bytes
            private Encoding _encoding;

            private void FlushBytes() {
                if (_numBytes > 0) {
                    _numChars += _encoding.GetChars(_byteBuffer, 0, _numBytes, _charBuffer, _numChars);
                    _numBytes = 0;
                }
            }

            internal UrlDecoder(int bufferSize, Encoding encoding) {
                _bufferSize = bufferSize;
                _encoding = encoding;

                _charBuffer = new char[bufferSize];
                // byte buffer created on demand
            }

            internal void AddChar(char ch) {
                if (_numBytes > 0)
                    FlushBytes();

                _charBuffer[_numChars++] = ch;
            }

            internal void AddByte(byte b) {
                // if there are no pending bytes treat 7 bit bytes as characters
                // this optimization is temp disable as it doesn't work for some encodings
//
//              if (_numBytes == 0 && ((b & 0x80) == 0)) {
//                  AddChar((char)b);
//              }
//              else
//
                {
                    if (_byteBuffer == null)
                        _byteBuffer = new byte[_bufferSize];

                    _byteBuffer[_numBytes++] = b;
                }
            }

            internal String GetString() {
                if (_numBytes > 0)
                    FlushBytes();

                if (_numChars > 0)
                    return new String(_charBuffer, 0, _numChars);
                else
                    return String.Empty;
            }
        }

        internal static string CollapsePercentUFromStringInternal(string s, Encoding e) {
            int count = s.Length;
            UrlDecoder helper = new UrlDecoder(count, e);

            // go through the string's chars collapsing just %uXXXX and
            // appending each char as char
            int loc = s.IndexOf("%u");
            if (loc == -1) {
                return s;
            }

            for (int pos = 0; pos < count; pos++) {
                char ch = s[pos];

                if (ch == '%' && pos < count - 5) {
                    if (s[pos + 1] == 'u') {
                        int h1 = HexToInt(s[pos+2]);
                        int h2 = HexToInt(s[pos+3]);
                        int h3 = HexToInt(s[pos+4]);
                        int h4 = HexToInt(s[pos+5]);

                        if (h1 >= 0 && h2 >= 0 && h3 >= 0 && h4 >= 0) { //valid 4 hex chars
                            ch = (char)((h1 << 12) | (h2 << 8) | (h3 << 4) | h4);
                            pos += 5;

                            // add as char
                            helper.AddChar(ch);
                            continue;
                        }
                    }
                }
                if ((ch & 0xFF80) == 0)
                    helper.AddByte((byte)ch); // 7 bit have to go as bytes because of Unicode
                else
                    helper.AddChar(ch);
            }
            return helper.GetString();
        }

        private static string UrlDecodeStringFromStringInternal(string s, Encoding e) {
            int count = s.Length;
            UrlDecoder helper = new UrlDecoder(count, e);

            // go through the string's chars collapsing %XX and %uXXXX and
            // appending each char as char, with exception of %XX constructs
            // that are appended as bytes

            for (int pos = 0; pos < count; pos++) {
                char ch = s[pos];

                if (ch == '+') {
                    ch = ' ';
                }
                else if (ch == '%' && pos < count - 2) {
                    if (s[pos + 1] == 'u' && pos < count - 5) {
                        int h1 = HexToInt(s[pos+2]);
                        int h2 = HexToInt(s[pos+3]);
                        int h3 = HexToInt(s[pos+4]);
                        int h4 = HexToInt(s[pos+5]);

                        if (h1 >= 0 && h2 >= 0 && h3 >= 0 && h4 >= 0) {  // valid 4 hex chars
                            ch = (char)((h1 << 12) | (h2 << 8) | (h3 << 4) | h4);
                            pos += 5;

                            // only add as char
                            helper.AddChar(ch);
                            continue;
                        }
                    }
                    else {
                        int h1 = HexToInt(s[pos+1]);
                        int h2 = HexToInt(s[pos+2]);

                        if (h1 >= 0 && h2 >= 0) {    // valid 2 hex chars
                            byte b = (byte)((h1 << 4) | h2);
                            pos += 2;

                            // don't add as char
                            helper.AddByte(b);
                            continue;
                        }
                    }
                }

                if ((ch & 0xFF80) == 0)
                    helper.AddByte((byte)ch); // 7 bit have to go as bytes because of Unicode
                else
                    helper.AddChar(ch);
            }

            return helper.GetString();
        }

        private static string UrlDecodeStringFromBytesInternal(byte[] buf, int offset, int count, Encoding e) {
            UrlDecoder helper = new UrlDecoder(count, e);

            // go through the bytes collapsing %XX and %uXXXX and appending
            // each byte as byte, with exception of %uXXXX constructs that
            // are appended as chars

            for (int i = 0; i < count; i++) {
                int pos = offset + i;
                byte b = buf[pos];

                // The code assumes that + and % cannot be in multibyte sequence

                if (b == '+') {
                    b = (byte)' ';
                }
                else if (b == '%' && i < count - 2) {
                    if (buf[pos + 1] == 'u' && i < count - 5) {
                        int h1 = HexToInt((char)buf[pos+2]);
                        int h2 = HexToInt((char)buf[pos+3]);
                        int h3 = HexToInt((char)buf[pos+4]);
                        int h4 = HexToInt((char)buf[pos+5]);

                        if (h1 >= 0 && h2 >= 0 && h3 >= 0 && h4 >= 0) {  // valid 4 hex chars
                            char ch = (char)((h1 << 12) | (h2 << 8) | (h3 << 4) | h4);
                            i += 5;

                            // don't add as byte
                            helper.AddChar(ch);
                            continue;
                        }
                    }
                    else {
                        int h1 = HexToInt((char)buf[pos+1]);
                        int h2 = HexToInt((char)buf[pos+2]);

                        if (h1 >= 0 && h2 >= 0) {    // valid 2 hex chars
                            b = (byte)((h1 << 4) | h2);
                            i += 2;
                        }
                    }
                }

                helper.AddByte(b);
            }

            return helper.GetString();
        }

        private static byte[] UrlDecodeBytesFromBytesInternal(byte[] buf, int offset, int count) {
            int decodedBytesCount = 0;
            byte[] decodedBytes = new byte[count];

            for (int i = 0; i < count; i++) {
                int pos = offset + i;
                byte b = buf[pos];

                if (b == '+') {
                    b = (byte)' ';
                }
                else if (b == '%' && i < count - 2) {
                    int h1 = HexToInt((char)buf[pos+1]);
                    int h2 = HexToInt((char)buf[pos+2]);

                    if (h1 >= 0 && h2 >= 0) {    // valid 2 hex chars
                        b = (byte)((h1 << 4) | h2);
                        i += 2;
                    }
                }

                decodedBytes[decodedBytesCount++] = b;
            }

            if (decodedBytesCount < decodedBytes.Length) {
                byte[] newDecodedBytes = new byte[decodedBytesCount];
                Array.Copy(decodedBytes, newDecodedBytes, decodedBytesCount);
                decodedBytes = newDecodedBytes;
            }

            return decodedBytes;
        }

        //
        // Private helpers for URL encoding/decoding
        //

        private static int HexToInt(char h) {
            return( h >= '0' && h <= '9' ) ? h - '0' :
            ( h >= 'a' && h <= 'f' ) ? h - 'a' + 10 :
            ( h >= 'A' && h <= 'F' ) ? h - 'A' + 10 :
            -1;
        }

        private static char IntToHex(int n) {
            Debug.Assert(n < 0x10);

            if (n <= 9)
                return(char)(n + (int)'0');
            else
                return(char)(n - 10 + (int)'a');
        }

        // Set of safe chars, from RFC 1738.4 minus '+'
        private static bool IsSafe(char ch) {
            if (ch >= 'a' && ch <= 'z' || ch >= 'A' && ch <= 'Z' || ch >= '0' && ch <= '9')
                return true;

            switch (ch) {
                case '-':
                case '_':
                case '.':
                case '!':
                case '*':
                case '\'':
                case '(':
                case ')':
                    return true;
            }

            return false;
        }
    }
}
