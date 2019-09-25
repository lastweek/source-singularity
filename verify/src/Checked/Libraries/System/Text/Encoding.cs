// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Text
{

    using System;
    using System.Collections;
    using System.Runtime.CompilerServices;
    using System.Globalization;

    // This abstract base class represents a character encoding. The class provides
    // methods to convert arrays and strings of Unicode characters to and from
    // arrays of bytes. A number of Encoding implementations are provided in
    // the System.Text package, including:
    //
    // ASCIIEncoding, which encodes Unicode characters as single 7-bit
    // ASCII characters. This encoding only supports character values between 0x00
    // and 0x7F.
    // UnicodeEncoding, which encodes each Unicode character as two
    // consecutive bytes. Both little-endian (code page 1200) and big-endian (code
    // page 1201) encodings are supported.
    // UTF8Encoding, which encodes Unicode characters using the UTF-8
    // encoding (UTF-8 stands for UCS Transformation Format, 8-bit form). This
    // encoding supports all Unicode character values, and can also be accessed
    // as code page 65001.
    //
    // In addition to directly instantiating Encoding objects, an
    // application can use the ForCodePage, GetASCII,
    // GetDefault, GetUnicode, and GetUTF8
    // methods in this class to obtain encodings.
    //
    // Through an encoding, the GetBytes method is used to convert arrays
    // of characters to arrays of bytes, and the GetChars method is used to
    // convert arrays of bytes to arrays of characters. The GetBytes and
    // GetChars methods maintain no state between conversions, and are
    // generally intended for conversions of complete blocks of bytes and
    // characters in one operation. When the data to be converted is only available
    // in sequential blocks (such as data read from a stream) or when the amount of
    // data is so large that it needs to be divided into smaller blocks, an
    // application may choose to use a Decoder or an Encoder to
    // perform the conversion. Decoders and encoders allow sequential blocks of
    // data to be converted and they maintain the state required to support
    // conversions of data that spans adjacent blocks. Decoders and encoders are
    // obtained using the GetDecoder and GetEncoder methods.
    //
    // The core GetBytes and GetChars methods require the caller
    // to provide the destination buffer and ensure that the buffer is large enough
    // to hold the entire result of the conversion. When using these methods,
    // either directly on an Encoding object or on an associated
    // Decoder or Encoder, an application can use one of two methods
    // to allocate destination buffers.
    //
    // The GetByteCount and GetCharCount methods can be used to
    // compute the exact size of the result of a particular conversion, and an
    // appropriately sized buffer for that conversion can then be allocated.
    // The GetMaxByteCount and GetMaxCharCount methods can be
    // be used to compute the maximum possible size of a conversion of a given
    // number of bytes or characters, and a buffer of that size can then be reused
    // for multiple conversions.
    //
    // The first method generally uses less memory, whereas the second method
    // generally executes faster.
    //
    //| <include path='docs/doc[@for="Encoding"]/*' />
    public abstract class Encoding
    {
        private static Encoding unicodeEncoding;
        private static Encoding bigEndianUnicode;
        private static Encoding utf8Encoding;
        private static Encoding asciiEncoding;
        private static Hashtable encodings;

        internal int m_codePage;

        // Useful for Encodings whose GetPreamble method must return an
        // empty byte array.
        internal static readonly byte[] emptyByteArray = new byte[0];

        //| <include path='docs/doc[@for="Encoding.Encoding"]/*' />
        protected Encoding() : this(0) {
        }

        //| <include path='docs/doc[@for="Encoding.Encoding1"]/*' />
        protected Encoding(int codePage) {
            if (codePage < 0) {
                throw new ArgumentOutOfRangeException("codePage");
            }
            m_codePage = codePage;
        }

        // Converts a byte array from one encoding to another. The bytes in the
        // bytes array are converted from srcEncoding to
        // dstEncoding, and the returned value is a new byte array
        // containing the result of the conversion.
        //
        //| <include path='docs/doc[@for="Encoding.Convert"]/*' />
        public static byte[] Convert(Encoding srcEncoding, Encoding dstEncoding,
                                     byte[] bytes) {
            if (bytes == null)
                throw new ArgumentNullException("bytes");
            return Convert(srcEncoding, dstEncoding, bytes, 0, bytes.Length);
        }

        // Converts a range of bytes in a byte array from one encoding to another.
        // This method converts count bytes from bytes starting at
        // index index from srcEncoding to dstEncoding, and
        // returns a new byte array containing the result of the conversion.
        //
        //| <include path='docs/doc[@for="Encoding.Convert1"]/*' />
        public static byte[] Convert(Encoding srcEncoding, Encoding dstEncoding,
                                     byte[] bytes, int index, int count) {
            if (srcEncoding == null || dstEncoding == null) {
                throw new ArgumentNullException((srcEncoding == null ? "srcEncoding" : "dstEncoding"),
                                                "ArgumentNull_Array");
            }
            if (bytes == null) {
                throw new ArgumentNullException("bytes",
                                                "ArgumentNull_Array");
            }
            return dstEncoding.GetBytes(srcEncoding.GetChars(bytes, index, count));
        }

        //| <include path='docs/doc[@for="Encoding.GetPreamble"]/*' />
        public virtual byte[] GetPreamble()
        {
            return emptyByteArray;
        }

        // Returns an encoding for the ASCII character set. The returned encoding
        // will be an instance of the ASCIIEncoding class.
        //
        //| <include path='docs/doc[@for="Encoding.ASCII"]/*' />
        public static Encoding ASCII {
            get {
                if (asciiEncoding == null) asciiEncoding = new ASCIIEncoding();
                return asciiEncoding;
            }
        }

        // Returns the number of bytes required to encode the given character
        // array.
        //
        //| <include path='docs/doc[@for="Encoding.GetByteCount"]/*' />
        public virtual int GetByteCount(char[] chars) {
            if (chars == null) {
                throw new ArgumentNullException("chars",
                                                "ArgumentNull_Array");
            }
            return GetByteCount(chars, 0, chars.Length);
        }

        //| <include path='docs/doc[@for="Encoding.GetByteCount2"]/*' />
        public virtual int GetByteCount(String s)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            char[] chars = s.ToCharArray();
            return GetByteCount(chars, 0, chars.Length);
        }

        // Returns the number of bytes required to encode a range of characters in
        // a character array.
        //
        //| <include path='docs/doc[@for="Encoding.GetByteCount1"]/*' />
        public abstract int GetByteCount(char[] chars, int index, int count);

        // Returns a byte array containing the encoded representation of the given
        // character array.
        //
        //| <include path='docs/doc[@for="Encoding.GetBytes"]/*' />
        public virtual byte[] GetBytes(char[] chars) {
            if (chars == null) {
                throw new ArgumentNullException("chars",
                                                "ArgumentNull_Array");
            }
            return GetBytes(chars, 0, chars.Length);
        }

        // Returns a byte array containing the encoded representation of a range
        // of characters in a character array.
        //
        //| <include path='docs/doc[@for="Encoding.GetBytes1"]/*' />
        public virtual byte[] GetBytes(char[] chars, int index, int count) {
            byte[] result = new byte[GetByteCount(chars, index, count)];
            GetBytes(chars, index, count, result, 0);
            return result;
        }

        // Encodes a range of characters in a character array into a range of bytes
        // in a byte array. An exception occurs if the byte array is not large
        // enough to hold the complete encoding of the characters. The
        // GetByteCount method can be used to determine the exact number of
        // bytes that will be produced for a given range of characters.
        // Alternatively, the GetMaxByteCount method can be used to
        // determine the maximum number of bytes that will be produced for a given
        // number of characters, regardless of the actual character values.
        //
        //| <include path='docs/doc[@for="Encoding.GetBytes2"]/*' />
        public abstract int GetBytes(char[] chars, int charIndex, int charCount,
                                     byte[] bytes, int byteIndex);

        // Returns a byte array containing the encoded representation of the given
        // string.
        //
        //| <include path='docs/doc[@for="Encoding.GetBytes3"]/*' />
        public virtual byte[] GetBytes(String s) {
            if (s == null) {
                throw new ArgumentNullException("s",
                                                "ArgumentNull_String");
            }
            char[] chars = s.ToCharArray();
            return GetBytes(chars, 0, chars.Length);
        }

        //| <include path='docs/doc[@for="Encoding.GetBytes4"]/*' />
        public virtual int GetBytes(String s, int charIndex, int charCount,
                                    byte[] bytes, int byteIndex)
        {
            if (s == null)
                throw new ArgumentNullException("s");
            return GetBytes(s.ToCharArray(), charIndex, charCount, bytes, byteIndex);
        }

        // Returns the number of characters produced by decoding the given byte
        // array.
        //
        //| <include path='docs/doc[@for="Encoding.GetCharCount"]/*' />
        public virtual int GetCharCount(byte[] bytes) {
            if (bytes == null) {
                throw new ArgumentNullException("bytes",
                                                "ArgumentNull_Array");
            }
            return GetCharCount(bytes, 0, bytes.Length);
        }

        // Returns the number of characters produced by decoding a range of bytes
        // in a byte array.
        //
        //| <include path='docs/doc[@for="Encoding.GetCharCount1"]/*' />
        public abstract int GetCharCount(byte[] bytes, int index, int count);

        // Returns a character array containing the decoded representation of a
        // given byte array.
        //
        //| <include path='docs/doc[@for="Encoding.GetChars"]/*' />
        public virtual char[] GetChars(byte[] bytes) {
            if (bytes == null) {
                throw new ArgumentNullException("bytes",
                                                "ArgumentNull_Array");
            }
            return GetChars(bytes, 0, bytes.Length);
        }

        // Returns a character array containing the decoded representation of a
        // range of bytes in a byte array.
        //
        //| <include path='docs/doc[@for="Encoding.GetChars1"]/*' />
        public virtual char[] GetChars(byte[] bytes, int index, int count) {
            char[] result = new char[GetCharCount(bytes, index, count)];
            GetChars(bytes, index, count, result, 0);
            return result;
        }

        // Decodes a range of bytes in a byte array into a range of characters in a
        // character array. An exception occurs if the character array is not large
        // enough to hold the complete decoding of the bytes. The
        // GetCharCount method can be used to determine the exact number of
        // characters that will be produced for a given range of bytes.
        // Alternatively, the GetMaxCharCount method can be used to
        // determine the maximum number of characters that will be produced for a
        // given number of bytes, regardless of the actual byte values.
        //
        //| <include path='docs/doc[@for="Encoding.GetChars2"]/*' />
        public abstract int GetChars(byte[] bytes, int byteIndex, int byteCount,
                                     char[] chars, int charIndex);

        // Returns a Decoder object for this encoding. The returned object
        // can be used to decode a sequence of bytes into a sequence of characters.
        // Contrary to the GetChars family of methods, a Decoder can
        // convert partial sequences of bytes into partial sequences of characters
        // by maintaining the appropriate state between the conversions.
        //
        // This default implementation returns a Decoder that simply
        // forwards calls to the GetCharCount and GetChars methods to
        // the corresponding methods of this encoding. Encodings that require state
        // to be maintained between successive conversions should override this
        // method and return an instance of an appropriate Decoder
        // implementation.
        //
        //| <include path='docs/doc[@for="Encoding.GetDecoder"]/*' />
        public virtual Decoder GetDecoder() {
            return new DefaultDecoder(this);
        }

        // Returns an encoding for the system's current ANSI code page.
        // Singularity always defaults to UTF8 encoding.
        //
        //| <include path='docs/doc[@for="Encoding.Default"]/*' />
        public static Encoding Default {
            get {
                return UTF8;
            }
        }

        // Returns an Encoder object for this encoding. The returned object
        // can be used to encode a sequence of characters into a sequence of bytes.
        // Contrary to the GetBytes family of methods, an Encoder can
        // convert partial sequences of characters into partial sequences of bytes
        // by maintaining the appropriate state between the conversions.
        //
        // This default implementation returns an Encoder that simply
        // forwards calls to the GetByteCount and GetBytes methods to
        // the corresponding methods of this encoding. Encodings that require state
        // to be maintained between successive conversions should override this
        // method and return an instance of an appropriate Encoder
        // implementation.
        //
        //| <include path='docs/doc[@for="Encoding.GetEncoder"]/*' />
        public virtual Encoder GetEncoder() {
            return new DefaultEncoder(this);
        }

        // Returns the maximum number of bytes required to encode a given number of
        // characters. This method can be used to determine an appropriate buffer
        // size for byte arrays passed to the GetBytes method of this
        // encoding or the GetBytes method of an Encoder for this
        // encoding. All encodings must guarantee that no buffer overflow
        // exceptions will occur if buffers are sized according to the results of
        // this method.
        //
        //| <include path='docs/doc[@for="Encoding.GetMaxByteCount"]/*' />
        public abstract int GetMaxByteCount(int charCount);

        // Returns the maximum number of characters produced by decoding a given
        // number of bytes. This method can be used to determine an appropriate
        // buffer size for character arrays passed to the GetChars method of
        // this encoding or the GetChars method of a Decoder for this
        // encoding. All encodings must guarantee that no buffer overflow
        // exceptions will occur if buffers are sized according to the results of
        // this method.
        //
        //| <include path='docs/doc[@for="Encoding.GetMaxCharCount"]/*' />
        public abstract int GetMaxCharCount(int byteCount);

        // Returns a string containing the decoded representation of a given byte
        // array.
        //
        //| <include path='docs/doc[@for="Encoding.GetString"]/*' />
        public virtual String GetString(byte[] bytes) {
            if (bytes == null) {
                throw new ArgumentNullException("bytes",
                                                "ArgumentNull_Array");
            }
            return new String(GetChars(bytes));
        }

        // Returns a string containing the decoded representation of a range of
        // bytes in a byte array.
        //
        //| <include path='docs/doc[@for="Encoding.GetString1"]/*' />
        public virtual String GetString(byte[] bytes, int index, int count) {
            return new String(GetChars(bytes, index, count));
        }

        // Returns an encoding for Unicode format. The returned encoding will be
        // an instance of the UnicodeEncoding class.
        //
        // It will use little endian byte order, but will detect
        // input in big endian if it finds a byte order mark
        // (see Unicode 2.0 spec).
        //
        //| <include path='docs/doc[@for="Encoding.Unicode"]/*' />
        public static Encoding Unicode {
            get {
                if (unicodeEncoding == null)
                    unicodeEncoding = new UnicodeEncoding(false, true);
                return unicodeEncoding;
            }
        }

        // Returns an encoding for Unicode format. The returned encoding will be
        // an instance of the UnicodeEncoding class.
        //
        // It will use big endian byte order, but will detect
        // input in little endian if it finds a byte order mark
        // (see Unicode 2.0 spec).
        //
        //| <include path='docs/doc[@for="Encoding.BigEndianUnicode"]/*' />
        public static Encoding BigEndianUnicode {
            get {
                if (bigEndianUnicode == null)
                    bigEndianUnicode = new UnicodeEncoding(true, true);
                return bigEndianUnicode;
            }
        }

        // Returns an encoding for the UTF-8 format. The returned encoding will be
        // an instance of the UTF8Encoding class.
        //
        //| <include path='docs/doc[@for="Encoding.UTF8"]/*' />
        public static Encoding UTF8 {
            get {
                if (utf8Encoding == null)
                    utf8Encoding = new UTF8Encoding(true);
                return utf8Encoding;
            }
        }

        //| <include path='docs/doc[@for="Encoding.Equals"]/*' />
        public override bool Equals(Object value) {
            Encoding enc = value as Encoding;
            if (enc != null)
                return (m_codePage == enc.m_codePage);
            return (false);
        }

        //| <include path='docs/doc[@for="Encoding.GetHashCode"]/*' />
        public override int GetHashCode() {
            return m_codePage;
        }

        // Default decoder implementation. The GetCharCount and
        // GetChars methods simply forward to the corresponding methods of
        // the encoding. This implementation is appropriate for encodings that do
        // not require state to be maintained between successive conversions.
        private class DefaultDecoder : Decoder
        {
            private Encoding encoding;

            public DefaultDecoder(Encoding encoding) {
                this.encoding = encoding;
            }

            public override int GetCharCount(byte[] bytes, int index, int count) {
                return encoding.GetCharCount(bytes, index, count);
            }

            public override int GetChars(byte[] bytes, int byteIndex, int byteCount,
                                         char[] chars, int charIndex) {
                return encoding.GetChars(bytes, byteIndex, byteCount,
                                         chars, charIndex);
            }
        }

        // Default encoder implementation. The GetByteCount and
        // GetBytes methods simply forward to the corresponding methods of
        // the encoding. This implementation is appropriate for encodings that do
        // not require state to be maintained between successive conversions.
        private class DefaultEncoder : Encoder
        {
            private Encoding encoding;

            public DefaultEncoder(Encoding encoding) {
                this.encoding = encoding;
            }

            public override int GetByteCount(char[] chars, int index, int count, bool flush) {
                return encoding.GetByteCount(chars, index, count);
            }

            public override int GetBytes(char[] chars, int charIndex, int charCount,
                                         byte[] bytes, int byteIndex, bool flush) {
                return encoding.GetBytes(chars, charIndex, charCount,
                                         bytes, byteIndex);
            }
        }
    }
}
