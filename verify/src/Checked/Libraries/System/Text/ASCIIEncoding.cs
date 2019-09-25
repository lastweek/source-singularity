// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Text
{
    using System.Text;
    using System;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="ASCIIEncoding"]/*' />
    public partial class ASCIIEncoding : Encoding
    {
        private const int ASCII_CODEPAGE=20127;

        //| <include path='docs/doc[@for="ASCIIEncoding.ASCIIEncoding"]/*' />
        public ASCIIEncoding() : base(ASCII_CODEPAGE) {
        }

        //| <include path='docs/doc[@for="ASCIIEncoding.GetByteCount"]/*' />
        public override int GetByteCount(char[] chars, int index, int count) {
            if (chars == null) {
                throw new ArgumentNullException("chars", "ArgumentNull_Array");
            }
            if (index < 0 || count < 0) {
                throw new ArgumentOutOfRangeException((index<0 ? "index" : "count"),
                    "ArgumentOutOfRange_NeedNonNegNum");
            }
            if (chars.Length - index < count) {
                throw new ArgumentOutOfRangeException("chars",
                      "ArgumentOutOfRange_IndexCountBuffer");
            }

            return (count);
        }

        //| <include path='docs/doc[@for="ASCIIEncoding.GetByteCount1"]/*' />
        public override int GetByteCount(String chars) {
            if (chars == null) {
                throw new ArgumentNullException("chars", "ArgumentNull_Array");
            }
            return chars.Length;
        }

         //| <include path='docs/doc[@for="ASCIIEncoding.GetBytes"]/*' />
        public override int GetBytes(char[] chars, int charIndex, int charCount,
            byte[] bytes, int byteIndex) {
            if (chars == null || bytes == null) {
                throw new ArgumentNullException((chars == null ? "chars" : "bytes"),
                      "ArgumentNull_Array");
            }
            if (charIndex < 0 || charCount < 0) {
                throw new ArgumentOutOfRangeException((charIndex<0 ? "charIndex" : "charCount"),
                      "ArgumentOutOfRange_NeedNonNegNum");
            }
            if (chars.Length - charIndex < charCount) {
                throw new ArgumentOutOfRangeException("chars",
                      "ArgumentOutOfRange_IndexCountBuffer");
            }
            if (byteIndex < 0 || byteIndex > bytes.Length) {
                throw new ArgumentOutOfRangeException("byteIndex",
                    "ArgumentOutOfRange_Index");
            }
            if (bytes.Length - byteIndex < charCount) {
                throw new ArgumentException("Argument_ConversionOverflow");
            }
            int charEnd = charIndex + charCount;

            while (charIndex < charEnd) {
                char ch = chars[charIndex++];
                if (ch >= 0x0080) ch = '?';
                bytes[byteIndex++] = (byte)ch;
            }
            return charCount;
        }

        //| <include path='docs/doc[@for="ASCIIEncoding.GetBytes1"]/*' />
        public override int GetBytes(String chars, int charIndex, int charCount,
            byte[] bytes, int byteIndex) {
            if (chars == null || bytes == null) {
                throw new ArgumentNullException((chars == null ? "chars" : "bytes"),
                      "ArgumentNull_Array");
            }
            if (charIndex < 0 || charCount < 0) {
                throw new ArgumentOutOfRangeException((charIndex<0 ? "charIndex" : "charCount"),
                      "ArgumentOutOfRange_NeedNonNegNum");
            }
            if (chars.Length - charIndex < charCount) {
                throw new ArgumentOutOfRangeException("chars",
                      "ArgumentOutOfRange_IndexCount");
            }
            if (byteIndex < 0 || byteIndex > bytes.Length) {
                throw new ArgumentOutOfRangeException("byteIndex",
                    "ArgumentOutOfRange_Index");
            }
            if (bytes.Length - byteIndex < charCount) {
                throw new ArgumentException("Argument_ConversionOverflow");
            }
            int charEnd = charIndex + charCount;

            while (charIndex < charEnd) {
                char ch = chars[charIndex++];
                if (ch >= 0x0080) ch = '?';
                bytes[byteIndex++] = (byte)ch;
            }
            return charCount;
        }

        //| <include path='docs/doc[@for="ASCIIEncoding.GetCharCount"]/*' />
        public override int GetCharCount(byte[] bytes, int index, int count) {
            if (bytes == null) {
                throw new ArgumentNullException("bytes",
                    "ArgumentNull_Array");
            }
            if (index < 0 || count < 0) {
                throw new ArgumentOutOfRangeException((index<0 ? "index" : "count"),
                    "ArgumentOutOfRange_NeedNonNegNum");
            }
            if (bytes.Length - index < count) {
                throw new ArgumentOutOfRangeException("bytes",
                    "ArgumentOutOfRange_IndexCountBuffer");
            }
            return (count);

        }

        //| <include path='docs/doc[@for="ASCIIEncoding.GetChars"]/*' />
        public override int GetChars(byte[] bytes, int byteIndex, int byteCount,
            char[] chars, int charIndex) {
            if (bytes == null || chars == null) {
                throw new ArgumentNullException((bytes == null ? "bytes" : "chars"),
                    "ArgumentNull_Array");
            }
            if (byteIndex < 0 || byteCount < 0) {
                throw new ArgumentOutOfRangeException((byteIndex<0 ? "byteIndex" : "byteCount"),
                    "ArgumentOutOfRange_NeedNonNegNum");
            }
            if (bytes.Length - byteIndex < byteCount) {
                throw new ArgumentOutOfRangeException("bytes",
                    "ArgumentOutOfRange_IndexCountBuffer");
            }
            if (charIndex < 0 || charIndex > chars.Length) {
                throw new ArgumentOutOfRangeException("charIndex",
                    "ArgumentOutOfRange_Index");
            }
            if (chars.Length - charIndex < byteCount) {
                throw new ArgumentException("Argument_ConversionOverflow");
            }
            int byteEnd = byteIndex + byteCount;
            while (byteIndex < byteEnd) {
                byte b = bytes[byteIndex++];
                if (b > 0x7f) {
                    // This is an invalid byte in the ASCII encoding.
                    chars[charIndex++] = '?';
                }
                else {
                    chars[charIndex++] = (char)b;
                }
            }
            return (byteCount);

        }

        //| <include path='docs/doc[@for="ASCIIEncoding.GetString"]/*' />
        public override String GetString(byte[] bytes)
        {
            if (bytes == null)
                throw new ArgumentNullException("bytes", "ArgumentNull_Array");
            return String.CreateStringFromASCII(bytes, 0, bytes.Length);
        }

        //| <include path='docs/doc[@for="ASCIIEncoding.GetString1"]/*' />
        public override String GetString(byte[] bytes, int byteIndex, int byteCount)
        {
            if (bytes == null)
                throw new ArgumentNullException("bytes", "ArgumentNull_Array");
            if (byteIndex < 0 || byteCount < 0) {
                throw new ArgumentOutOfRangeException((byteIndex<0 ? "byteIndex" : "byteCount"),
                    "ArgumentOutOfRange_NeedNonNegNum");
            }
            if (bytes.Length - byteIndex < byteCount) {
                throw new ArgumentOutOfRangeException("bytes",
                    "ArgumentOutOfRange_IndexCountBuffer");
            }
            return String.CreateStringFromASCII(bytes, byteIndex, byteCount);
        }

        //| <include path='docs/doc[@for="ASCIIEncoding.GetMaxByteCount"]/*' />
        public override int GetMaxByteCount(int charCount) {
            if (charCount < 0) {
               throw new ArgumentOutOfRangeException("charCount",
                    "ArgumentOutOfRange_NeedNonNegNum");
            }

            return (charCount);
        }

        //| <include path='docs/doc[@for="ASCIIEncoding.GetMaxCharCount"]/*' />
        public override int GetMaxCharCount(int byteCount) {
            if (byteCount < 0) {
               throw new ArgumentOutOfRangeException("byteCount",
                    "ArgumentOutOfRange_NeedNonNegNum");
            }
            return byteCount;
        }
    }
}
