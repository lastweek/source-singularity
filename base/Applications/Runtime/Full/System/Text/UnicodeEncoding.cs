// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Text
{
    using System;
    //| <include path='docs/doc[@for="UnicodeEncoding"]/*' />
    public class UnicodeEncoding : Encoding
    {
        internal bool bigEndian;
        internal bool byteOrderMark;

        // Unicode version 2.0 character size in bytes
        //| <include path='docs/doc[@for="UnicodeEncoding.CharSize"]/*' />
        public const int CharSize = 2;


        //| <include path='docs/doc[@for="UnicodeEncoding.UnicodeEncoding"]/*' />
        public UnicodeEncoding()
            : this(false, true) {
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.UnicodeEncoding1"]/*' />
        public UnicodeEncoding(bool bigEndian, bool byteOrderMark)
            : base(bigEndian? 1201 : 1200) { //Set the data item.
            this.bigEndian = bigEndian;
            this.byteOrderMark = byteOrderMark;
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetByteCount"]/*' />
        public override int GetByteCount(char[] chars, int index, int count) {
            if (chars == null) {
                throw new ArgumentNullException("chars",
                    "ArgumentNull_Array");
            }
            if (index < 0 || count < 0) {
                throw new ArgumentOutOfRangeException((index<0 ? "index" : "count"),
                    "ArgumentOutOfRange_NeedNonNegNum");
            }
            if (chars.Length - index < count) {
                throw new ArgumentOutOfRangeException("chars",
                      "ArgumentOutOfRange_IndexCountBuffer");
            }

            int byteCount = count * CharSize;
            // check for overflow
            if (byteCount < 0)
                throw new ArgumentOutOfRangeException("count", "ArgumentOutOfRange_GetByteCountOverflow");
            return byteCount;
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetByteCount1"]/*' />
        public override int GetByteCount(String s)
        {
            if (s == null)
                throw new ArgumentNullException("s");

            int byteCount = s.Length * CharSize;
            // check for overflow
            if (byteCount < 0)
                throw new ArgumentOutOfRangeException("s", "ArgumentOutOfRange_GetByteCountOverflow");

            return byteCount;
        }


        //| <include path='docs/doc[@for="UnicodeEncoding.GetBytes"]/*' />
        public override int GetBytes(char[] chars, int charIndex, int charCount,
            byte[] bytes, int byteIndex) {
            int byteCount = charCount * CharSize;
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
            if (bytes.Length - byteIndex < byteCount) {
                throw new ArgumentException("Argument_ConversionOverflow");
            }
            if (bigEndian) {
                int charEnd = charIndex + charCount;
                while (charIndex < charEnd) {
                    char ch = chars[charIndex++];
                    bytes[byteIndex++] = (byte)(ch >> 8);
                    bytes[byteIndex++] = (byte)ch;
                }
            }
            else {
                Buffer.InternalBlockCopy(chars, charIndex * CharSize, bytes, byteIndex, byteCount);
            }
            return byteCount;
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetBytes2"]/*' />
        public override byte[] GetBytes(String s) {
            if (s == null) {
                throw new ArgumentNullException("s",
                    "ArgumentNull_String");
            }
            int byteLen = GetByteCount(s);
            byte[] bytes = new byte[byteLen];
            GetBytes(s, 0, s.Length, bytes, 0);
            return bytes;
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetBytes1"]/*' />
        public override int GetBytes(String s, int charIndex, int charCount,
            byte[] bytes, int byteIndex) {
            int byteCount = charCount * CharSize;
            if (s == null || bytes == null) {
                throw new ArgumentNullException((s == null ? "s" : "bytes"),
                      "ArgumentNull_Array");
            }
            if (charIndex < 0 || charCount < 0) {
                throw new ArgumentOutOfRangeException((charIndex<0 ? "charIndex" : "charCount"),
                      "ArgumentOutOfRange_NeedNonNegNum");
            }
            if (s.Length - charIndex < charCount) {
                throw new ArgumentOutOfRangeException("s",
                      "ArgumentOutOfRange_IndexCount");
            }
            if (byteIndex < 0 || byteIndex > bytes.Length) {
                throw new ArgumentOutOfRangeException("byteIndex",
                    "ArgumentOutOfRange_Index");
            }
            if (bytes.Length - byteIndex < byteCount) {
                throw new ArgumentException("Argument_ConversionOverflow");
            }
            if (bigEndian) {
                int charEnd = charIndex + charCount;
                while (charIndex < charEnd) {
                    char ch = s[charIndex++];
                    bytes[byteIndex++] = (byte)(ch >> 8);
                    bytes[byteIndex++] = (byte)ch;
                }
            }
            else {
                // @TODO: Consider pinning the String here and then using a managed
                // memcpy implementation (see VTable).  This would
                // require a C# compiler that can get an interior pointer to a
                // String, probably via the fixed statement.
                s.CopyToByteArray(charIndex, bytes, byteIndex, charCount);
            }
            return byteCount;
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetCharCount"]/*' />
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
            return (count / CharSize);
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetChars"]/*' />
        public override int GetChars(byte[] bytes, int byteIndex, int byteCount,
            char[] chars, int charIndex) {
            int charCount = byteCount / CharSize;
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
            if (chars.Length - charIndex < charCount) {
                throw new ArgumentException("Argument_ConversionOverflow");
            }

            byteCount = charCount * CharSize;
            if (bigEndian) {
                int byteEnd = byteIndex + byteCount;
                while (byteIndex < byteEnd) {
                    int hi = bytes[byteIndex++];
                    int lo = bytes[byteIndex++];
                    chars[charIndex++] = (char)(hi << 8 | lo);
                }
            }
            else {
                Buffer.InternalBlockCopy(bytes, byteIndex, chars, charIndex * CharSize, byteCount);
            }
            return charCount;
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetDecoder"]/*' />
        public override System.Text.Decoder GetDecoder() {
            return new Decoder(this);
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetPreamble"]/*' />
        public override byte[] GetPreamble()
        {
            if (byteOrderMark) {
                // Note - we must allocate new byte[]'s here to prevent someone
                // from modifying a cached byte[].
                if (bigEndian)
                    return new byte[2] { 0xfe, 0xff };
                else
                    return new byte[2] { 0xff, 0xfe };
            }
            return emptyByteArray;
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetMaxByteCount"]/*' />
        public override int GetMaxByteCount(int charCount) {
            if (charCount < 0) {
               throw new ArgumentOutOfRangeException("charCount",
                    "ArgumentOutOfRange_NeedNonNegNum");
            }
            long byteCount = (long)charCount * CharSize;
            if (byteCount > 0x7fffffff)
                throw new ArgumentOutOfRangeException("charCount", "ArgumentOutOfRange_GetByteCountOverflow");
            return (int)byteCount;
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetMaxCharCount"]/*' />
        public override int GetMaxCharCount(int byteCount) {
            if (byteCount < 0) {
               throw new ArgumentOutOfRangeException("byteCount",
                    "ArgumentOutOfRange_NeedNonNegNum");
            }
            long result = ((long)byteCount + 1) / CharSize;
            if (result > 0x7fffffff) {
                throw new ArgumentOutOfRangeException("byteCount", "ArgumentOutOfRange_GetCharCountOverflow");
            }
            return (int)result;
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.Equals"]/*' />
        public override bool Equals(Object value) {
            UnicodeEncoding uenc = value as UnicodeEncoding;
            if (uenc != null) {
                //
                // Big Endian Unicode has different code page (1201) than small Endian one (1200),
                // so we still have to check m_codePage here.
                //
                return (m_codePage == uenc.m_codePage &&
                        byteOrderMark == uenc.byteOrderMark);
            }
            return (false);
        }

        //| <include path='docs/doc[@for="UnicodeEncoding.GetHashCode"]/*' />
        public override int GetHashCode()
        {
            return m_codePage;
        }

        private class Decoder : System.Text.Decoder
        {
            private bool bigEndian;
            private int lastByte;

            public Decoder(UnicodeEncoding encoding) {
                bigEndian = encoding.bigEndian;
                lastByte = -1;
            }

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
                if (lastByte >= 0) count++;
                return count / CharSize;
            }

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
                int charCount = GetCharCount(bytes, byteIndex, byteCount);
                if (chars.Length - charIndex < charCount) {
                    throw new ArgumentException("Argument_ConversionOverflow");
                }

                if (lastByte >= 0) {
                    if (byteCount == 0) return charCount;
                    int nextByte = bytes[byteIndex++];
                    byteCount--;
                    if (bigEndian) {
                        chars[charIndex++] = (char)(lastByte << 8 | nextByte);
                    }
                    else {
                        chars[charIndex++] = (char)(nextByte << 8 | lastByte);
                    }
                    lastByte = -1;
                }
                if ((byteCount & 1) != 0) {
                    lastByte = bytes[byteIndex + --byteCount];
                }
                if (bigEndian) {
                    int byteEnd = byteIndex + byteCount;
                    while (byteIndex < byteEnd) {
                        ushort hi = bytes[byteIndex++];
                        byte lo = bytes[byteIndex++];
                        chars[charIndex++] = (char)(hi << 8 | lo);
                    }
                }
                else {
                    Buffer.InternalBlockCopy(bytes, byteIndex, chars, charIndex * CharSize, byteCount);
                }
                return charCount;
            }
        }
    }
}
