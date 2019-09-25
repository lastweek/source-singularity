//
//
//This file contains an implementation of the MD4 hash algorithm.
//The implementation was derived from the example source code that
//is provided in RFC 1320 - "The MD4 Message-Digest Algorithm".
//
//The code has been ported from C to C#.
//The original copyright is preserved here.
//
//
// Copyright (C) 1991-2, RSA Data Security, Inc. Created 1991. All
// rights reserved.
//
// License to copy and use this software is granted provided that it
// is identified as the "RSA Data Security, Inc. MD4 Message-Digest
// Algorithm" in all material mentioning or referencing this software
// or this function.
//
// License is also granted to make and use derivative works provided
// that such works are identified as "derived from the RSA Data
// Security, Inc. MD4 Message-Digest Algorithm" in all material
// mentioning or referencing the derived work.
//
// RSA Data Security, Inc. makes no representations concerning either
// the merchantability of this software or the suitability of this
// software for any particular purpose. It is provided "as is"
// without express or implied warranty of any kind.
//
// These notices must be retained in any copies of any part of this
// documentation and/or software.
//
//

using System;
using System.Diagnostics;
using System.Text;

namespace System.Security.Cryptography
{

    /// <summary>
    /// This class implements the MD4 message digest algorithm.
    /// The implementation is a C# port of the original RSA C implementation that is
    /// provided in RFC 1320.
    /// </summary>
    public class MD4Context
    {
        public MD4Context()
        {
            Reset();
        }

        public const int DigestLength = 16;

        /// <summary>
        /// This field is "true" if GetDigest has been called.
        /// It cannot be called again, unless Reset is called.
        /// </summary>
        bool _done;

        public void Clear()
        {
            _state0 = 0;
            _state1 = 0;
            _state2 = 0;
            _state3 = 0;
            _count = 0;
            for (int i = 0; i < 64; i++)
                _buffer[i] = 0;
        }

        /// <summary>
        /// This method can be used to reset the state of the MD4 context.  After returning, the
        /// state of the MD4Context is equivalent to its state immediately after the constructor
        /// finished.
        /// </summary>
        public void Reset()
        {
            // Load magic initialization constants.
            _count = 0;
            _state0 = 0x67452301;
            _state1 = 0xefcdab89;
            _state2 = 0x98badcfe;
            _state3 = 0x10325476;
            _done = false;
        }

        //
        //MD4 basic transformation. Transforms state based on block.
        // 
        void Transform(byte[]/*!*/ block, int offset)
        {
            if (offset < 0)
                throw new ArgumentException("offset cannot be negative.");

            Decode(_block, 0, block, offset, 64);
            Transform(_block);

            // Zeroize sensitive information.
            // MD4_memset ((POINTER)x, 0, sizeof (x));
        }

        #region Constants for MD4Transform routine.
        const int S11 = 3;
        const int S12 = 7;
        const int S13 = 11;
        const int S14 = 19;
        const int S21 = 3;
        const int S22 = 5;
        const int S23 = 9;
        const int S24 = 13;
        const int S31 = 3;
        const int S32 = 9;
        const int S33 = 11;
        const int S34 = 15;
        #endregion

        /// <summary>
        /// This routine transforms the current MD4 context, using a block of input.
        /// The input is 16 words, where each word is 32 unsigned bits.  This method
        /// is the core of the MD4 algorithm.
        /// </summary>
        /// <param name="x">The message data to use to transform the context.</param>
        void Transform(uint[] x)
        {
            uint a = _state0;
            uint b = _state1;
            uint c = _state2;
            uint d = _state3;

            // Round 1   
            a = FF(a, b, c, d, x[00], S11); // 1   
            d = FF(d, a, b, c, x[01], S12); // 2   
            c = FF(c, d, a, b, x[02], S13); // 3   
            b = FF(b, c, d, a, x[03], S14); // 4   
            a = FF(a, b, c, d, x[04], S11); // 5   
            d = FF(d, a, b, c, x[05], S12); // 6   
            c = FF(c, d, a, b, x[06], S13); // 7   
            b = FF(b, c, d, a, x[07], S14); // 8   
            a = FF(a, b, c, d, x[08], S11); // 9   
            d = FF(d, a, b, c, x[09], S12); // 10   
            c = FF(c, d, a, b, x[10], S13); // 11   
            b = FF(b, c, d, a, x[11], S14); // 12   
            a = FF(a, b, c, d, x[12], S11); // 13   
            d = FF(d, a, b, c, x[13], S12); // 14   
            c = FF(c, d, a, b, x[14], S13); // 15   
            b = FF(b, c, d, a, x[15], S14); // 16   

            // Round 2   
            a = GG(a, b, c, d, x[00], S21); // 17   
            d = GG(d, a, b, c, x[04], S22); // 18   
            c = GG(c, d, a, b, x[08], S23); // 19   
            b = GG(b, c, d, a, x[12], S24); // 20   
            a = GG(a, b, c, d, x[01], S21); // 21   
            d = GG(d, a, b, c, x[05], S22); // 22   
            c = GG(c, d, a, b, x[09], S23); // 23   
            b = GG(b, c, d, a, x[13], S24); // 24   
            a = GG(a, b, c, d, x[02], S21); // 25   
            d = GG(d, a, b, c, x[06], S22); // 26   
            c = GG(c, d, a, b, x[10], S23); // 27   
            b = GG(b, c, d, a, x[14], S24); // 28   
            a = GG(a, b, c, d, x[03], S21); // 29   
            d = GG(d, a, b, c, x[07], S22); // 30   
            c = GG(c, d, a, b, x[11], S23); // 31   
            b = GG(b, c, d, a, x[15], S24); // 32   

            // Round 3   
            a = HH(a, b, c, d, x[00], S31); // 33   
            d = HH(d, a, b, c, x[08], S32); // 34   
            c = HH(c, d, a, b, x[04], S33); // 35   
            b = HH(b, c, d, a, x[12], S34); // 36   
            a = HH(a, b, c, d, x[02], S31); // 37   
            d = HH(d, a, b, c, x[10], S32); // 38   
            c = HH(c, d, a, b, x[06], S33); // 39   
            b = HH(b, c, d, a, x[14], S34); // 40   
            a = HH(a, b, c, d, x[01], S31); // 41   
            d = HH(d, a, b, c, x[09], S32); // 42   
            c = HH(c, d, a, b, x[05], S33); // 43   
            b = HH(b, c, d, a, x[13], S34); // 44   
            a = HH(a, b, c, d, x[03], S31); // 45   
            d = HH(d, a, b, c, x[11], S32); // 46   
            c = HH(c, d, a, b, x[07], S33); // 47   
            b = HH(b, c, d, a, x[15], S34); // 48   

            _state0 = unchecked(_state0 + a);
            _state1 = unchecked(_state1 + b);
            _state2 = unchecked(_state2 + c);
            _state3 = unchecked(_state3 + d);
        }

        public const int BytesPerTransform = 64;
        public const int WordsPerTransform = 16;

        uint _state0;             // state A
        uint _state1;             // state B
        uint _state2;             // state C
        uint _state3;             // state D
        Int64 _count;              // number of bits, modulo 2^64

        /// <summary>
        /// This buffer holds data that was submitted using the Update method, but which
        /// was too short to complete a full transform block (64 bytes).
        /// </summary>
        readonly byte[]/*!*/ _buffer = new byte[BytesPerTransform];

        /// <summary>
        /// This buffer contains the current block (of message data) that is being transformed.
        /// </summary>
        readonly uint[]/*!*/ _block = new uint[WordsPerTransform];

        static MD4Context()
        {
            PADDING = new byte[BytesPerTransform];
            Array.Clear(PADDING, 0, 64);
            PADDING[0] = 0x80;
        }

        static readonly byte[]/*!*/ PADDING;
        //
        //{
        //  0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        //      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        //      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
        //};
        //

        // F, G and H are basic MD4 functions.
        //
        static uint F(uint x, uint y, uint z) { return (x & y) | ((~x) & z); }
        static uint G(uint x, uint y, uint z) { return (x & y) | (x & z) | (y & z); }
        static uint H(uint x, uint y, uint z) { return x ^ y ^ z; }

        // ROTATE_LEFT rotates x left n bits.
        //
        static uint RotateLeft(uint x, int n)
        {
            return (x << n) | (x >> (32 - n));
        }

        // FF, GG and HH are transformations for rounds 1, 2 and 3   
        // Rotation is separate from addition to prevent recomputation   
        // (Or at least it used to be, when these were C macros.   

        static uint FF(uint a, uint b, uint c, uint d, uint x, int s)
        {
            a = unchecked(a + F(b, c, d) + x);
            return RotateLeft(a, s);
        }

        static uint GG(uint a, uint b, uint c, uint d, uint x, int s)
        {
            a = unchecked(a + G(b, c, d) + x + (uint)0x5a827999);
            return RotateLeft(a, s);
        }

        static uint HH(uint a, uint b, uint c, uint d, uint x, int s)
        {
            a = unchecked(a + H(b, c, d) + x + (uint)0x6ed9eba1);
            return RotateLeft(a, s);
        }


        // Decodes input (unsigned char) into output (uint). Assumes len is
        //   a multiple of 4.
//
        // 

        /// <summary>
        /// 
        /// </summary>
        /// <param name="output"></param>
        /// <param name="outputoffset"></param>
        /// <param name="input"></param>
        /// <param name="inputoffset"></param>
        /// <param name="length">number of BYTES to transfer</param>
        static void Decode(uint[]/*!*/ output, int outputoffset, byte[]/*!*/ input, int inputoffset, int length)
        {
            Debug.Assert(length % 4 == 0);

            int outpos = outputoffset;

            for (int j = 0; j < length; j += 4) {
                uint value = ((uint)input[inputoffset + j])
                    | (((uint)input[inputoffset + j + 1]) << 8)
                    | (((uint)input[inputoffset + j + 2]) << 16)
                    | (((uint)input[inputoffset + j + 3]) << 24);
                output[outpos] = value;

                outpos++;
            }
        }

        static void EncodeLe(uint value, byte[]/*!*/ output, int pos)
        {
            output[pos] = (byte)(value & 0xff);
            output[pos + 1] = (byte)((value >> 8) & 0xff);
            output[pos + 2] = (byte)((value >> 16) & 0xff);
            output[pos + 3] = (byte)((value >> 24) & 0xff);
        }

        /// <summary>
        /// MD4 block update operation. Continues an MD4 message-digest operation,
        /// processing another message block, and updating the context.
        /// </summary>
        /// <param name="input">The buffer containing data to process.</param>
        /// <param name="offset">The offset within the buffer where the data begins.</param>
        /// <param name="length">The length of the data.</param>
        public void Update(byte[]/*!*/ input, int offset, int length)
        {
            if (_done)
                throw new InvalidOperationException("The hash context has been closed (GetDigest has been called).  It cannot be reused until Reset is called.");

            if (length == 0)
                return;

            // Compute number of bytes mod 64   
            int index = (int)((_count >> 3) & 0x3F);
            _count += length << 3;

            int partLen = 64 - index;

            // Transform as many times as possible.
            //
            int i;
            if (length >= partLen) {
                // MD4_memcpy((POINTER)&buffer_pinned[index], (POINTER)&input[offset], partLen);
                Array.Copy(input, offset, _buffer, index, partLen);
                Transform(_buffer, 0);

                for (i = partLen; i + 63 < length; i += 64)
                    Transform(input, offset + i);

                index = 0;
            }
            else
                i = 0;

            // Buffer remaining input   
            // MD4_memcpy((POINTER)&_buffer[index], (POINTER)&input[i], inputLen-i);
            // MD4_memcpy((POINTER)&buffer_pinned[index], (POINTER)&input[offset + i], inputLen-i);
            Array.Copy(input, offset + i, _buffer, index, length - i);
        }


        public static MD4Digest GetDigest(byte[]/*!*/ buffer)
        {
            return GetDigest(buffer, 0, buffer.Length);
        }

        public static MD4Digest GetDigest(byte[]/*!*/ buffer, int offset, int length)
        {
            MD4Context context = new MD4Context();
            context.Update(buffer, offset, length);
            return context.GetDigest();
        }

        // MD4 finalization. Ends an MD4 message-digest operation, writing the
        //   the message digest and zeroizing the context.
        // 
        public MD4Digest GetDigest()
        {
            if (_done)
                throw new InvalidOperationException("GetDigest cannot be called twice for a single hash sequence.  Call Reset() to reset the context.");

            byte[]/*!*/ bits = new byte[8];

            // Save number of bits   
            EncodeLe((uint)(_count & 0xffffffffu), bits, 0);
            EncodeLe((uint)(_count >> 32), bits, 4);

            // Pad out to 56 mod 64.
            int index = (int)((_count >> 3) & 0x3f);
            int padLen = (index < 56) ? (56 - index) : (120 - index);
            Update(PADDING, 0, padLen);

            // Append length (before padding)
            Update(bits, 0, 8);

            // Store state in digest

            MD4Digest digest;
            digest.state0 = _state0;
            digest.state1 = _state1;
            digest.state2 = _state2;
            digest.state3 = _state3;

            Clear();

            _done = true;

            return digest;
        }
    }

    public struct MD4Digest
    {
        public uint state0;
        public uint state1;
        public uint state2;
        public uint state3;

        static void PackLe(byte[]/*!*/ dest, int offset, uint value)
        {
            dest[offset + 0] = (byte)((value) & 0xff);
            dest[offset + 1] = (byte)((value >> 8) & 0xff);
            dest[offset + 2] = (byte)((value >> 16) & 0xff);
            dest[offset + 3] = (byte)((value >> 24) & 0xff);
        }

        public const int DigestLength = 16;

        public byte[]/*!*/ ToArray()
        {
            byte[] result = new byte[DigestLength];
            ToArray(result);
            return result;
        }

        public void ToArray(byte[]/*!*/ result)
        {
            if (result.Length < 0x10)
                throw new ArgumentException("Input array is too short.");

            PackLe(result, 0, state0);
            PackLe(result, 4, state1);
            PackLe(result, 8, state2);
            PackLe(result, 12, state3);
        }

        public static implicit operator byte[]/*!*/(MD4Digest digest)
        {
            return digest.ToArray();
        }

        override public string/*!*/ ToString()
        {
            string hex = "0123456789abcdef";
            byte[] arr = ToArray();
            StringBuilder buffer = new StringBuilder(DigestLength * 2);
            for (int i = 0; i < 0x10; i++) {
                byte b = arr[i];
                buffer.Append(hex[b >> 4]);
                buffer.Append(hex[b & 0xf]);
            }
            return buffer.ToString();
        }
    }

}
